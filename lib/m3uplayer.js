/**
 * ============================================================
 * M3U Player — وحدة مستقلة بالكامل
 * ============================================================
 * لا تشارك أي كود أو متغيرات مع أوامر:
 *   .record / .recordiptv / .stoprecord / .stoprecordiptv / .m3u8 / .hls
 *
 * الغرض: تشغيل/تسجيل أي رابط m3u أو m3u8 مباشر يُدخله المستخدم بنفسه
 * (وليس من قوائم UGEEN أو iptv-org)، عبر أمرين مستقلين:
 *   .playm3u [رابط] [المدة بالدقائق] [مدة الجزء - اختياري]
 *   .stopplaym3u
 * ============================================================
 */

const fs = require('fs');
const path = require('path');
const { spawn } = require('child_process');

// ── ثوابت خاصة بهذه الوحدة فقط ──
const M3U_TARGET_MB = 100;
const M3U_DEFAULT_SEGMENT_MIN = 6;
const M3U_SEGMENT_SAFETY_BYTES = 180 * 1024 * 1024;
const M3U_MAX_DURATION_MIN = 360;
const M3U_MAX_RECONNECTS = 15;
const M3U_FAST_FAIL_SEC = 20; // أي تشغيل ينتهي قبل هذه المدة بدون أجزاء يُعدّ فشلاً فورياً
const M3U_USER_AGENT = 'VLC/3.0.20 LibVLC/3.0.20';

// إخفاء بيانات الدخول من أي رابط قبل عرضه في المحادثة أو السجلات
function maskM3UUrl(text) {
    return String(text)
        .replace(/(password|pass|pwd|token)=([^&\s]+)/gi, '$1=***')
        .replace(/(username|user)=([^&\s]+)/gi, '$1=***')
        .replace(/\/(live|movie|series)\/[^/\s]+\/[^/\s]+\//gi, '/$1/***/***/');
}

// آخر سطر خطأ مفيد من مخرجات ffmpeg
function lastFfmpegError(stderr) {
    const lines = String(stderr).split(/[\r\n]+/).map(l => l.trim())
        .filter(l => l && !/^(size|frame)=|time=\d|speed=/.test(l));
    const hit = [...lines].reverse().find(l =>
        /(error|fail|refused|denied|forbidden|unauthorized|not found|invalid|timed out|max|limit|403|401|404|406|458|509)/i.test(l)
    ) || lines[lines.length - 1] || 'سبب غير معروف';
    return maskM3UUrl(hit).slice(0, 220);
}

// ── تتبع الجلسات النشطة الخاصة بهذه الوحدة فقط ──
const activeM3UPlayers = new Map(); // chatId -> { proc, cancelled }

function isValidM3UUrl(url) {
    return typeof url === 'string' && /^https?:\/\//i.test(url.trim());
}

function probeM3UBitrate(streamUrl) {
    return new Promise((resolve) => {
        let settled = false;
        const finish = (val) => { if (!settled) { settled = true; resolve(val); } };
        const args = [
            '-v', 'quiet', '-print_format', 'json', '-show_format',
            '-analyzeduration', '4000000', '-probesize', '4000000',
            streamUrl
        ];
        const proc = spawn('ffprobe', args);
        let out = '';
        proc.stdout.on('data', (d) => { out += d.toString(); });
        proc.on('close', () => {
            try {
                const data = JSON.parse(out);
                const bitrate = parseInt(data?.format?.bit_rate);
                if (bitrate && bitrate > 0) return finish(bitrate);
            } catch (_) {}
            finish(null);
        });
        proc.on('error', () => finish(null));
        setTimeout(() => { try { proc.kill(); } catch (_) {} finish(null); }, 12000);
    });
}

function computeM3USegmentSec(bitrateBps) {
    if (!bitrateBps || bitrateBps <= 0) return M3U_DEFAULT_SEGMENT_MIN * 60;
    const targetBits = M3U_TARGET_MB * 1024 * 1024 * 8;
    const seconds = Math.floor(targetBits / bitrateBps);
    return Math.max(120, Math.min(20 * 60, seconds));
}

// تسجيل/تشغيل متواصل مُجزّأ لرابط m3u المُدخل مباشرة من المستخدم
async function playM3USegmented(streamUrl, segDir, prefix, totalDurationSec, segmentTimeSec, onSegmentReady, control) {
    const pattern = path.join(segDir, `${prefix}_%03d.mp4`);
    const args = [
        '-y',
        '-user_agent', M3U_USER_AGENT,
        '-reconnect', '1',
        '-reconnect_streamed', '1',
        '-reconnect_at_eof', '1',
        '-reconnect_on_network_error', '1',
        '-reconnect_delay_max', '10',
        '-rw_timeout', '20000000',
        '-i', streamUrl,
        '-map', '0:v:0?',
        '-map', '0:a:0?',
        '-sn', '-dn',
        '-t', String(totalDurationSec),
        '-c', 'copy',
        '-f', 'segment',
        '-segment_time', String(segmentTimeSec),
        '-reset_timestamps', '1',
        pattern
    ];

    const proc = spawn('ffmpeg', args);
    control.proc = proc; // كشف مرجع العملية لأمر .stopplaym3u الخارجي
    let stderr = '';
    proc.stderr.on('data', (d) => { stderr += d.toString(); });

    let finished = false;
    let abortedBySize = false;
    proc.on('close', () => { finished = true; });
    proc.on('error', () => { finished = true; });

    const getSegFiles = () => {
        try {
            return fs.readdirSync(segDir)
                .filter(f => f.startsWith(prefix + '_') && f.endsWith('.mp4'))
                .map(f => ({ file: f, idx: parseInt(f.match(/_(\d+)\.mp4$/)?.[1] || '-1') }))
                .filter(x => x.idx >= 0)
                .sort((a, b) => a.idx - b.idx);
        } catch (_) { return []; }
    };

    let lastSentIndex = -1;

    while (!finished) {
        if (control.cancelled) {
            proc.kill('SIGINT');
            break;
        }

        const files = getSegFiles();

        for (let i = 0; i < files.length - 1; i++) {
            if (files[i].idx > lastSentIndex && !control.cancelled) {
                lastSentIndex = files[i].idx;
                await onSegmentReady(path.join(segDir, files[i].file));
            }
        }

        if (!abortedBySize && files.length > 0) {
            const activeFile = files[files.length - 1];
            try {
                const activeSize = fs.statSync(path.join(segDir, activeFile.file)).size;
                if (activeSize >= M3U_SEGMENT_SAFETY_BYTES) {
                    abortedBySize = true;
                    proc.kill('SIGINT');
                }
            } catch (_) {}
        }

        await new Promise(r => setTimeout(r, 3000));
    }

    if (!finished) {
        await new Promise((resolve) => {
            if (proc.exitCode !== null || proc.killed) return resolve();
            proc.once('close', resolve);
            proc.once('error', resolve);
        });
    }

    const finalFiles = getSegFiles();
    for (const item of finalFiles) {
        if (item.idx > lastSentIndex) {
            lastSentIndex = item.idx;
            if (!control.cancelled || item.idx === finalFiles[finalFiles.length - 1].idx) {
                await onSegmentReady(path.join(segDir, item.file));
            }
        }
    }

    return { stderr, segmentCount: lastSentIndex + 1, abortedBySize, cancelled: control.cancelled };
}

// ============================================================
// الدالة الرئيسية التي يستدعيها index.js لأمر .playm3u
// ============================================================
async function startM3UPlayer({ sock, chatId, mek, streamUrl, durationMin, manualSegmentMin, tmpRootDir }) {
    if (activeM3UPlayers.has(chatId)) {
        await sock.sendMessage(chatId, {
            text: `⚠️ يوجد تشغيل m3u نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stopplaym3u\` قبل بدء تشغيل جديد.`
        }, { quoted: mek });
        return;
    }

    const totalDurationSec = durationMin * 60;
    const segDir = path.join(tmpRootDir, `m3uplay_${Date.now()}`);
    fs.mkdirSync(segDir, { recursive: true });

    let segmentTimeSec;
    let segmentMinutes;
    let bitrateNote = '';

    if (manualSegmentMin !== null) {
        segmentMinutes = manualSegmentMin;
        segmentTimeSec = manualSegmentMin * 60;
    } else {
        await sock.sendMessage(chatId, {
            text: `🔍 جاري فحص معدل بت الرابط لتقدير حجم الجزء بدقة (~${M3U_TARGET_MB} MB)...`
        }, { quoted: mek });

        const bitrate = await probeM3UBitrate(streamUrl);
        segmentTimeSec = computeM3USegmentSec(bitrate);
        segmentMinutes = Math.round(segmentTimeSec / 60);

        bitrateNote = bitrate
            ? `\n📊 معدل البت المُقاس: ~${(bitrate / 1000000).toFixed(2)} Mbps`
            : `\n⚠️ تعذر قياس معدل البت، تم استخدام تقدير احتياطي (${M3U_DEFAULT_SEGMENT_MIN} دقائق)`;
    }

    await sock.sendMessage(chatId, {
        text: `▶️ *بدأ تشغيل رابط m3u!*\n🔗 الرابط: ${maskM3UUrl(streamUrl)}\n⏱️ المدة الكلية: *${durationMin} دقيقة*\n📦 كل جزء: *~${segmentMinutes} دقيقة* (تقدير لـ ~${M3U_TARGET_MB} MB)${bitrateNote}\n\n🛑 لإلغاء التشغيل في أي وقت: \`.stopplaym3u\``
    }, { quoted: mek });

    const control = { proc: null, cancelled: false };
    activeM3UPlayers.set(chatId, control);

    let segmentIndex = 0;
    let abortedBySize = false;
    let wasCancelled = false;
    let remainingSec = totalDurationSec;
    let attempt = 0;
    let reconnectedCount = 0;
    let consecutiveFails = 0; // فشل متتالٍ بدون تقدم فعلي
    let lastReason = '';

    const onSegmentReady = async (filePath) => {
        try {
            if (fs.statSync(filePath).size < 10 * 1024) { // ملف فارغ/تالف من محاولة فاشلة
                try { fs.unlinkSync(filePath); } catch (_) {}
                return;
            }
        } catch (_) { return; }
        segmentIndex++;
        try {
            const sizeMB = (fs.statSync(filePath).size / 1024 / 1024).toFixed(2);
            await sock.sendMessage(chatId, {
                document: { url: filePath },
                mimetype: 'video/mp4',
                fileName: `PlayM3U_part${segmentIndex}.mp4`,
                caption: `📦 *الجزء ${segmentIndex}*\n⚖️ ${sizeMB} MB`
            }, { quoted: mek });
        } catch (e) {
            await sock.sendMessage(chatId, {
                text: `⚠️ فشل إرسال الجزء ${segmentIndex}: ${e.message}`
            }, { quoted: mek });
        } finally {
            try { fs.unlinkSync(filePath); } catch (_) {}
        }
    };

    try {
        while (remainingSec > 10 && consecutiveFails < M3U_MAX_RECONNECTS && !control.cancelled) {
            attempt++;
            const startTs = Date.now();

            const result = await playM3USegmented(
                streamUrl, segDir, `pm3u_a${attempt}`, remainingSec, segmentTimeSec,
                onSegmentReady, control
            );

            const elapsedSec = Math.floor((Date.now() - startTs) / 1000);
            remainingSec -= elapsedSec;

            abortedBySize = result.abortedBySize;
            wasCancelled = result.cancelled;

            if (wasCancelled || abortedBySize) break;
            if (remainingSec <= 10) break;

            // فشل فوري = انتهى بسرعة بدون أي جزء → السبب غالباً في الرابط/السيرفر وليس انقطاعاً عابراً
            const madeProgress = result.segmentCount > 0 || elapsedSec >= 60;
            consecutiveFails = madeProgress ? 0 : consecutiveFails + 1;
            lastReason = lastFfmpegError(result.stderr);

            reconnectedCount++;
            const backoffMs = Math.min(3000 * Math.pow(2, Math.min(consecutiveFails, 5)), 60000);
            await sock.sendMessage(chatId, {
                text: `⚠️ *انقطع الاتصال بالرابط بشكل غير متوقع.*\n⏱️ الوقت المتبقي: ~${Math.ceil(remainingSec / 60)} دقيقة\n🧾 السبب: \`${lastReason}\`\n🔄 جاري إعادة الاتصال بعد ${Math.round(backoffMs / 1000)} ثانية... (فشل متتالٍ ${consecutiveFails}/${M3U_MAX_RECONNECTS})`
            }, { quoted: mek });
            await new Promise(r => setTimeout(r, backoffMs));
        }

        if (!wasCancelled && !abortedBySize && consecutiveFails >= M3U_MAX_RECONNECTS && remainingSec > 10) {
            await sock.sendMessage(chatId, {
                text: `❌ تعذر إكمال التشغيل بعد ${M3U_MAX_RECONNECTS} محاولات فاشلة متتالية.\n🧾 آخر سبب: \`${lastReason}\``
            }, { quoted: mek });
        }
    } catch (err) {
        await sock.sendMessage(chatId, {
            text: `❌ خطأ في تشغيل الرابط: ${err.message}`
        }, { quoted: mek });
    } finally {
        activeM3UPlayers.delete(chatId);
        try { fs.rmSync(segDir, { recursive: true, force: true }); } catch (_) {}
    }

    if (wasCancelled) {
        await sock.sendMessage(chatId, {
            text: `🛑 *تم إلغاء التشغيل بطلبك.*\n📦 عدد الأجزاء المُرسلة قبل الإلغاء: ${segmentIndex}`
        }, { quoted: mek });
    } else if (abortedBySize) {
        await sock.sendMessage(chatId, {
            text: `🛑 *تم إيقاف التشغيل مبكراً!*\nجودة البث كانت أعلى من المتوقع وتجاوز حجم أحد الأجزاء الحد الآمن للتخزين المتاح.\n📦 عدد الأجزاء المُرسلة قبل التوقف: ${segmentIndex}\n\n💡 جرّب تقليل مدة الجزء (مثال: \`.playm3u ${streamUrl} ${durationMin} 3\`).`
        }, { quoted: mek });
    } else {
        const reconnectNote = reconnectedCount > 0 ? `\n🔄 حدثت ${reconnectedCount} إعادة اتصال بسبب انقطاعات مؤقتة.` : '';
        await sock.sendMessage(chatId, {
            text: `✅ *اكتمل التشغيل الكامل!*\n📦 عدد الأجزاء المُرسلة: ${segmentIndex}${reconnectNote}`
        }, { quoted: mek });
    }
}

// أمر .stopplaym3u
function stopM3UPlayer(chatId) {
    const control = activeM3UPlayers.get(chatId);
    if (!control) return false;
    control.cancelled = true;
    return true;
}

function hasActiveM3UPlayer(chatId) {
    return activeM3UPlayers.has(chatId);
}

module.exports = {
    isValidM3UUrl,
    startM3UPlayer,
    stopM3UPlayer,
    hasActiveM3UPlayer,
    M3U_MAX_DURATION_MIN,
    M3U_TARGET_MB,
    maskM3UUrl
};

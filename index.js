/**
 * Knight Bot - A WhatsApp Bot
 * Copyright (c) 2026 Professor
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the MIT License.
 */
require('./settings')
const { Boom } = require('@hapi/boom')
const fs = require('fs')
const chalk = require('chalk')
const FileType = require('file-type')
const path = require('path')
const axios = require('axios')
const { exec, spawn } = require('child_process')
const { handleMessages, handleGroupParticipantUpdate, handleStatus } = require('./main');
const PhoneNumber = require('awesome-phonenumber')
const { imageToWebp, videoToWebp, writeExifImg, writeExifVid } = require('./lib/exif')
const { smsg, isUrl, generateMessageTag, getBuffer, getSizeMedia, fetch, await, sleep, reSize } = require('./lib/myfunc')
const {
    default: makeWASocket,
    useMultiFileAuthState,
    DisconnectReason,
    fetchLatestBaileysVersion,
    generateForwardMessageContent,
    prepareWAMessageMedia,
    generateWAMessageFromContent,
    generateMessageID,
    downloadContentFromMessage,
    jidDecode,
    proto,
    jidNormalizedUser,
    makeCacheableSignalKeyStore,
    delay
} = require("@whiskeysockets/baileys")
const NodeCache = require("node-cache")
const pino = require("pino")
const readline = require("readline")
const { parsePhoneNumber } = require("libphonenumber-js")
const { PHONENUMBER_MCC } = require('@whiskeysockets/baileys/lib/Utils/generics')
const { rmSync, existsSync } = require('fs')
const { join } = require('path')
const { randomBytes } = require('crypto')

// ── وحدة مشغّل m3u المستقلة (أوامر .playm3u / .stopplaym3u فقط) ──
const m3uPlayer = require('./lib/m3uplayer')

// ============================================================
// إعدادات Xtream Codes IPTV
// ============================================================
// ── الحد الأقصى المسموح به لحجم أي ملف يتم تحميله أو تسجيله (لتفادي مشاكل الذاكرة/القرص) ──
const MAX_DOWNLOAD_MB = 200;
const MAX_DOWNLOAD_BYTES = MAX_DOWNLOAD_MB * 1024 * 1024;

// ── إعدادات التسجيل المُجزّأ المتواصل (اتصال واحد بالبث، بدون أي انقطاع بين الأجزاء) ──
const RECORD_TARGET_MB = 100; // الحجم المستهدف لكل جزء
const RECORD_DEFAULT_SEGMENT_MIN = 6; // احتياطي إذا فشل فحص معدل البت
const RECORD_SEGMENT_SAFETY_BYTES = 180 * 1024 * 1024; // حد أمان 180 ميجا للجزء الواحد (أقل من مساحة القرص المتاحة)

// فحص معدل بت البث الفعلي عبر ffprobe لحساب مدة جزء تعطي ~100 ميجا بدقة أعلى
function probeStreamBitrate(streamUrl) {
    return new Promise((resolve) => {
        let settled = false;
        const finish = (val) => { if (!settled) { settled = true; resolve(val); } };

        const args = [
            '-v', 'quiet',
            '-print_format', 'json',
            '-show_format',
            '-analyzeduration', '4000000',
            '-probesize', '4000000',
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

        // مهلة أمان: لا تنتظر الفحص أكثر من 12 ثانية
        setTimeout(() => {
            try { proc.kill(); } catch (_) {}
            finish(null);
        }, 12000);
    });
}

// حساب مدة الجزء بالثواني بناءً على معدل البت المُقاس، بحد أدنى دقيقتين وحد أقصى 20 دقيقة
function computeSegmentTimeSec(bitrateBps) {
    if (!bitrateBps || bitrateBps <= 0) return RECORD_DEFAULT_SEGMENT_MIN * 60;
    const targetBits = RECORD_TARGET_MB * 1024 * 1024 * 8;
    const seconds = Math.floor(targetBits / bitrateBps);
    return Math.max(120, Math.min(20 * 60, seconds));
}

// تسجيل متواصل: عملية ffmpeg واحدة فقط تقرأ البث بلا انقطاع، وتُقسّم المخرجات
// داخلياً إلى ملفات متتالية عبر segment muxer. يستدعي onSegmentReady لكل ملف
// فور اكتماله (بينما التسجيل مستمر)، ثم يرسل آخر جزء بعد توقف العملية.
// إذا تجاوز الجزء الحالي (قيد الكتابة) حد الأمان، يتم إيقاف كامل العملية فوراً
// لتفادي امتلاء القرص، ويُعاد abortedBySize=true.
async function recordContinuousSegmented(streamUrl, segDir, prefix, totalDurationSec, segmentTimeSec, onSegmentReady, control) {
    const pattern = path.join(segDir, `${prefix}_%03d.mp4`);
    const args = [
        '-y',
        '-i', streamUrl,
        '-t', String(totalDurationSec),
        '-c', 'copy',
        '-f', 'segment',
        '-segment_time', String(segmentTimeSec),
        '-reset_timestamps', '1',
        pattern
    ];

    const proc = spawn('ffmpeg', args);
    control.proc = proc; // كشف مرجع العملية لأمر .stoprecord الخارجي
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

    // أثناء التسجيل: أي ملف غير الأخير (الحالي قيد الكتابة) يكون قد اكتمل فعلاً
    while (!finished) {
        // إلغاء فوري مطلوب من المستخدم عبر .stoprecord
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

        // فحص أمان: هل تجاوز الجزء الحالي (قيد الكتابة) الحد الآمن؟
        if (!abortedBySize && files.length > 0) {
            const activeFile = files[files.length - 1];
            try {
                const activeSize = fs.statSync(path.join(segDir, activeFile.file)).size;
                if (activeSize >= RECORD_SEGMENT_SAFETY_BYTES) {
                    abortedBySize = true;
                    proc.kill('SIGINT'); // إيقاف آمن يسمح لـ ffmpeg بإغلاق الملف الحالي بشكل صحيح
                }
            } catch (_) {}
        }

        await new Promise(r => setTimeout(r, 3000));
    }

    // انتظار خروج العملية فعلياً إذا تم كسر الحلقة بسبب الإلغاء المباشر قبل أن يضبط finished
    if (!finished) {
        await new Promise((resolve) => {
            if (proc.exitCode !== null || proc.killed) return resolve();
            proc.once('close', resolve);
            proc.once('error', resolve);
        });
    }

    // بعد انتهاء العملية: إرسال أي أجزاء متبقية (بما فيها الجزء الأخير المُنهى الآن)
    // إلا إذا كان الإلغاء بطلب المستخدم — عندها نرسل الجزء الأخير فقط إن كان قد اكتمل فعلياً
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

// ── تتبع التسجيلات النشطة لكل محادثة (لدعم أمر .stoprecord) ──
const activeRecordings = new Map(); // chatId -> { proc, cancelled }

// ── تتبع التسجيلات النشطة الخاصة بقائمة IPTV الثابتة فقط (منفصل عن UGEEN) ──
const activeIptvRecordings = new Map(); // chatId -> { proc, cancelled }

const UGEEN_CONFIG = {
    host: "https://ugeen.live",
    user: "Ugeen_VIPT8j6wm",
    pass: "LCCyLS"
};

// مسار حفظ إعدادات UGEEN بشكل دائم (يبقى فعّالاً حتى بعد إعادة تشغيل البوت)
const UGEEN_CONFIG_PATH = path.join(process.cwd(), 'data', 'ugeen_config.json');

// تحميل إعدادات محفوظة سابقاً (إن وُجدت) لتجاوز القيم الافتراضية أعلاه
try {
    if (fs.existsSync(UGEEN_CONFIG_PATH)) {
        const saved = JSON.parse(fs.readFileSync(UGEEN_CONFIG_PATH, 'utf8'));
        if (saved.host && saved.user && saved.pass) {
            UGEEN_CONFIG.host = saved.host;
            UGEEN_CONFIG.user = saved.user;
            UGEEN_CONFIG.pass = saved.pass;
            console.log('✅ تم تحميل إعدادات UGEEN المحفوظة من', UGEEN_CONFIG_PATH);
        }
    }
} catch (e) {
    console.log('⚠️ فشل تحميل إعدادات UGEEN المحفوظة:', e.message);
}

// ── تخزين مؤقت لقائمة قنوات UGEEN (M3U) لتفادي طلب القائمة الكاملة في كل مرة ──
let ugeenChannelsCache = [];
let ugeenChannelsCacheTime = 0;
const UGEEN_CACHE_TTL = 10 * 60 * 1000; // 10 دقائق

// تحليل نص M3U إلى مصفوفة قنوات {id, name, url}
function parseM3U(m3uText) {
    const channels = [];
    const lines = String(m3uText).split(/\r?\n/);
    let pendingName = null;

    for (const rawLine of lines) {
        const line = rawLine.trim();
        if (!line) continue;

        if (line.startsWith('#EXTINF')) {
            const nameMatch = line.match(/,(.*)$/);
            pendingName = nameMatch ? nameMatch[1].trim() : 'غير معروف';
        } else if (/^https?:\/\//i.test(line) && pendingName !== null) {
            const url = line;
            // استخراج ID من الرابط (عادة رقم قبل الامتداد أو في آخر جزء من المسار)
            const idMatch = url.match(/\/(\d+)(?:\.[a-zA-Z0-9]+)?(?:\?.*)?$/);
            const id = idMatch ? idMatch[1] : String(channels.length + 1);
            channels.push({ id, name: pendingName, url });
            pendingName = null;
        }
    }
    return channels;
}

// جلب قائمة القنوات مع استخدام الكاش إن كان حديثاً
async function fetchUgeenChannels(forceRefresh = false) {
    const now = Date.now();
    if (!forceRefresh && ugeenChannelsCache.length > 0 && (now - ugeenChannelsCacheTime) < UGEEN_CACHE_TTL) {
        return ugeenChannelsCache;
    }

    const res = await axios.get(
        `${UGEEN_CONFIG.host}/get.php?username=${UGEEN_CONFIG.user}&password=${UGEEN_CONFIG.pass}&type=m3u&output=ts`,
        { timeout: 30000 }
    );

    const channels = parseM3U(res.data);
    if (channels.length === 0) throw new Error('تعذر تحليل قائمة القنوات (M3U فارغة أو بصيغة غير متوقعة).');

    ugeenChannelsCache = channels;
    ugeenChannelsCacheTime = now;
    return channels;
}

// ============================================================
// قائمة IPTV ثابتة (iptv-org) — منفصلة تمامًا عن UGEEN
// ============================================================
const FIXED_IPTV_URL = 'https://iptv-org.github.io/iptv/index.m3u';
let fixedIptvCache = [];
let fixedIptvCacheTime = 0;
const FIXED_IPTV_CACHE_TTL = 10 * 60 * 1000; // 10 دقائق

async function fetchFixedIptvChannels(forceRefresh = false) {
    const now = Date.now();
    if (!forceRefresh && fixedIptvCache.length > 0 && (now - fixedIptvCacheTime) < FIXED_IPTV_CACHE_TTL) {
        return fixedIptvCache;
    }

    const res = await axios.get(FIXED_IPTV_URL, { timeout: 30000 });
    const channels = parseM3U(res.data);
    if (channels.length === 0) throw new Error('تعذر تحليل قائمة القنوات الثابتة.');

    fixedIptvCache = channels;
    fixedIptvCacheTime = now;
    return channels;
}

// ============================================================
// مصدر M3U مستقل قابل للاستبدال — أمر .setm3u / .m3usource
// مستقل تماماً عن UGEEN_CONFIG وعن قائمة iptv-org الثابتة، ومكتوب
// بالكامل هنا داخل index.js بدون أي اعتماد على ملفات خارجية.
// ============================================================
const M3U_SOURCE_CONFIG_PATH = path.join(process.cwd(), 'data', 'm3u_source_config.json');
const M3U_SOURCE_CONFIG = { url: null };

try {
    if (fs.existsSync(M3U_SOURCE_CONFIG_PATH)) {
        const savedSrc = JSON.parse(fs.readFileSync(M3U_SOURCE_CONFIG_PATH, 'utf8'));
        if (savedSrc.url) {
            M3U_SOURCE_CONFIG.url = savedSrc.url;
            console.log('✅ تم تحميل مصدر M3U المستقل المحفوظ من', M3U_SOURCE_CONFIG_PATH);
        }
    }
} catch (e) {
    console.log('⚠️ فشل تحميل مصدر M3U المستقل المحفوظ:', e.message);
}

let m3uSourceChannelsCache = [];
let m3uSourceChannelsCacheTime = 0;
const M3U_SOURCE_CACHE_TTL = 10 * 60 * 1000; // 10 دقائق

// جلب قنوات مصدر M3U المستقل الحالي (مع كاش)
async function fetchM3USourceChannels(forceRefresh = false) {
    if (!M3U_SOURCE_CONFIG.url) {
        throw new Error('لم يتم ضبط أي مصدر M3U بعد. استخدم أمر .setm3u [رابط] أولاً.');
    }

    const now = Date.now();
    if (!forceRefresh && m3uSourceChannelsCache.length > 0 && (now - m3uSourceChannelsCacheTime) < M3U_SOURCE_CACHE_TTL) {
        return m3uSourceChannelsCache;
    }

    const res = await axios.get(M3U_SOURCE_CONFIG.url, { timeout: 30000 });
    const channels = parseM3U(res.data);
    if (channels.length === 0) throw new Error('تعذر تحليل قائمة القنوات (M3U فارغة أو بصيغة غير متوقعة).');

    m3uSourceChannelsCache = channels;
    m3uSourceChannelsCacheTime = now;
    return channels;
}

// استبدال/تحديث رابط مصدر M3U — يتحقق أولاً قبل الحفظ الدائم لتفادي حفظ رابط لا يعمل
async function replaceM3USource(newUrl) {
    if (!newUrl || !/^https?:\/\//i.test(newUrl.trim())) {
        throw new Error('الرابط غير صحيح. يجب أن يبدأ بـ http:// أو https://');
    }

    const oldUrl = M3U_SOURCE_CONFIG.url;
    const oldCache = m3uSourceChannelsCache;
    const oldCacheTime = m3uSourceChannelsCacheTime;

    // تجربة الرابط الجديد مؤقتاً قبل الاعتماد النهائي
    M3U_SOURCE_CONFIG.url = newUrl.trim();
    m3uSourceChannelsCache = [];
    m3uSourceChannelsCacheTime = 0;

    try {
        const channels = await fetchM3USourceChannels(true);

        // نجح التحقق → حفظ دائم على القرص
        const dataDir = path.dirname(M3U_SOURCE_CONFIG_PATH);
        if (!fs.existsSync(dataDir)) fs.mkdirSync(dataDir, { recursive: true });
        fs.writeFileSync(M3U_SOURCE_CONFIG_PATH, JSON.stringify({ url: M3U_SOURCE_CONFIG.url }, null, 2));

        return { url: M3U_SOURCE_CONFIG.url, channelCount: channels.length };
    } catch (err) {
        // فشل التحقق → استرجاع الإعدادات القديمة لتفادي كسر المصدر السابق
        M3U_SOURCE_CONFIG.url = oldUrl;
        m3uSourceChannelsCache = oldCache;
        m3uSourceChannelsCacheTime = oldCacheTime;
        throw err;
    }
}

// ============================================================
// إعدادات "المُنزّل عن بُعد" (Remote Downloader عبر GitHub Actions)
// يعتمد على مستودع خارجي (fork من sadekch1/file-splitter) يحتوي على
// split_upload.py + workflow بإسم REMOTE_DL_CONFIG.workflowFile.
// البوت يشغّل الـ workflow، ينتظر اكتماله، ثم يسحب روابط الأجزاء من
// الـ Release الناتج ويعيد تحميلها/إرسالها في المحادثة.
// ============================================================
const REMOTE_DL_CONFIG_PATH = path.join(process.cwd(), 'data', 'remotedl_config.json');
const REMOTE_DL_CONFIG = {
    owner: '',   // مثال: 'myuser'
    repo: '',    // مثال: 'file-splitter'
    workflowFile: 'remote-download.yml',
    token: process.env.REMOTE_DL_GITHUB_TOKEN || ''
};

try {
    if (fs.existsSync(REMOTE_DL_CONFIG_PATH)) {
        const saved = JSON.parse(fs.readFileSync(REMOTE_DL_CONFIG_PATH, 'utf8'));
        if (saved.owner) REMOTE_DL_CONFIG.owner = saved.owner;
        if (saved.repo) REMOTE_DL_CONFIG.repo = saved.repo;
        if (saved.workflowFile) REMOTE_DL_CONFIG.workflowFile = saved.workflowFile;
        if (saved.token) REMOTE_DL_CONFIG.token = saved.token;
        console.log('✅ تم تحميل إعدادات Remote Downloader المحفوظة من', REMOTE_DL_CONFIG_PATH);
    }
} catch (e) {
    console.log('⚠️ فشل تحميل إعدادات Remote Downloader:', e.message);
}

function saveRemoteDlConfig() {
    const dataDir = path.dirname(REMOTE_DL_CONFIG_PATH);
    if (!fs.existsSync(dataDir)) fs.mkdirSync(dataDir, { recursive: true });
    fs.writeFileSync(REMOTE_DL_CONFIG_PATH, JSON.stringify(REMOTE_DL_CONFIG, null, 2));
}

function remoteDlHeaders() {
    return {
        'Authorization': `Bearer ${REMOTE_DL_CONFIG.token}`,
        'Accept': 'application/vnd.github+json',
        'X-GitHub-Api-Version': '2022-11-28',
        'User-Agent': 'KnightBot-RemoteDL'
    };
}

// ── تتبع التحميلات النشطة عن بُعد لكل محادثة (لدعم أمر .stopremotedl) ──
const activeRemoteDl = new Map(); // chatId -> { cancelled, runId }

// إلغاء تشغيل الـ workflow نفسه على GitHub (لا يفيد بعد اكتماله، فقط أثناء التشغيل)
async function cancelRemoteRun(runId) {
    try {
        await axios.post(
            `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/actions/runs/${runId}/cancel`,
            {}, { headers: remoteDlHeaders(), timeout: 15000 }
        );
    } catch (_) {}
}

// تشغيل الـ workflow عن بُعد (workflow_dispatch) — يعيد وقت الإطلاق لاستخدامه لاحقاً
async function triggerRemoteDownload(fileUrl, chunkSizeMb = 100) {
    if (!REMOTE_DL_CONFIG.token || !REMOTE_DL_CONFIG.owner || !REMOTE_DL_CONFIG.repo) {
        throw new Error('لم يتم ضبط إعدادات Remote Downloader بعد. استخدم أمر .setremotedl أولاً.');
    }
    const dispatchTime = new Date();
    const url = `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/actions/workflows/${REMOTE_DL_CONFIG.workflowFile}/dispatches`;

    await axios.post(url, {
        ref: 'main',
        inputs: { file_url: fileUrl, chunk_size_mb: String(chunkSizeMb) }
    }, { headers: remoteDlHeaders(), timeout: 15000 });

    return dispatchTime;
}

// البحث عن الـ run الذي بدأ بعد وقت الإطلاق (workflow_dispatch لا يُرجع run id مباشرة)
async function findTriggeredRun(dispatchTime, maxWaitMs = 30000) {
    const url = `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/actions/workflows/${REMOTE_DL_CONFIG.workflowFile}/runs?event=workflow_dispatch&per_page=5`;
    const deadline = Date.now() + maxWaitMs;

    while (Date.now() < deadline) {
        const res = await axios.get(url, { headers: remoteDlHeaders(), timeout: 15000 });
        const runs = res.data?.workflow_runs || [];
        const match = runs.find(r => new Date(r.created_at).getTime() >= dispatchTime.getTime() - 5000);
        if (match) return match;
        await new Promise(r => setTimeout(r, 3000));
    }
    throw new Error('تعذر العثور على الـ workflow run بعد إطلاقه (تأكد من اسم ملف الـ workflow والفرع main).');
}

// انتظار اكتمال الـ run، مع استدعاء onTick دورياً لإرسال تحديثات
// control (اختياري): إذا control.cancelled = true أثناء الانتظار، يتم إلغاء الـ run فعلياً على GitHub
// ويُرمى خطأ خاص (isCancelled = true) يُميَّز عن الفشل العادي في المستدعي
async function waitForRunCompletion(runId, maxWaitMs, onTick, control) {
    const url = `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/actions/runs/${runId}`;
    const deadline = Date.now() + maxWaitMs;
    let lastTick = Date.now();

    while (Date.now() < deadline) {
        if (control?.cancelled) {
            await cancelRemoteRun(runId);
            const err = new Error('تم إلغاء التحميل عن بُعد بطلبك.');
            err.isCancelled = true;
            throw err;
        }

        const res = await axios.get(url, { headers: remoteDlHeaders(), timeout: 15000 });
        const run = res.data;
        if (run.status === 'completed') return run;

        if (onTick && Date.now() - lastTick > 120000) {
            lastTick = Date.now();
            await onTick(run);
        }
        await new Promise(r => setTimeout(r, 8000));
    }
    throw new Error('انتهت مهلة الانتظار (timeout) قبل اكتمال التحميل عن بُعد.');
}

// جلب الإصدار (Release) الذي أنشأه الـ run والحصول على روابط الأجزاء من direct_links.txt
// ملاحظة: لا نعتمد على مقارنة أي توقيت (لا وقت إطلاق البوت ولا created_at) لأن اسم
// الـ tag (split-upload-<timestamp>) يُولَّد داخل split_upload.py وقت تنفيذه الفعلي
// على GitHub، وقد يختلف عن ساعة سيرفر البوت. بدلاً من ذلك: قائمة releases عند GitHub
// تُرجَع دائماً مرتّبة من الأحدث للأقدم، فنأخذ أول عنصر مطابق للنمط ببساطة (وهو
// الإصدار الذي أنشأه آخر تشغيل ناجح لهذا المستودع).
async function fetchRemoteDlResult() {
    const url = `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/releases?per_page=10`;
    const res = await axios.get(url, { headers: remoteDlHeaders(), timeout: 15000 });
    const releases = res.data || [];

    const release = releases.find(r => r.tag_name?.startsWith('split-upload-'));
    if (!release) throw new Error('تم تشغيل الـ workflow لكن تعذر العثور على الإصدار (Release) الناتج.');

    const linksAsset = release.assets?.find(a => a.name.startsWith('direct_links'));
    if (!linksAsset) throw new Error('لم يتم العثور على ملف الروابط (direct_links.txt) في الإصدار.');

    const linksRes = await axios.get(linksAsset.url, {
        headers: { ...remoteDlHeaders(), 'Accept': 'application/octet-stream' },
        timeout: 15000
    });

    const links = String(linksRes.data).split(/\r?\n/).map(l => l.trim()).filter(Boolean);
    if (links.length === 0) throw new Error('ملف الروابط فارغ.');

    return { release, links };
}

// حذف الإصدار والـ tag بعد إرسال الملفات (تنظيف اختياري لتفادي تراكم الإصدارات على المستودع)
async function cleanupRemoteDlRelease(release) {
    try {
        await axios.delete(
            `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/releases/${release.id}`,
            { headers: remoteDlHeaders(), timeout: 15000 }
        );
    } catch (_) {}
    try {
        await axios.delete(
            `https://api.github.com/repos/${REMOTE_DL_CONFIG.owner}/${REMOTE_DL_CONFIG.repo}/git/refs/tags/${release.tag_name}`,
            { headers: remoteDlHeaders(), timeout: 15000 }
        );
    } catch (_) {}
}

// ============================================================
// مخازن مؤقتة (Cache)
// ============================================================
const animeCache = new Map();
const qualityCache = new Map();
const akwamCache = new Map();
const mangaCache = new Map();
const okruCache = new Map();

// Import lightweight store
const store = require('./lib/lightweight_store')
store.readFromFile()
const settings = require('./settings')
setInterval(() => store.writeToFile(), settings.storeWriteInterval || 10000)

// Memory optimization
setInterval(() => {
    if (global.gc) {
        global.gc()
        console.log('🧹 Garbage collection completed')
    }
}, 60_000)

// Memory monitoring
setInterval(() => {
    const used = process.memoryUsage().rss / 1024 / 1024
    if (used > 1500) {
        console.log('⚠️ RAM too high (>250MB), restarting bot...')
        process.exit(1)
    }
}, 30_000)

let phoneNumber = ""
let owner = JSON.parse(fs.readFileSync('./data/owner.json'))

global.botname = "KNIGHT BOT"
global.themeemoji = "•"
const pairingCode = process.argv.includes("--pairing-code")
const usePairing = pairingCode || !!process.env.GITHUB_ACTIONS
const useMobile = process.argv.includes("--mobile")

const rl = process.stdin.isTTY ? readline.createInterface({ input: process.stdin, output: process.stdout }) : null
const question = (text) => {
    if (rl) {
        return new Promise((resolve) => rl.question(text, resolve))
    } else {
        return Promise.resolve(settings.ownerNumber || phoneNumber)
    }
}

// ============================================================
// دوال مساعدة لـ akwam
// ============================================================
const AKWAM_HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
    'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
    'Accept-Language': 'ar,en;q=0.5',
    'Referer': 'https://akwam.it/'
};

async function akwamFetch(url) {
    const res = await axios.get(url, {
        headers: AKWAM_HEADERS,
        timeout: 15000,
        validateStatus: s => s < 500
    });
    return res.data;
}

function extractAkwamSeries(html) {
    const results = [];
    const regex = /href="(https?:\/\/akwam\.it\/series\/[^"#?]+)"/g;
    let m;
    while ((m = regex.exec(html)) !== null) {
        const url = m[1].split('?')[0];
        if (!results.some(r => r.url === url)) {
            const slug = url.replace(/.*\/series\//, '').replace(/\/$/, '');
            results.push({ url, name: decodeURIComponent(slug).replace(/-/g, ' ') });
        }
    }
    return results;
}

function extractAkwamEpisodes(html) {
    const results = [];
    const regex = /href="(https?:\/\/akwam\.it\/episode\/[^"#?]+)"/g;
    let m;
    while ((m = regex.exec(html)) !== null) {
        const url = m[1].split('?')[0];
        if (!results.includes(url)) results.push(url);
    }
    return results;
}

async function extractAkwamMp4Links(epUrl) {
    const html = await akwamFetch(epUrl);
    const watchMatch = html.match(/"(https?:\/\/akwam\.it\/watch[^"]+)"/);
    if (!watchMatch) return [];
    const watchHtml = await akwamFetch(watchMatch[1]);
    const mp4Links = [...new Set(
        (watchHtml.match(/https?:\/\/[^"'\s<>]+\.mp4[^"'\s<>]*/g) || [])
    )].filter(l => !l.includes('sample') && !l.includes('preview'));
    return mp4Links;
}

// ============================================================
// دالة جلب روابط جودات حلقة أنمي معينة (قابلة لإعادة الاستخدام)
// ============================================================
async function fetchAnimeQualityLines(slug, epNum) {
    const fullUrl = `http://103.155.92.42/watch/${slug}/${epNum}`;
    const fallbackUrl = `http://103.155.92.42/anime/${slug}/${epNum}`;

    const fetchPage = async (url) => axios.get(url, {
        headers: {
            'User-Agent': 'Mozilla/5.0',
            'Referer': 'http://103.155.92.42/'
        },
        timeout: 10000,
        validateStatus: s => s < 500
    });

    let lines = [];
    const regexLink = /https?:\/\/bkvideo\.site\/video\/[^\s"']+/g;

    try {
        const response = await fetchPage(fullUrl);
        if (response.status === 200 && response.data) {
            lines = response.data.match(regexLink) || [];
        }
    } catch (e) {}

    if (lines.length === 0) {
        try {
            const fallbackResponse = await fetchPage(fallbackUrl);
            if (fallbackResponse.status === 200 && fallbackResponse.data) {
                lines = fallbackResponse.data.match(regexLink) || [];
                if (lines.length === 0) {
                    const iframeRegex = /src=["'](https?:\/\/bkvideo\.site\/video\/[^"'\>]+)["']/g;
                    let match;
                    while ((match = iframeRegex.exec(fallbackResponse.data)) !== null) {
                        lines.push(match[1]);
                    }
                }
            }
        } catch (err) {}
    }

    lines = [...new Set(lines)].map(l => l.trim()).filter(l => l.length > 0);

    const getWeight = (url) => {
        const lower = url.toLowerCase();
        if (lower.includes('fhd') || lower.includes('1080')) return 4;
        if (lower.includes('hd') || lower.includes('720')) return 3;
        if (lower.includes('sd') || lower.includes('480')) return 2;
        if (lower.includes('360')) return 1;
        return 0;
    };
    lines.sort((a, b) => getWeight(a) - getWeight(b));

    return lines;
}

// ============================================================
// دالة بناء ZIP بدون مكتبات خارجية
// ============================================================
const buildZip = (files, outPath) => {
    const entries    = [];
    const centralDir = [];
    let offset       = 0;

    for (const { data, name } of files) {
        const nameBytes = Buffer.from(name, 'utf8');

        let crc = 0xFFFFFFFF;
        for (let i = 0; i < data.length; i++) {
            let b = (crc ^ data[i]) & 0xFF;
            for (let j = 0; j < 8; j++) b = (b & 1) ? (b >>> 1) ^ 0xEDB88320 : b >>> 1;
            crc = (crc >>> 8) ^ b;
        }
        crc = (crc ^ 0xFFFFFFFF) >>> 0;

        const lh = Buffer.alloc(30 + nameBytes.length);
        lh.writeUInt32LE(0x04034b50, 0);
        lh.writeUInt16LE(20, 4);
        lh.writeUInt16LE(0, 6);
        lh.writeUInt16LE(0, 8);
        lh.writeUInt16LE(0, 10);
        lh.writeUInt16LE(0x5360, 12);
        lh.writeUInt32LE(crc, 14);
        lh.writeUInt32LE(data.length, 18);
        lh.writeUInt32LE(data.length, 22);
        lh.writeUInt16LE(nameBytes.length, 26);
        lh.writeUInt16LE(0, 28);
        nameBytes.copy(lh, 30);
        entries.push(Buffer.concat([lh, data]));

        const cd = Buffer.alloc(46 + nameBytes.length);
        cd.writeUInt32LE(0x02014b50, 0);
        cd.writeUInt16LE(20, 4); cd.writeUInt16LE(20, 6);
        cd.writeUInt16LE(0, 8);  cd.writeUInt16LE(0, 10);
        cd.writeUInt16LE(0, 12); cd.writeUInt16LE(0x5360, 14);
        cd.writeUInt32LE(crc, 16);
        cd.writeUInt32LE(data.length, 20);
        cd.writeUInt32LE(data.length, 24);
        cd.writeUInt16LE(nameBytes.length, 28);
        cd.writeUInt16LE(0, 30); cd.writeUInt16LE(0, 32);
        cd.writeUInt16LE(0, 34); cd.writeUInt16LE(0, 36);
        cd.writeUInt32LE(0, 38); cd.writeUInt32LE(offset, 42);
        nameBytes.copy(cd, 46);
        centralDir.push(cd);

        offset += lh.length + data.length;
    }

    const cdBuf = Buffer.concat(centralDir);
    const eocd  = Buffer.alloc(22);
    eocd.writeUInt32LE(0x06054b50, 0);
    eocd.writeUInt16LE(0, 4); eocd.writeUInt16LE(0, 6);
    eocd.writeUInt16LE(files.length, 8);
    eocd.writeUInt16LE(files.length, 10);
    eocd.writeUInt32LE(cdBuf.length, 12);
    eocd.writeUInt32LE(offset, 16);
    eocd.writeUInt16LE(0, 20);

    fs.writeFileSync(outPath, Buffer.concat([...entries, cdBuf, eocd]));
};

// ============================================================
// أدوات تحميل عامة (روابط مباشرة + Google Drive) — قابلة لإعادة الاستخدام
// تُستخدم من أوامر .download و .batchdl و .remotedl
// ============================================================
const DOWNLOAD_MIME_MAP = {
    '.mp4': 'video/mp4', '.mkv': 'video/x-matroska',
    '.webm': 'video/webm', '.avi': 'video/x-msvideo',
    '.zip': 'application/zip', '.rar': 'application/x-rar-compressed',
    '.pdf': 'application/pdf', '.apk': 'application/vnd.android.package-archive',
    '.mp3': 'audio/mpeg', '.ogg': 'audio/ogg',
    '.jpg': 'image/jpeg', '.png': 'image/png',
    '.bin': 'application/octet-stream'
};

function detectDownloadExt(url, contentType = '', contentDisposition = '') {
    const cdMatch = contentDisposition.match(/filename[^;=\n]*=\s*["']?([^"'\n;]+)/i);
    if (cdMatch) {
        const ext = path.extname(cdMatch[1].trim().replace(/["']/g, ''));
        if (ext.length >= 2 && ext.length <= 5) return ext.toLowerCase();
    }
    const urlExt = path.extname(url.split('?')[0]);
    if (urlExt.length >= 2 && urlExt.length <= 5) return urlExt.toLowerCase();
    const ctMap = {
        'video/mp4': '.mp4', 'video/x-matroska': '.mkv',
        'video/webm': '.webm', 'video/avi': '.avi',
        'application/zip': '.zip', 'application/x-rar-compressed': '.rar',
        'application/x-rar': '.rar', 'application/pdf': '.pdf',
        'application/vnd.android.package-archive': '.apk',
        'audio/mpeg': '.mp3', 'audio/ogg': '.ogg',
        'image/jpeg': '.jpg', 'image/png': '.png',
    };
    for (const [ct, ext] of Object.entries(ctMap)) {
        if (contentType.includes(ct)) return ext;
    }
    return '.bin';
}

// استخراج رابط تحميل مباشر من رابط Google Drive (يدعم الملفات الكبيرة التي تحتاج تأكيد "فحص الفيروسات")
async function resolveGoogleDriveUrl(inputUrl) {
    const idMatch = inputUrl.match(/\/d\/([a-zA-Z0-9_-]+)/) || inputUrl.match(/[?&]id=([a-zA-Z0-9_-]+)/);
    if (!idMatch) return null; // ليس رابط Google Drive
    const fileId = idMatch[1];

    const GD_HEADERS = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
    };

    let cookieHeader = '';
    const mergeCookies = (setCookieArr) => {
        if (!setCookieArr) return;
        const parts = setCookieArr.map(c => c.split(';')[0]);
        cookieHeader = cookieHeader ? `${cookieHeader}; ${parts.join('; ')}` : parts.join('; ');
    };

    let url = `https://drive.google.com/uc?export=download&confirm=t&id=${fileId}`;
    let res = await axios.get(url, {
        headers: { ...GD_HEADERS, ...(cookieHeader ? { Cookie: cookieHeader } : {}) },
        responseType: 'text',
        maxRedirects: 5,
        validateStatus: () => true
    });
    mergeCookies(res.headers['set-cookie']);

    const contentType = res.headers['content-type'] || '';
    if (!contentType.includes('text/html')) {
        return { url, headers: { ...GD_HEADERS, ...(cookieHeader ? { Cookie: cookieHeader } : {}) } };
    }

    // صفحة HTML (تحذير فحص فيروسات لملف كبير) — استخرج نموذج التأكيد
    const html = String(res.data);
    const actionMatch  = html.match(/action="([^"]+)"/);
    const idInput      = html.match(/name="id"\s+value="([^"]+)"/);
    const confirmInput = html.match(/name="confirm"\s+value="([^"]+)"/);
    const uuidInput    = html.match(/name="uuid"\s+value="([^"]+)"/);

    if (actionMatch && confirmInput) {
        const params = new URLSearchParams();
        params.set('id', idInput ? idInput[1] : fileId);
        params.set('export', 'download');
        params.set('confirm', confirmInput[1]);
        if (uuidInput) params.set('uuid', uuidInput[1]);
        const finalUrl = `${actionMatch[1].replace(/&amp;/g, '&')}?${params.toString()}`;
        return { url: finalUrl, headers: { ...GD_HEADERS, ...(cookieHeader ? { Cookie: cookieHeader } : {}) } };
    }

    const oldConfirmMatch = html.match(/confirm=([0-9A-Za-z_-]+)&(?:amp;)?id=/);
    if (oldConfirmMatch) {
        const finalUrl = `https://drive.google.com/uc?export=download&confirm=${oldConfirmMatch[1]}&id=${fileId}`;
        return { url: finalUrl, headers: { ...GD_HEADERS, ...(cookieHeader ? { Cookie: cookieHeader } : {}) } };
    }

    throw new Error('تعذر استخراج رابط Google Drive المباشر. تأكد أن الملف "متاح لأي شخص لديه الرابط".');
}

// ── رؤوس افتراضية أقرب لمتصفح حقيقي (تقلل رفض السيرفرات) ──
const DL_BASE_HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
    'Accept': '*/*',
    'Accept-Language': 'ar,en-US;q=0.9,en;q=0.8',
    'Accept-Encoding': 'identity',
    'Connection': 'keep-alive'
};

const sleepMs = (ms) => new Promise(r => setTimeout(r, ms));

// طلب مع إعادة محاولة تلقائية عند 5xx / 429 / أخطاء الشبكة المؤقتة
async function requestWithRetry(config, { retries = 4, baseDelay = 3000 } = {}) {
    let lastErr;
    for (let attempt = 1; attempt <= retries; attempt++) {
        try {
            const res = await axios({ ...config, validateStatus: () => true });

            if (res.status >= 500 || res.status === 429) {
                const retryAfter = parseInt(res.headers?.['retry-after']);
                lastErr = new Error(`السيرفر رد بالحالة ${res.status} (مؤقتًا غير متاح)`);
                if (attempt < retries) {
                    const wait = Math.min(retryAfter ? retryAfter * 1000 : baseDelay * attempt, 30000);
                    await sleepMs(wait);
                    continue;
                }
                throw lastErr;
            }
            return res;
        } catch (e) {
            lastErr = e;
            if (attempt < retries) await sleepMs(baseDelay * attempt);
            else throw lastErr;
        }
    }
    throw lastErr;
}

// فحص الرابط: HEAD أولاً، وعند فشله نستخدم GET بنطاق صغير (bytes=0-0)
// لأن سيرفرات كثيرة ترفض HEAD وترجع 503/405/403 رغم أن GET يعمل
async function resolveDirectUrl(url, headers) {
    try {
        const res = await requestWithRetry(
            { method: 'HEAD', url, headers, timeout: 20000, maxRedirects: 10 },
            { retries: 2, baseDelay: 2000 }
        );
        if (res.status < 400) {
            return { finalUrl: res.request?.res?.responseUrl || url, headRes: res };
        }
    } catch (_) { /* نتجاهل ونجرّب GET */ }

    const res = await requestWithRetry({
        method: 'GET', url,
        headers: { ...headers, 'Range': 'bytes=0-0' },
        timeout: 20000, maxRedirects: 10, responseType: 'stream'
    });

    try { res.data.destroy(); } catch (_) {}

    if (res.status >= 400 && res.status !== 416) {
        throw new Error(`تعذر الوصول للرابط (HTTP ${res.status}) — قد يكون السيرفر مطفأ أو الرابط منتهي الصلاحية.`);
    }

    // استخراج الحجم الكلي من content-range لأن content-length هنا = 1 بايت
    const cr = res.headers['content-range'];
    if (cr) {
        const total = parseInt(String(cr).split('/')[1]);
        if (total && !isNaN(total)) res.headers['content-length'] = String(total);
        res.headers['accept-ranges'] = 'bytes';
    } else {
        res.headers['accept-ranges'] = res.headers['accept-ranges'] || 'none';
    }

    return { finalUrl: res.request?.res?.responseUrl || url, headRes: res };
}

// ── عرض تقدم التحميل في السجل (كل 5 ثوانٍ) ──
function makeProgress(label, total) {
    const t = { label, total: total || 0, bytes: 0, start: Date.now(), timer: null };
    t.timer = setInterval(() => {
        const mb = t.bytes / 1048576;
        const sec = Math.max((Date.now() - t.start) / 1000, 0.1);
        const pct = t.total ? ` (${(t.bytes / t.total * 100).toFixed(1)}%)` : '';
        const tot = t.total ? ` / ${(t.total / 1048576).toFixed(1)} MB` : '';
        console.log(`[PROGRESS] ${t.label}: ${mb.toFixed(1)} MB${tot}${pct} | ${(mb / sec).toFixed(2)} MB/s | ${sec.toFixed(0)}s`);
    }, 5000);
    t.add = (n) => { t.bytes += n; };
    t.stop = () => clearInterval(t.timer);
    return t;
}
function trackStream(stream, label, total) {
    const t = makeProgress(label, parseInt(total) || 0);
    stream.on('data', (c) => t.add(c.length));
    const end = () => t.stop();
    stream.on('end', end); stream.on('error', end); stream.on('close', end);
    return t;
}

function downloadChunkToFile(url, start, end, destPath, headers, tracker) {
    return new Promise(async (resolve, reject) => {
        try {
            const res = await requestWithRetry({
                method: 'GET', url, responseType: 'stream', timeout: 1800000,
                maxRedirects: 10, headers: { ...headers, 'Range': `bytes=${start}-${end}` }
            }, { retries: 4, baseDelay: 4000 });

            if (res.status >= 400) return reject(new Error(`فشل تحميل الجزء (HTTP ${res.status})`));

            const writer = fs.createWriteStream(destPath);
            if (tracker) res.data.on('data', (c) => tracker.add(c.length));
            res.data.pipe(writer);
            res.data.on('error', reject);
            writer.on('finish', resolve);
            writer.on('error', reject);
        } catch (e) { reject(e); }
    });
}

function mergeChunkFiles(chunkPaths, outputPath) {
    return new Promise((resolve, reject) => {
        const out = fs.createWriteStream(outputPath, { flags: 'a' });
        const writeNext = (i) => {
            if (i >= chunkPaths.length) { out.end(); return resolve(); }
            const src = fs.createReadStream(chunkPaths[i]);
            src.pipe(out, { end: false });
            src.on('end', () => {
                try { fs.unlinkSync(chunkPaths[i]); } catch (_) {}
                writeNext(i + 1);
            });
            src.on('error', reject);
        };
        writeNext(0);
        out.on('error', reject);
    });
}

// تحميل بخيط واحد مع إعادة محاولة — يُستخدم كخطة بديلة عند فشل التحميل المتوازي
async function singleStreamDownload(url, headers, outputPath, tracker) {
    const res = await requestWithRetry({
        method: 'GET', url, responseType: 'stream',
        timeout: 1800000, maxRedirects: 10, headers
    }, { retries: 4, baseDelay: 4000 });

    if (res.status >= 400) throw new Error(`فشل التحميل (HTTP ${res.status})`);

    const writer = fs.createWriteStream(outputPath);
    if (tracker) res.data.on('data', (c) => tracker.add(c.length));
    res.data.pipe(writer);
    await new Promise((resolve, reject) => {
        res.data.on('error', reject);
        writer.on('finish', resolve);
        writer.on('error', reject);
    });
}

// الدالة الموحّدة: تُحمّل رابطاً مباشراً أو رابط Google Drive إلى ملف على القرص
// وتُرجع مساره ونوعه وحجمه — يستخدمها كل من .download و .batchdl و .remotedl
async function smartDownloadUrl(rawUrl, tmpDir, fileTag) {
    let finalUrl, headRes, headersToUse = { ...DL_BASE_HEADERS };

    const gdrive = /drive\.google\.com|docs\.google\.com/i.test(rawUrl)
        ? await resolveGoogleDriveUrl(rawUrl)
        : null;

    if (gdrive) {
        finalUrl = gdrive.url;
        headersToUse = gdrive.headers;
        headRes = await axios({
            method: 'HEAD', url: finalUrl, headers: headersToUse,
            timeout: 20000, maxRedirects: 10, validateStatus: () => true
        }).catch(err => err.response || {});
    } else {
        try {
            headersToUse = { ...DL_BASE_HEADERS, 'Referer': new URL(rawUrl).origin + '/' };
        } catch (_) {}
        const resolved = await resolveDirectUrl(rawUrl, headersToUse);
        finalUrl = resolved.finalUrl;
        headRes = resolved.headRes;
        try {
            headersToUse = { ...headersToUse, 'Referer': new URL(finalUrl).origin + '/' };
        } catch (_) {}
    }

    const contentType  = headRes?.headers?.['content-type'] || '';
    const contentDisp  = headRes?.headers?.['content-disposition'] || '';
    const totalSize    = parseInt(headRes?.headers?.['content-length'] || '0');
    const acceptRanges = headRes?.headers?.['accept-ranges'] === 'bytes';

    const fileExt  = detectDownloadExt(finalUrl, contentType, contentDisp);
    const mimeType = DOWNLOAD_MIME_MAP[fileExt] || 'application/octet-stream';

    const fileId = randomBytes(4).toString('hex');
    const outputPath = path.join(tmpDir, `${fileTag || 'DL'}_${fileId}${fileExt}`);
    const chunkPaths = [];
    const THREADS = 8;

    let _dlName = (String(contentDisp).match(/filename\*?=(?:UTF-8'')?"?([^";]+)/i) || [])[1];
    if (!_dlName) { try { _dlName = decodeURIComponent(path.basename(new URL(finalUrl).pathname)) || '?'; } catch (_) { _dlName = '?'; } }
    const _parallel = !gdrive && acceptRanges && totalSize > 1024 * 1024;
    console.log(`[DOWNLOAD] info: name=${_dlName} | type=${contentType || '?'} | size=${totalSize ? (totalSize / 1048576).toFixed(1) + ' MB' : 'unknown'} | mode=${gdrive ? 'gdrive' : (_parallel ? 'parallel x' + THREADS : 'single')}`);
    const tracker = makeProgress(`${fileTag || 'DL'} ${_dlName}`.slice(0, 80), totalSize);

    const cleanupChunks = () => {
        for (const cp of chunkPaths) { try { if (fs.existsSync(cp)) fs.unlinkSync(cp); } catch (_) {} }
        chunkPaths.length = 0;
    };

    try {
        // Google Drive لا يدعم التقسيم المتوازي بشكل موثوق (روابط التأكيد أحادية الاستخدام أحياناً)
        if (!gdrive && acceptRanges && totalSize > 1024 * 1024) {
            try {
                const chunkSize = Math.ceil(totalSize / THREADS);
                const promises = [];
                for (let i = 0; i < THREADS; i++) {
                    const start = i * chunkSize;
                    const end = Math.min(start + chunkSize - 1, totalSize - 1);
                    const chunkPath = path.join(tmpDir, `chunk_${fileId}_${i}`);
                    chunkPaths.push(chunkPath);
                    promises.push(downloadChunkToFile(finalUrl, start, end, chunkPath, headersToUse, tracker));
                }
                await Promise.all(promises);
                await mergeChunkFiles(chunkPaths, outputPath);
            } catch (parallelErr) {
                // خطة بديلة: بعض السيرفرات تخنق الاتصالات المتوازية وترد 503
                cleanupChunks();
                try { if (fs.existsSync(outputPath)) fs.unlinkSync(outputPath); } catch (_) {}
                console.log('[DOWNLOAD] parallel failed, retrying single stream...');
                tracker.bytes = 0; tracker.start = Date.now();
                await sleepMs(3000);
                await singleStreamDownload(finalUrl, headersToUse, outputPath, tracker);
            }
        } else {
            await singleStreamDownload(finalUrl, headersToUse, outputPath, tracker);
        }
        tracker.stop();
    } catch (err) {
        tracker.stop();
        cleanupChunks();
        try { if (fs.existsSync(outputPath)) fs.unlinkSync(outputPath); } catch (_) {}
        throw err;
    }

    const stat = fs.statSync(outputPath);
    if (stat.size === 0) {
        try { fs.unlinkSync(outputPath); } catch (_) {}
        throw new Error('الملف الناتج فارغ (0 بايت) — السيرفر رفض التحميل.');
    }

    const finalSizeMB = (stat.size / 1024 / 1024).toFixed(2);
    return { outputPath, fileExt, mimeType, sizeMB: finalSizeMB, isGoogleDrive: !!gdrive };
}

// ============================================================
// البوت الرئيسي
// ============================================================
async function startXeonBotInc() {
    try {
        let { version, isLatest } = await fetchLatestBaileysVersion()
        const { state, saveCreds } = await useMultiFileAuthState(`./session`)
        const msgRetryCounterCache = new NodeCache()

        const XeonBotInc = makeWASocket({
            version,
            logger: pino({ level: 'silent' }),
            printQRInTerminal: !usePairing,
            browser: ["Ubuntu", "Chrome", "20.0.04"],
            auth: {
                creds: state.creds,
                keys: makeCacheableSignalKeyStore(state.keys, pino({ level: "fatal" }).child({ level: "fatal" })),
            },
            markOnlineOnConnect: false,
            generateHighQualityLinkPreview: true,
            syncFullHistory: false,
            getMessage: async (key) => {
                let jid = jidNormalizedUser(key.remoteJid)
                let msg = await store.loadMessage(jid, key.id)
                return msg?.message || ""
            },
            msgRetryCounterCache,
            defaultQueryTimeoutMs: 60000,
            connectTimeoutMs: 60000,
            keepAliveIntervalMs: 10000,
        })

        XeonBotInc.ev.on('creds.update', saveCreds)
        store.bind(XeonBotInc.ev)

        // ── طلب Pairing Code تلقائياً (لتشغيل GitHub Actions) ──
        if (usePairing && !XeonBotInc.authState.creds.registered) {
            global.__pairTries = (global.__pairTries || 0) + 1
            if (global.__pairTries <= 3) {
                let num = String(require('./settings').ownerNumber || (owner && owner[0]) || '').replace(/[^0-9]/g, '')
                setTimeout(async () => {
                    try {
                        let code = await XeonBotInc.requestPairingCode(num)
                        code = code?.match(/.{1,4}/g)?.join('-') || code
                        console.log('Your Pairing Code : ' + code)
                        console.log('Enter it now: WhatsApp > Linked Devices > Link with phone number')
                    } catch (e) { console.error('Pairing code error:', e.message) }
                }, 3000)
            }
        }

        // ============================================================
        // معالجة الرسائل
        // ============================================================
        XeonBotInc.ev.on('messages.upsert', async chatUpdate => {
            try {
                const mek = chatUpdate.messages[0]
                if (!mek.message) return
                mek.message = (Object.keys(mek.message)[0] === 'ephemeralMessage')
                    ? mek.message.ephemeralMessage.message
                    : mek.message

                const msgType = Object.keys(mek.message || {})[0];
                let text = '';
                if (msgType === 'conversation') text = mek.message.conversation;
                else if (msgType === 'extendedTextMessage') text = mek.message.extendedTextMessage.text;
                else if (mek.message?.[msgType]?.caption) text = mek.message[msgType].caption;

                const chatId = mek.key.remoteJid;
                // ── سجل الأوامر (يظهر في Actions) ──
                if (text && text.trim().startsWith('.')) {
                    const _who = String(mek.key.participant || chatId || '').split('@')[0];
                    const _masked = _who.length > 4 ? '***' + _who.slice(-4) : _who;
                    const _where = String(chatId).endsWith('@g.us') ? 'group' : 'private';
                    console.log(`[CMD] ${new Date().toISOString()} | ${_where} | from:${mek.key.fromMe ? 'me' : _masked} | ${text.trim().slice(0, 200)}`);
                }
                const isReply = msgType === 'extendedTextMessage' &&
                    mek.message.extendedTextMessage.contextInfo?.quotedMessage;

                // ============================================================
                // معالجة الردود (Reply)
                // ============================================================
                if (isReply && text) {
                    const quotedId = mek.message.extendedTextMessage.contextInfo.stanzaId;
                    const replyText = text.trim();

                    // ── المرحلة 4: اختيار الجودة ──
                    if (qualityCache.has(quotedId)) {
                        const cached = qualityCache.get(quotedId);
                        const idx = parseInt(replyText) - 1;
                        if (!cached.links[idx]) {
                            await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                            return;
                        }

                        const qName = cached.names[idx];
                        qualityCache.delete(quotedId);

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        // ── تحميل نطاق حلقات أنمي (عدة حلقات بنفس الجودة) ──
                        if (cached.mode === 'anime_range') {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `📥 جودة [${qName}] — سيتم تحميل الحلقات *${cached.fromEp} → ${cached.toEp}*...`
                            }, { quoted: mek });

                            for (let ep = cached.fromEp; ep <= cached.toEp; ep++) {
                                let outPath;
                                try {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `📖 جاري تحميل الحلقة *${ep}*...`
                                    }, { quoted: mek });

                                    const epLines = (ep === cached.fromEp)
                                        ? cached.links
                                        : await fetchAnimeQualityLines(cached.slug, ep);

                                    const finalUrl = epLines[idx] || epLines[epLines.length - 1];

                                    if (!finalUrl) {
                                        await XeonBotInc.sendMessage(chatId, {
                                            text: `⚠️ الحلقة ${ep}: لم يتم العثور عليها، تم التخطي.`
                                        }, { quoted: mek });
                                        continue;
                                    }

                                    outPath = path.join(tmpDir, `vid_${randomBytes(4).toString('hex')}.mp4`);

                                    const response = await axios({
                                        method: 'GET',
                                        url: finalUrl,
                                        responseType: 'stream',
                                        timeout: 1800000,
                                        headers: {
                                            'User-Agent': 'Mozilla/5.0',
                                            'Referer': cached.referer || 'http://103.155.92.42/'
                                        }
                                    });

                                    const writer = fs.createWriteStream(outPath);
                                    trackStream(response.data, `${cached.slug} Ep${ep}`, response.headers['content-length']);
                                    response.data.pipe(writer);

                                    await new Promise((resolve, reject) => {
                                        writer.on('finish', resolve);
                                        writer.on('error', reject);
                                    });

                                    const finalSizeMB = (fs.statSync(outPath).size / 1024 / 1024).toFixed(2);

                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: outPath },
                                        mimetype: 'video/mp4',
                                        fileName: `${cached.slug}_Ep${ep}.mp4`,
                                        caption: `✅ *تم التحميل بنجاح!*\n📌 *الحلقة:* ${ep}\n⚙️ *الجودة:* ${qName}\n⚖️ *الحجم:* ${finalSizeMB} MB`
                                    }, { quoted: mek });

                                } catch (err) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ فشل الحلقة ${ep}: ${err.message}`
                                    }, { quoted: mek });
                                } finally {
                                    try { if (outPath && fs.existsSync(outPath)) fs.unlinkSync(outPath); } catch (_) {}
                                }
                            }

                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ *اكتمل تحميل النطاق!*\n🔖 الحلقات: ${cached.fromEp} → ${cached.toEp}`
                            }, { quoted: mek });

                            return;
                        }

                        // ── تحميل رابط/حلقة واحدة (السلوك الأصلي) ──
                        const finalUrl = cached.links[idx];

                        await XeonBotInc.sendMessage(chatId, {
                            text: `📥 جودة [${qName}] — جاري التحميل، يرجى الانتظار...`
                        }, { quoted: mek });

                        let outPath;

                        try {

                            outPath = path.join(
                                tmpDir,
                                `vid_${randomBytes(4).toString('hex')}.mp4`
                            );

                            const response = await axios({
                                method: 'GET',
                                url: finalUrl,
                                responseType: 'stream',
                                timeout: 1800000,
                                headers: {
                                    'User-Agent': 'Mozilla/5.0',
                                    'Referer': cached.referer || 'https://akwam.it/'
                                }
                            });

                            const writer = fs.createWriteStream(outPath);

                            trackStream(response.data, `${cached.title || 'video'} [${qName}]`, response.headers['content-length']);
                            response.data.pipe(writer);

                            await new Promise((resolve, reject) => {
                                writer.on('finish', resolve);
                                writer.on('error', reject);
                            });

                            const finalSizeMB =
                            (fs.statSync(outPath).size / 1024 / 1024).toFixed(2);

                        await XeonBotInc.sendMessage(chatId, {
                            document: { url: outPath },
                            mimetype: 'video/mp4',
                            fileName: `${cached.title || 'video'}.mp4`,
                            caption:
                        `✅ *تم التحميل بنجاح!*
                        📌 *العنوان:* ${cached.title || '-'}
                        ⚙️ *الجودة:* ${qName}
                        ⚖️ *الحجم:* ${finalSizeMB} MB`
                        }, { quoted: mek });

                        } catch (err) {

                            try {
                                if (outPath && fs.existsSync(outPath))
                                    fs.unlinkSync(outPath);
                            } catch (_) {}

                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل التحميل:\n\`${err.message}\``
                            }, { quoted: mek });

                        } finally {

                            try {
                                if (outPath && fs.existsSync(outPath))
                                    fs.unlinkSync(outPath);
                            } catch (_) {}

                        }

                        return;
                    }

                    // ── اختيار جودة فيديو ok.ru (okruCache) ──
                    if (okruCache.has(quotedId)) {
                        const cached = okruCache.get(quotedId);
                        const idx = parseInt(replyText) - 1;
                        const chosen = cached.videos[idx];

                        if (!chosen) {
                            await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح، اختر رقماً من القائمة.' }, { quoted: mek });
                            return;
                        }

                        okruCache.delete(quotedId);

                        const qualityLabels = {
                            ultra: '2160p (Ultra HD)',
                            quad: '1440p (Quad HD)',
                            full: '1080p (Full HD)',
                            hd: '720p (HD)',
                            sd: '480p (SD)',
                            low: '360p',
                            lowest: '240p',
                            mobile: '144p (Mobile)'
                        };
                        const qLabel = qualityLabels[chosen.name] || chosen.name || 'غير معروفة';

                        await XeonBotInc.sendMessage(chatId, {
                            text: `⬇️ *جاري تحميل الفيديو...*\n📺 الجودة: ${qLabel}`
                        }, { quoted: mek });

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });
                        const tmpPath = path.join(tmpDir, `okru_${randomBytes(4).toString('hex')}.mp4`);

                        try {
                            const videoUrl = String(chosen.url).replace(/\\u0026/g, '&').replace(/\\\//g, '/');

                            const videoRes = await axios({
                                method: 'GET',
                                url: videoUrl,
                                responseType: 'stream',
                                timeout: 1800000,
                                headers: { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36' }
                            });

                            const writer = fs.createWriteStream(tmpPath);
                            trackStream(videoRes.data, 'ok.ru video', videoRes.headers['content-length']);
                            videoRes.data.pipe(writer);
                            await new Promise((resolve, reject) => {
                                writer.on('finish', resolve);
                                writer.on('error', reject);
                            });

                            const sizeMB = (fs.statSync(tmpPath).size / 1024 / 1024).toFixed(2);

                            await XeonBotInc.sendMessage(chatId, {
                                video: { url: tmpPath },
                                mimetype: 'video/mp4',
                                caption: `✅ *${cached.title}*\n⚖️ الحجم: ${sizeMB} MB\n📺 الجودة: ${qLabel}`
                            }, { quoted: mek });

                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل تحميل الفيديو من ok.ru:\n\`${err.message}\``
                            }, { quoted: mek });
                        } finally {
                            if (fs.existsSync(tmpPath)) {
                                try { fs.unlinkSync(tmpPath); } catch (_) {}
                            }
                        }
                        return;
                    }

                    // ── مراحل المانجا (mangaCache) ──
                    if (mangaCache.has(quotedId)) {
                        const cached = mangaCache.get(quotedId);

                        // المرحلة 1: اختيار المانجا
                        if (cached.stage === 'manga_list') {
                            const idx = parseInt(replyText) - 1;
                            if (!cached.results[idx]) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح.' }, { quoted: mek });
                                return;
                            }
                            const selected = cached.results[idx];
                            mangaCache.delete(quotedId);

                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري جلب قائمة فصول *${selected.name}*...`
                            }, { quoted: mek });

                            try {
                                const MANGA_HEADERS = {
                                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                                    'Accept': 'text/html,*/*;q=0.9',
                                    'Accept-Language': 'ar,en;q=0.9',
                                    'Referer': 'https://3asq.online/'
                                };

                                const pageRes = await axios.get(selected.url, {
                                    headers: MANGA_HEADERS, timeout: 15000
                                });
                                const pageHtml = pageRes.data;
                                const mangaSlug = selected.url.replace(/.*\/manga\//, '').replace(/\/$/, '');

                                const chapterRegex = new RegExp(
                                    'href="(https?://3asq\\.online/manga/' + mangaSlug.replace(/-/g, '-') + '/([\\d]+(?:\\.[\\d]+)?)/?)(?:[^"]*)"',
                                    'gi'
                                );

                                const chapters = [];
                                let cm;
                                while ((cm = chapterRegex.exec(pageHtml)) !== null) {
                                    const url = cm[1].endsWith('/') ? cm[1] : cm[1] + '/';
                                    const num = parseFloat(cm[2]);
                                    if (!isNaN(num) && !chapters.some(c => c.num === num)) {
                                        chapters.push({ url, num });
                                    }
                                }

                                if (chapters.length <= 2) {
                                    const nonceMatch = pageHtml.match(/["']nonce["']\s*:\s*["']([a-f0-9]+)["']/);
                                    const idMatch    = pageHtml.match(/postid-([0-9]+)|manga_id[^0-9]+([0-9]+)|data-id="([0-9]+)"/);
                                    const mangaId    = idMatch ? (idMatch[1] || idMatch[2] || idMatch[3]) : null;
                                    const nonce      = nonceMatch ? nonceMatch[1] : '';

                                    if (mangaId) {
                                        try {
                                            const ajaxRes = await axios.post(
                                                'https://3asq.online/wp-admin/admin-ajax.php',
                                                `action=manga_get_chapters&manga=${mangaId}${nonce ? '&nonce=' + nonce : ''}`,
                                                {
                                                    headers: {
                                                        'User-Agent': 'Mozilla/5.0',
                                                        'Referer': selected.url,
                                                        'Content-Type': 'application/x-www-form-urlencoded',
                                                        'X-Requested-With': 'XMLHttpRequest',
                                                        'Origin': 'https://3asq.online'
                                                    },
                                                    timeout: 20000,
                                                    validateStatus: () => true
                                                }
                                            );

                                            const ajaxHtml = typeof ajaxRes.data === 'string'
                                                ? ajaxRes.data
                                                : (ajaxRes.data?.data || '');

                                            const ajaxRegex = /href="(https?:\/\/3asq\.online\/manga\/[^\/]+\/([\d]+(?:\.[\d]+)?)\/?)"/gi;
                                            let am;
                                            while ((am = ajaxRegex.exec(ajaxHtml)) !== null) {
                                                const url = am[1].endsWith('/') ? am[1] : am[1] + '/';
                                                const num = parseFloat(am[2]);
                                                if (!isNaN(num) && !chapters.some(c => c.num === num)) {
                                                    chapters.push({ url, num });
                                                }
                                            }
                                        } catch (_) {}
                                    }

                                    if (chapters.length <= 2 && chapters.length > 0) {
                                        const minCh = Math.min(...chapters.map(c => c.num));
                                        const maxCh = Math.max(...chapters.map(c => c.num));
                                        for (let n = minCh; n <= maxCh; n++) {
                                            if (!chapters.some(c => c.num === n)) {
                                                chapters.push({
                                                    url: `https://3asq.online/manga/${mangaSlug}/${n}/`,
                                                    num: n
                                                });
                                            }
                                        }
                                    }
                                }

                                chapters.sort((a, b) => a.num - b.num);
                                if (chapters.length === 0) throw new Error('تعذر جلب الفصول. تأكد من اسم المانجا.');

                                const first = chapters[0].num;
                                const last  = chapters[chapters.length - 1].num;

                                let chText = `📚 *${selected.name}*\n\n`;
                                chText += `📖 الفصول المتاحة: *${first}* → *${last}*\n`;
                                chText += `📊 العدد الكلي: *${chapters.length}* فصل\n\n`;
                                chText += `💡 **رد (Reply)** بأرقام الفصول المطلوبة:\n`;
                                chText += `مثال: \`1 5\` (من فصل 1 إلى 5)\n`;
                                chText += `أو: \`10\` (فصل واحد فقط)\n\n`;
                                chText += `⚠️ الحد الأقصى 10 فصول في طلب واحد.\n`;
                                chText += `📦 سيتم إرسال كل فصل كملف ZIP منفصل.`;

                                const sentCh = await XeonBotInc.sendMessage(chatId, { text: chText }, { quoted: mek });
                                mangaCache.set(sentCh.key.id, {
                                    stage: 'chapter_select',
                                    mangaName: selected.name,
                                    mangaUrl: selected.url,
                                    chapters,
                                    timestamp: Date.now()
                                });
                                setTimeout(() => mangaCache.delete(sentCh.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, { text: `❌ ${err.message}` }, { quoted: mek });
                            }
                            return;
                        }

                        // المرحلة 2: اختيار الفصول → إرسال كل فصل ZIP منفصل
                        if (cached.stage === 'chapter_select') {
                            const parts   = replyText.trim().split(/\s+/);
                            const fromNum = parseFloat(parts[0]);
                            const toNum   = parts[1] ? parseFloat(parts[1]) : fromNum;
                            mangaCache.delete(quotedId);

                            if (isNaN(fromNum)) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ صيغة غير صحيحة. مثال: `1 5` أو `10`' }, { quoted: mek });
                                return;
                            }

                            const selectedChapters = cached.chapters.filter(
                                c => c.num >= fromNum && c.num <= toNum
                            ).slice(0, 10);

                            if (selectedChapters.length === 0) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ لم يتم العثور على الفصول المطلوبة.' }, { quoted: mek });
                                return;
                            }

                            const tmpDir = path.join(process.cwd(), 'dltmp');
                            if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                            const mangaNameClean = cached.mangaName.replace(/[^\w\s-]/g, '').trim();

                            await XeonBotInc.sendMessage(chatId, {
                                text: `📥 *سيتم إرسال ${selectedChapters.length} فصل — كل فصل كملف ZIP منفصل*\n📚 ${cached.mangaName}\n⏳ جاري البدء...`
                            }, { quoted: mek });

                            // دالة استخراج صور فصل واحد
                            const fetchChapterImgs = async (ch) => {
                                const chRes = await axios.get(ch.url, {
                                    headers: {
                                        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                                        'Referer': 'https://3asq.online/'
                                    },
                                    timeout: 15000
                                });

                                const imgUrls = [];
                                const wpMangaRegex = /(https?:\/\/3asq\.online\/wp-content\/uploads\/WP-manga\/data\/[^"'\s<>]+\.(?:png|jpg|jpeg|webp))/gi;
                                let im;
                                while ((im = wpMangaRegex.exec(chRes.data)) !== null) {
                                    const u = im[1].replace(/&amp;/g, '&').trim();
                                    if (!imgUrls.includes(u)) imgUrls.push(u);
                                }
                                if (imgUrls.length === 0) {
                                    const lazySrcRegex = /data-src="(https?:\/\/3asq\.online\/wp-content\/uploads\/WP-manga\/data\/[^"]+\.(?:png|jpg|jpeg|webp))"/gi;
                                    while ((im = lazySrcRegex.exec(chRes.data)) !== null) {
                                        const u = im[1].replace(/&amp;/g, '&').trim();
                                        if (!imgUrls.includes(u)) imgUrls.push(u);
                                    }
                                }
                                if (imgUrls.length === 0) {
                                    const classRegex = /class="wp-manga-chapter-img"[^>]*(?:src|data-src)="([^"]+\.(?:png|jpg|jpeg|webp))"/gi;
                                    while ((im = classRegex.exec(chRes.data)) !== null) {
                                        const u = im[1].replace(/&amp;/g, '&').trim();
                                        if (u.startsWith('http') && !imgUrls.includes(u)) imgUrls.push(u);
                                    }
                                }
                                return imgUrls;
                            };

                            // ── معالجة كل فصل بشكل منفصل ──
                            for (const ch of selectedChapters) {
                                const batchId    = randomBytes(3).toString('hex');
                                const chZipPath  = path.join(tmpDir, `${mangaNameClean}_Ch${ch.num}_${batchId}.zip`);

                                try {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `📖 جاري تحميل الفصل *${ch.num}*...`
                                    }, { quoted: mek });

                                    const imgUrls = await fetchChapterImgs(ch);
                                    if (imgUrls.length === 0) {
                                        await XeonBotInc.sendMessage(chatId, {
                                            text: `⚠️ الفصل ${ch.num}: لم يتم العثور على صور، تم التخطي.`
                                        }, { quoted: mek });
                                        continue;
                                    }

                                    // تحميل صور الفصل بالتوازي
                                    const dlPromises = imgUrls.map(async (imgUrl, i) => {
                                        const ext = imgUrl.match(/\.(jpg|jpeg|png|webp)/i)?.[1] || 'jpg';
                                        try {
                                            const imgRes = await axios({
                                                method: 'GET', url: imgUrl,
                                                responseType: 'arraybuffer', timeout: 30000,
                                                headers: {
                                                    'User-Agent': 'Mozilla/5.0',
                                                    'Referer': 'https://3asq.online/'
                                                }
                                            });
                                            return {
                                                data: Buffer.from(imgRes.data),
                                                name: `page_${String(i).padStart(3, '0')}.${ext}`
                                            };
                                        } catch (_) { return null; }
                                    });

                                    const downloaded = (await Promise.all(dlPromises))
                                        .filter(Boolean)
                                        .sort((a, b) => a.name.localeCompare(b.name));

                                    if (downloaded.length === 0) {
                                        await XeonBotInc.sendMessage(chatId, {
                                            text: `⚠️ الفصل ${ch.num}: فشل تحميل الصور، تم التخطي.`
                                        }, { quoted: mek });
                                        continue;
                                    }

                                    // بناء ZIP لهذا الفصل فقط
                                    buildZip(downloaded, chZipPath);

                                    const sizeMB = (fs.statSync(chZipPath).size / 1024 / 1024).toFixed(2);

                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: chZipPath },
                                        mimetype: 'application/zip',
                                        fileName: `${mangaNameClean}_Ch${ch.num}.zip`,
                                        caption: `📚 *${cached.mangaName}*\n🔖 الفصل: ${ch.num}\n🖼️ الصفحات: ${downloaded.length}\n⚖️ الحجم: ${sizeMB} MB`
                                    }, { quoted: mek });

                                } catch (err) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ فشل الفصل ${ch.num}: ${err.message}`
                                    }, { quoted: mek });
                                } finally {
                                    // تنظيف فوري بعد كل فصل
                                    try { if (fs.existsSync(chZipPath)) fs.unlinkSync(chZipPath); } catch (_) {}
                                }
                            }

                            // رسالة اكتمال
                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ *اكتمل الإرسال!*\n📚 ${cached.mangaName}\n🔖 الفصول: ${selectedChapters[0].num} → ${selectedChapters[selectedChapters.length - 1].num}\n📦 تم إرسال ${selectedChapters.length} ملف ZIP`
                            }, { quoted: mek });

                            return;
                        }
                    }

                    // ── المرحلة 3 (akwam): اختيار الحلقة → جلب الجودات ──
                    if (akwamCache.has(quotedId)) {
                        const cached = akwamCache.get(quotedId);

                        if (cached.stage === 'series_list') {
                            const idx = parseInt(replyText) - 1;
                            if (!cached.results[idx]) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح.' }, { quoted: mek });
                                return;
                            }
                            const selected = cached.results[idx];
                            akwamCache.delete(quotedId);

                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري جلب حلقات *${selected.name}*...`
                            }, { quoted: mek });

                            try {
                                const html = await akwamFetch(selected.url);
                                const episodes = extractAkwamEpisodes(html);
                                if (episodes.length === 0) throw new Error('لم يتم العثور على حلقات.');

                                let epText = `🎬 *حلقات ${selected.name}:*\n\n`;
                                episodes.slice(0, 40).forEach((ep, i) => {
                                    const label = ep.replace(/.*\/episode\//, '').replace(/-/g, ' ').replace(/\/$/, '');
                                    epText += `*${i + 1}* - ${label}\n`;
                                });
                                epText += `\n💡 **رد (Reply)** برقم الحلقة لاستخراج الجودات.`;

                                const sentEp = await XeonBotInc.sendMessage(chatId, { text: epText }, { quoted: mek });
                                akwamCache.set(sentEp.key.id, {
                                    stage: 'episode_list',
                                    results: episodes.slice(0, 40),
                                    seriesName: selected.name,
                                    timestamp: Date.now()
                                });
                                setTimeout(() => akwamCache.delete(sentEp.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, { text: `❌ ${err.message}` }, { quoted: mek });
                            }
                            return;
                        }

                        if (cached.stage === 'episode_list') {
                            const idx = parseInt(replyText) - 1;
                            if (!cached.results[idx]) {
                                await XeonBotInc.sendMessage(chatId, { text: '❌ رقم غير صحيح.' }, { quoted: mek });
                                return;
                            }
                            const epUrl = cached.results[idx];
                            const seriesName = cached.seriesName;
                            akwamCache.delete(quotedId);

                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري استخراج الجودات المتاحة...`
                            }, { quoted: mek });

                            try {
                                const mp4Links = await extractAkwamMp4Links(epUrl);
                                if (mp4Links.length === 0) throw new Error('لم يتم العثور على روابط تحميل مباشرة.');

                                const getQualityName = (url) => {
                                    const u = url.toLowerCase();
                                    if (u.includes('1080') || u.includes('fhd')) return '🔵 FHD 1080p';
                                    if (u.includes('720') || u.includes('hd'))  return '🟢 HD 720p';
                                    if (u.includes('480') || u.includes('sd'))  return '🟡 SD 480p';
                                    if (u.includes('360'))                       return '🟠 360p';
                                    return `⚪ جودة ${url.match(/(\d{3,4}p)/i)?.[1] || 'غير معروفة'}`;
                                };

                                const getWeight = (url) => {
                                    const u = url.toLowerCase();
                                    if (u.includes('1080') || u.includes('fhd')) return 4;
                                    if (u.includes('720') || u.includes('hd'))  return 3;
                                    if (u.includes('480') || u.includes('sd'))  return 2;
                                    if (u.includes('360'))                       return 1;
                                    return 0;
                                };
                                mp4Links.sort((a, b) => getWeight(b) - getWeight(a));

                                const names = mp4Links.map(l => getQualityName(l));

                                let qText = `⚙️ *الجودات المتاحة لـ ${seriesName}:*\n\n`;
                                names.forEach((n, i) => { qText += `*${i + 1}* - ${n}\n`; });
                                qText += `\n💡 **رد (Reply)** برقم الجودة لبدء التحميل الفوري.`;

                                const sentQ = await XeonBotInc.sendMessage(chatId, { text: qText }, { quoted: mek });
                                qualityCache.set(sentQ.key.id, {
                                    links: mp4Links,
                                    names,
                                    title: seriesName,
                                    referer: 'https://akwam.it/',
                                    timestamp: Date.now()
                                });
                                setTimeout(() => qualityCache.delete(sentQ.key.id), 300000);
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, { text: `❌ ${err.message}` }, { quoted: mek });
                            }
                            return;
                        }
                    }

                    // ── مراحل الأنمي القديمة (animeCache) ──
                    if (animeCache.has(quotedId)) {
                        const cachedData = animeCache.get(quotedId);
                        const parts = replyText.split(/\s+/);

                        if (parts.length >= 2) {
                            const animeIndex = parseInt(parts[0]) - 1;
                            const epArg = parts[1];
                            if (cachedData.results[animeIndex]) {
                                const selectedAnimeSlug = cachedData.results[animeIndex];
                                animeCache.delete(quotedId);

                                // ── دعم نطاق الحلقات: `1 5-10` أو `1 5 10` أو حلقة واحدة `1 5` ──
                                const rangeMatch = epArg.match(/^(\d+)\s*-\s*(\d+)$/);
                                let fromEp, toEp;
                                if (rangeMatch) {
                                    fromEp = parseInt(rangeMatch[1]);
                                    toEp   = parseInt(rangeMatch[2]);
                                } else if (parts.length >= 3 && !isNaN(parseInt(parts[2]))) {
                                    fromEp = parseInt(epArg);
                                    toEp   = parseInt(parts[2]);
                                } else {
                                    fromEp = toEp = parseInt(epArg);
                                }

                                if (isNaN(fromEp) || isNaN(toEp) || fromEp < 1) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: '❌ صيغة غير صحيحة.\n💡 مثال: `1 5` (حلقة واحدة) أو `1 5-10` (نطاق حلقات)'
                                    }, { quoted: mek });
                                    return;
                                }
                                if (toEp < fromEp) { const t = fromEp; fromEp = toEp; toEp = t; }
                                if (toEp - fromEp + 1 > 15) toEp = fromEp + 14; // حد أقصى 15 حلقة في الطلب الواحد

                                const isRange = fromEp !== toEp;
                                const epLabel = isRange ? `${fromEp} → ${toEp}` : `${fromEp}`;

                                await XeonBotInc.sendMessage(chatId, {
                                    text: `⏳ جاري فحص السيرفر واستخراج الجودات للحلقة *${epLabel}*...`
                                }, { quoted: mek });

                                (async () => {
                                    try {
                                        const lines = await fetchAnimeQualityLines(selectedAnimeSlug, fromEp);

                                        if (lines.length === 0) {
                                            await XeonBotInc.sendMessage(chatId, {
                                                text: `❌ تعذر العثور على تيار الفيديو لهذه الحلقة.\n💡 _قد لا تكون الحلقة مرفوعة بعد._`
                                            }, { quoted: mek });
                                            return;
                                        }

                                        let qualityNames = [];
                                        if (lines.length === 4) {
                                            qualityNames = ["أضعف جودة", "جودة متوسطة", "جودة أعلى", "الخارقة (الأعلى)"];
                                        } else {
                                            lines.forEach((_, index) => {
                                                if (index === 0) qualityNames.push("أضعف جودة");
                                                else if (index === lines.length - 1) qualityNames.push("الخارقة (الأعلى)");
                                                else qualityNames.push(`جودة رقم ${index + 1}`);
                                            });
                                        }

                                        let qualityResponseText = `🍿 *اختر جودة تحميل الحلقة ${epLabel}:*\n\n`;
                                        qualityNames.forEach((qName, idx) => {
                                            qualityResponseText += `*${idx + 1}* - ${qName}\n`;
                                        });
                                        if (isRange) {
                                            qualityResponseText += `\n📦 سيتم تحميل *${toEp - fromEp + 1}* حلقة بنفس الجودة المختارة تلقائياً.`;
                                        }
                                        qualityResponseText += `\n💡 قم **بالرد (Reply)** على هذه الرسالة برقم الجودة المطلوبة.`;

                                        const sentQualityMsg = await XeonBotInc.sendMessage(chatId, { text: qualityResponseText }, { quoted: mek });
                                        qualityCache.set(sentQualityMsg.key.id, {
                                            mode: isRange ? 'anime_range' : 'anime_single',
                                            slug: selectedAnimeSlug,
                                            fromEp,
                                            toEp,
                                            links: lines,
                                            names: qualityNames,
                                            title: `${selectedAnimeSlug}_Ep_${epLabel}`,
                                            referer: 'http://103.155.92.42/',
                                            timestamp: Date.now()
                                        });
                                        setTimeout(() => qualityCache.delete(sentQualityMsg.key.id), 300000);
                                    } catch (err) {
                                        await XeonBotInc.sendMessage(chatId, {
                                            text: `❌ ${err.message}`
                                        }, { quoted: mek });
                                    }
                                })();
                                return;
                            }
                        }
                    }
                }

                // ============================================================
                // الأوامر الرئيسية
                // ============================================================
                if (text && (
                    text.startsWith('.download') ||
                    text.startsWith('.batchdl') ||
                    text.startsWith('.apk') ||
                    text.startsWith('.anime') ||
                    text.startsWith('.series') ||
                    text.startsWith('.manga') ||
                    text.startsWith('.movie') ||
                    text.startsWith('.test') ||
                    text.startsWith('.seturl') ||
                    text.startsWith('.channels') ||
                    text.startsWith('.iptv') ||
                    text.startsWith('.recordiptv') ||
                    text.startsWith('.stoprecordiptv') ||
                    text.startsWith('.m3u') ||
                    text.startsWith('.record') ||
                    text.startsWith('.stoprecord') ||
                    text.startsWith('.okru') ||
                    text.startsWith('.playm3u') ||
                    text.startsWith('.stopplaym3u') ||
                    text.startsWith('.setm3u') ||
                    text.startsWith('.m3usource') ||
                    text.startsWith('.remotedl') ||
                    text.startsWith('.stopremotedl') ||
                    text.startsWith('.setremotedl')
                )) {
                    const args = text.split(' ');
                    const command = args[0].toLowerCase();
                    let query = args.slice(1).join(' ').trim();

                    // ============================================================
                    // ── أوامر مشغّل m3u المستقل (.playm3u / .stopplaym3u) ──
                    // مستقلة بالكامل عن .record/.recordiptv وتعتمد على lib/m3uplayer.js
                    // ============================================================

                    // ── أمر .stopplaym3u ──
                    if (command === '.stopplaym3u') {
                        const stopped = m3uPlayer.stopM3UPlayer(chatId);
                        if (!stopped) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `ℹ️ لا يوجد تشغيل m3u نشط حالياً في هذه المحادثة.`
                            }, { quoted: mek });
                            return;
                        }
                        await XeonBotInc.sendMessage(chatId, {
                            text: `🛑 جاري إلغاء تشغيل m3u... سيتم إرسال الجزء الحالي (إن اكتمل) ثم التوقف.`
                        }, { quoted: mek });
                        return;
                    }

                    // ── أمر .playm3u [رابط] [المدة بالدقائق] [مدة الجزء - اختياري] ──
                    if (command === '.playm3u') {
                        const parts = query.split(' ').filter(Boolean);
                        const streamUrl = parts[0];
                        const durationMin = parseInt(parts[1]);
                        const manualSegmentMin = parts[2] && !isNaN(parseInt(parts[2])) ? parseInt(parts[2]) : null;

                        if (!streamUrl || !m3uPlayer.isValidM3UUrl(streamUrl) || isNaN(durationMin)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ الصيغة الصحيحة:\n\`.playm3u [رابط m3u/m3u8] [المدة الكلية بالدقائق] [مدة الجزء بالدقائق - اختياري]\`\n\n💡 مثال: \`.playm3u https://example.com/stream.m3u8 60\`\nأو: \`.playm3u https://example.com/stream.m3u8 60 10\` (كل جزء 10 دقائق بالضبط)`
                            }, { quoted: mek });
                            return;
                        }

                        if (durationMin < 1 || durationMin > m3uPlayer.M3U_MAX_DURATION_MIN) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ المدة يجب أن تكون بين 1 و ${m3uPlayer.M3U_MAX_DURATION_MIN} دقيقة.`
                            }, { quoted: mek });
                            return;
                        }
                        if (manualSegmentMin !== null && (manualSegmentMin < 1 || manualSegmentMin > durationMin)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ مدة الجزء يجب أن تكون بين 1 دقيقة والمدة الكلية.`
                            }, { quoted: mek });
                            return;
                        }

                        if (m3uPlayer.hasActiveM3UPlayer(chatId)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ يوجد تشغيل m3u نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stopplaym3u\` قبل بدء تشغيل جديد.`
                            }, { quoted: mek });
                            return;
                        }

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        // لا ننتظر (fire-and-forget) — تماماً مثل .record — حتى لا يتوقف معالج الرسائل
                        m3uPlayer.startM3UPlayer({
                            sock: XeonBotInc,
                            chatId,
                            mek,
                            streamUrl,
                            durationMin,
                            manualSegmentMin,
                            tmpRootDir: tmpDir
                        }).catch(async (err) => {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ خطأ غير متوقع في مشغّل m3u: ${err.message}`
                            }, { quoted: mek });
                        });
                        return;
                    }

                    // ============================================================
                    // ── أمر .setm3u (استبدال/تحديث رابط مصدر M3U — مستقل عن UGEEN) ──
                    // ============================================================
                    if (command === '.setm3u') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ يرجى إرسال رابط M3U الجديد بعد الأمر.\n💡 مثال:\n\`.setm3u https://example.com/playlist.m3u\`\n\nهذا الأمر مستقل تماماً عن \`.seturl\` (الخاص بـ UGEEN) — يضبط مصدر M3U منفصل خاصاً به، يُستخدم مع \`.m3usource\` للبحث عن قنواته.`
                            }, { quoted: mek });
                            return;
                        }

                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري التحقق من الرابط الجديد...`
                            }, { quoted: mek });

                            const result = await replaceM3USource(query.trim());

                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ *تم استبدال مصدر M3U بنجاح وحُفظ بشكل دائم!*\n🔗 الرابط: ${result.url}\n📺 عدد القنوات المتاحة: ${result.channelCount}\n\n💡 استخدم \`.m3usource [اسم]\` للبحث ضمن هذا المصدر، أو استخدم أي رابط قناة مباشرة مع \`.playm3u\`.`
                            }, { quoted: mek });

                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل استبدال الرابط:\n\`${e.message}\`\n\n⚠️ تم إبقاء المصدر القديم كما هو (لم يُحفظ الرابط الجديد).`
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .m3usource (عرض/بحث قنوات مصدر M3U المستقل الحالي) ──
                    if (command === '.m3usource') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: query
                                    ? `🔍 جاري البحث عن قنوات تحتوي على *${query}* في مصدر M3U الحالي...`
                                    : `📡 جاري جلب قائمة قنوات مصدر M3U الحالي...`
                            }, { quoted: mek });

                            const channels = await fetchM3USourceChannels();

                            let filtered = query
                                ? channels.filter(ch => ch.name.toLowerCase().includes(query.toLowerCase()))
                                : channels;

                            if (filtered.length === 0) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ لم يتم العثور على قنوات تطابق: *${query}*`
                                }, { quoted: mek });
                                return;
                            }

                            let msg = `📺 *نتائج مصدر M3U المستبدل (${filtered.length} قناة):*\n\n`;
                            filtered.slice(0, 20).forEach((ch) => {
                                msg += `${ch.name}\n🆔 ID: \`${ch.id}\`\n🔗 ${ch.url}\n\n`;
                            });
                            if (filtered.length > 20) msg += `💡 _عرض أول 20 نتيجة فقط من ${filtered.length}._\n`;
                            msg += `\n▶️ للتشغيل استخدم: \`.playm3u [الرابط] [المدة بالدقائق]\``;

                            await XeonBotInc.sendMessage(chatId, { text: msg }, { quoted: mek });
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ ${e.message}`
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .seturl (تحديث رابط M3U بعد كل تجديد بدون تعديل الكود) ──
                    if (command === '.seturl') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى إرسال رابط M3U الجديد بعد الأمر.\n💡 مثال:\n`.seturl https://ugeen.live/get.php?username=USER&password=PASS&type=m3u&output=ts`'
                            }, { quoted: mek });
                            return;
                        }

                        let oldConfig;
                        try {
                            const parsed = new URL(query.trim());
                            const newUser = parsed.searchParams.get('username');
                            const newPass = parsed.searchParams.get('password');

                            if (!newUser || !newPass) {
                                throw new Error('لم أتمكن من استخراج اليوزر أو الباسورد من هذا الرابط. تأكد أن الرابط يحتوي على username= و password=');
                            }

                            oldConfig = { ...UGEEN_CONFIG };

                            UGEEN_CONFIG.host = parsed.origin;
                            UGEEN_CONFIG.user = newUser;
                            UGEEN_CONFIG.pass = newPass;

                            // مسح الكاش لإجبار إعادة الجلب بالبيانات الجديدة فوراً
                            ugeenChannelsCache = [];
                            ugeenChannelsCacheTime = 0;

                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ جاري التحقق من الرابط الجديد...`
                            }, { quoted: mek });

                            // تحقق فعلي قبل الحفظ الدائم — لتفادي حفظ رابط لا يعمل
                            const channels = await fetchUgeenChannels(true);

                            // الحفظ الدائم لا يتم إلا بعد نجاح التحقق
                            const dataDir = path.dirname(UGEEN_CONFIG_PATH);
                            if (!fs.existsSync(dataDir)) fs.mkdirSync(dataDir, { recursive: true });
                            fs.writeFileSync(UGEEN_CONFIG_PATH, JSON.stringify(UGEEN_CONFIG, null, 2));

                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ *تم تحديث الرابط بنجاح وحُفظ بشكل دائم!*\n🌐 Host: ${UGEEN_CONFIG.host}\n👤 User: ${UGEEN_CONFIG.user}\n📺 عدد القنوات المتاحة: ${channels.length}\n\n💡 سيبقى هذا الرابط فعّالاً حتى بعد إعادة تشغيل البوت.`
                            }, { quoted: mek });

                        } catch (e) {
                            // فشل التحقق → استرجاع الإعدادات القديمة لتفادي كسر البوت برابط لا يعمل
                            if (typeof oldConfig !== 'undefined') {
                                UGEEN_CONFIG.host = oldConfig.host;
                                UGEEN_CONFIG.user = oldConfig.user;
                                UGEEN_CONFIG.pass = oldConfig.pass;
                                ugeenChannelsCache = [];
                                ugeenChannelsCacheTime = 0;
                            }
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل تحديث الرابط:\n\`${e.message}\`\n\n⚠️ تم إبقاء الإعدادات القديمة كما هي (لم يُحفظ الرابط الجديد).`
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .test ──
                    if (command === '.test') {
                        try {
                            const res = await axios.get(
                                `${UGEEN_CONFIG.host}/get.php?username=${UGEEN_CONFIG.user}&password=${UGEEN_CONFIG.pass}&type=m3u&output=ts`,
                                { timeout: 30000 }
                            );
                            const channelCount = (String(res.data).match(/#EXTINF/g) || []).length;
                            if (channelCount === 0) throw new Error('لم يتم العثور على أي قنوات في الرد (تحقق من صحة الحساب).');
                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ *سيرفر IPTV يعمل بنجاح!*\n📺 إجمالي القنوات المتاحة: *${channelCount}*`
                            }, { quoted: mek });
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل الاتصال بالسيرفر:\n\`${e.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .channels ──
                    if (command === '.channels') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: query
                                    ? `🔍 جاري البحث عن قنوات تحتوي على *${query}*...`
                                    : `📡 جاري جلب قائمة جميع القنوات...`
                            }, { quoted: mek });

                            const channels = await fetchUgeenChannels();

                            let filtered = query
                                ? channels.filter(ch => ch.name.toLowerCase().includes(query.toLowerCase()))
                                : channels;

                            if (filtered.length === 0) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ لم يتم العثور على قنوات تطابق: *${query}*`
                                }, { quoted: mek });
                                return;
                            }

                            let msg = `📺 *نتائج البحث (${filtered.length} قناة):*\n\n`;
                            filtered.slice(0, 20).forEach((ch) => {
                                msg += `${ch.name}\n🆔 ID: \`${ch.id}\`\n\n`;
                            });
                            if (filtered.length > 20) msg += `💡 _عرض أول 20 نتيجة فقط من ${filtered.length}._\n`;
                            msg += `\n▶️ للتسجيل استخدم: \`.record [ID] [المدة بالدقائق]\``;

                            await XeonBotInc.sendMessage(chatId, { text: msg }, { quoted: mek });
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ خطأ في جلب القنوات:\n\`${e.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .iptv (قائمة ثابتة من iptv-org، منفصلة عن UGEEN) ──
                    if (command === '.iptv') {
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: query
                                    ? `🔍 جاري البحث عن قنوات تحتوي على *${query}* في القائمة الثابتة...`
                                    : `📡 جاري جلب قائمة القنوات الثابتة (iptv-org)...`
                            }, { quoted: mek });

                            const channels = await fetchFixedIptvChannels();

                            let filtered = query
                                ? channels.filter(ch => ch.name.toLowerCase().includes(query.toLowerCase()))
                                : channels;

                            if (filtered.length === 0) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ لم يتم العثور على قنوات تطابق: *${query}*`
                                }, { quoted: mek });
                                return;
                            }

                            let msg = `📺 *نتائج قائمة IPTV الثابتة (${filtered.length} قناة):*\n\n`;
                            filtered.slice(0, 20).forEach((ch) => {
                                msg += `${ch.name}\n🆔 ID: \`${ch.id}\`\n🔗 ${ch.url}\n\n`;
                            });
                            if (filtered.length > 20) msg += `💡 _عرض أول 20 نتيجة فقط من ${filtered.length}._\n`;
                            msg += `\n▶️ للتسجيل استخدم: \`.recordiptv [ID] [المدة بالدقائق]\``;

                            await XeonBotInc.sendMessage(chatId, { text: msg }, { quoted: mek });
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ خطأ في جلب القائمة الثابتة:\n\`${e.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .stoprecord ──
                    if (command === '.stoprecord') {
                        const control = activeRecordings.get(chatId);
                        if (!control) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `ℹ️ لا يوجد تسجيل نشط حالياً في هذه المحادثة.`
                            }, { quoted: mek });
                            return;
                        }
                        control.cancelled = true;
                        await XeonBotInc.sendMessage(chatId, {
                            text: `🛑 جاري إلغاء التسجيل... سيتم إرسال الجزء الحالي (إن اكتمل) ثم التوقف.`
                        }, { quoted: mek });
                        return;
                    }

                    // ── أمر .stopremotedl (إلغاء تحميل عن بُعد نشط: يلغي الـ workflow على GitHub إن كان لسه شغال، أو يوقف إرسال الأجزاء المتبقية) ──
                    if (command === '.stopremotedl') {
                        const control = activeRemoteDl.get(chatId);
                        if (!control) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `ℹ️ لا يوجد تحميل عن بُعد نشط حالياً في هذه المحادثة.`
                            }, { quoted: mek });
                            return;
                        }
                        control.cancelled = true;
                        await XeonBotInc.sendMessage(chatId, {
                            text: `🛑 جاري إلغاء التحميل عن بُعد... (سيتم إلغاء تشغيل GitHub Actions إن كان لا يزال يعمل، أو إيقاف إرسال الأجزاء المتبقية)`
                        }, { quoted: mek });
                        return;
                    }

                    // ── أمر .stoprecordiptv (خاص بتسجيلات القائمة الثابتة فقط) ──
                    if (command === '.stoprecordiptv') {
                        const control = activeIptvRecordings.get(chatId);
                        if (!control) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `ℹ️ لا يوجد تسجيل IPTV (ثابت) نشط حالياً في هذه المحادثة.`
                            }, { quoted: mek });
                            return;
                        }
                        control.cancelled = true;
                        await XeonBotInc.sendMessage(chatId, {
                            text: `🛑 جاري إلغاء تسجيل IPTV الثابت... سيتم إرسال الجزء الحالي (إن اكتمل) ثم التوقف.`
                        }, { quoted: mek });
                        return;
                    }

                    // ── أمر .record ──
                    if (command === '.record') {
                        if (args.length < 3 || isNaN(parseInt(args[2]))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ الصيغة الصحيحة:\n\`.record [ID القناة] [المدة الكلية بالدقائق] [مدة الجزء بالدقائق - اختياري]\`\n\n💡 مثال: \`.record 1234 120\` (تسجيل متواصل 120 دقيقة، كل جزء ~${RECORD_TARGET_MB} MB تلقائياً عبر فحص معدل البت)\nأو: \`.record 1234 120 10\` (كل جزء 10 دقائق بالضبط، بدون فحص)\n\n🔍 للحصول على ID القناة استخدم: \`.channels [اسم القناة]\``
                            }, { quoted: mek });
                            return;
                        }

                        const streamId = args[1];
                        const duration = parseInt(args[2]);
                        const manualSegmentMinutes = args[3] && !isNaN(parseInt(args[3])) ? parseInt(args[3]) : null;

                        if (duration < 1 || duration > 360) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ المدة يجب أن تكون بين 1 و 360 دقيقة.`
                            }, { quoted: mek });
                            return;
                        }
                        if (manualSegmentMinutes !== null && (manualSegmentMinutes < 1 || manualSegmentMinutes > duration)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ مدة الجزء يجب أن تكون بين 1 دقيقة والمدة الكلية.`
                            }, { quoted: mek });
                            return;
                        }

                        let channel;
                        try {
                            const channels = await fetchUgeenChannels();
                            channel = channels.find(ch => ch.id === streamId);
                            if (!channel) throw new Error('لم يتم العثور على قناة بهذا الـ ID. تأكد منه عبر أمر .channels');
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ ${e.message}`
                            }, { quoted: mek });
                            return;
                        }

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        if (activeRecordings.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ يوجد تسجيل نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stoprecord\` قبل بدء تسجيل جديد.`
                            }, { quoted: mek });
                            return;
                        }

                        const streamUrl = channel.url;
                        const totalDurationSec = duration * 60;

                        let segmentTimeSec;
                        let segmentMinutes;
                        let bitrateNote = '';

                        if (manualSegmentMinutes !== null) {
                            segmentMinutes = manualSegmentMinutes;
                            segmentTimeSec = manualSegmentMinutes * 60;
                        } else {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري فحص معدل بت القناة لتقدير حجم الجزء بدقة (~${RECORD_TARGET_MB} MB)...`
                            }, { quoted: mek });

                            const bitrate = await probeStreamBitrate(streamUrl);
                            segmentTimeSec = computeSegmentTimeSec(bitrate);
                            segmentMinutes = Math.round(segmentTimeSec / 60);

                            bitrateNote = bitrate
                                ? `\n📊 معدل البت المُقاس: ~${(bitrate / 1000000).toFixed(2)} Mbps`
                                : `\n⚠️ تعذر قياس معدل البت، تم استخدام تقدير احتياطي (${RECORD_DEFAULT_SEGMENT_MIN} دقائق)`;
                        }

                        const segDir = path.join(tmpDir, `rec_${streamId}_${Date.now()}`);
                        fs.mkdirSync(segDir, { recursive: true });

                        await XeonBotInc.sendMessage(chatId, {
                            text: `🎙️ *بدأ التسجيل المتواصل!*\n📺 القناة: ${channel.name}\n🆔 ID: \`${streamId}\`\n⏱️ المدة الكلية: *${duration} دقيقة*\n📦 كل جزء: *~${segmentMinutes} دقيقة* (تقدير لـ ~${RECORD_TARGET_MB} MB)${bitrateNote}\n🔗 اتصال واحد متواصل بالبث — بدون أي انقطاع بين الأجزاء\n\n🛑 لإلغاء التسجيل في أي وقت: \`.stoprecord\``
                        }, { quoted: mek });

                        const control = { proc: null, cancelled: false };
                        activeRecordings.set(chatId, control);

                        const MAX_RECONNECT_ATTEMPTS = 15; // مع التأخير التصاعدي (backoff)، هذا يكفي لتغطية ساعات من الانقطاعات المتكررة بدون إغراق السيرفر

                        (async () => {
                            let segmentIndex = 0;
                            let abortedBySize = false;
                            let wasCancelled = false;
                            let remainingSec = totalDurationSec;
                            let attempt = 0;
                            let reconnectedCount = 0;

                            const onSegmentReady = async (filePath) => {
                                segmentIndex++;
                                try {
                                    const sizeMB = (fs.statSync(filePath).size / 1024 / 1024).toFixed(2);
                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: filePath },
                                        mimetype: 'video/mp4',
                                        fileName: `Match_${streamId}_part${segmentIndex}.mp4`,
                                        caption: `📦 *الجزء ${segmentIndex}*\n📺 ${channel.name}\n⚖️ ${sizeMB} MB`
                                    }, { quoted: mek });
                                } catch (e) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `⚠️ فشل إرسال الجزء ${segmentIndex}: ${e.message}`
                                    }, { quoted: mek });
                                } finally {
                                    try { fs.unlinkSync(filePath); } catch (_) {}
                                }
                            };

                            try {
                                while (remainingSec > 60 && attempt < MAX_RECONNECT_ATTEMPTS && !control.cancelled) {
                                    attempt++;
                                    const startTs = Date.now();

                                    const result = await recordContinuousSegmented(
                                        streamUrl, segDir, `part_a${attempt}`, remainingSec, segmentTimeSec,
                                        onSegmentReady, control
                                    );

                                    const elapsedSec = Math.floor((Date.now() - startTs) / 1000);
                                    remainingSec -= elapsedSec;

                                    abortedBySize = result.abortedBySize;
                                    wasCancelled = result.cancelled;

                                    if (wasCancelled || abortedBySize) break;
                                    if (remainingSec <= 60) break; // اكتملت المدة فعلياً (بهامش بسيط)

                                    // توقف مبكر غير متوقع (انقطاع بث/شبكة) وما زال هناك وقت متبقٍ → أعد الاتصال
                                    reconnectedCount++;
                                    // تأخير تصاعدي: 3، 6، 12، 24، 48 ثانية، ثم يثبت عند 60 ثانية
                                    // لتفادي إغراق السيرفر بطلبات متكررة سريعة (قد يُفسَّر كإساءة استخدام ويؤدي لحظر الـIP)
                                    const backoffMs = Math.min(3000 * Math.pow(2, Math.min(reconnectedCount - 1, 5)), 60000);
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `⚠️ *انقطع الاتصال بالبث بشكل غير متوقع.*\n⏱️ الوقت المتبقي: ~${Math.ceil(remainingSec / 60)} دقيقة\n🔄 جاري إعادة الاتصال بعد ${Math.round(backoffMs / 1000)} ثانية... (محاولة ${attempt + 1}/${MAX_RECONNECT_ATTEMPTS})`
                                    }, { quoted: mek });
                                    await new Promise(r => setTimeout(r, backoffMs));
                                }

                                if (!wasCancelled && !abortedBySize && attempt >= MAX_RECONNECT_ATTEMPTS && remainingSec > 60) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ تعذر إكمال التسجيل بعد ${MAX_RECONNECT_ATTEMPTS} محاولات إعادة اتصال. قد تكون القناة غير مستقرة حالياً.`
                                    }, { quoted: mek });
                                }
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ خطأ في التسجيل: ${err.message}`
                                }, { quoted: mek });
                            } finally {
                                activeRecordings.delete(chatId);
                                try { fs.rmSync(segDir, { recursive: true, force: true }); } catch (_) {}
                            }

                            if (wasCancelled) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🛑 *تم إلغاء التسجيل بطلبك.*\n📦 عدد الأجزاء المُرسلة قبل الإلغاء: ${segmentIndex}`
                                }, { quoted: mek });
                            } else if (abortedBySize) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🛑 *تم إيقاف التسجيل مبكراً!*\nجودة البث كانت أعلى من المتوقع وتجاوز حجم أحد الأجزاء الحد الآمن للتخزين المتاح.\n📦 عدد الأجزاء المُرسلة قبل التوقف: ${segmentIndex}\n\n💡 جرّب تقليل مدة الجزء (مثال: \`.record ${streamId} ${duration} 3\`) للحصول على أجزاء أصغر تلائم جودة هذا البث.`
                                }, { quoted: mek });
                            } else {
                                const reconnectNote = reconnectedCount > 0 ? `\n🔄 حدثت ${reconnectedCount} إعادة اتصال بسبب انقطاعات مؤقتة في البث.` : '';
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `✅ *اكتمل التسجيل الكامل!*\n📺 القناة: ${channel.name}\n📦 عدد الأجزاء المُرسلة: ${segmentIndex}${reconnectNote}`
                                }, { quoted: mek });
                            }
                        })();
                        return;
                    }

                    // ── أمر .recordiptv (تسجيل من القائمة الثابتة iptv-org فقط) ──
                    if (command === '.recordiptv') {
                        if (args.length < 3 || isNaN(parseInt(args[2]))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ الصيغة الصحيحة:\n\`.recordiptv [ID القناة] [المدة الكلية بالدقائق] [مدة الجزء بالدقائق - اختياري]\`\n\n💡 مثال: \`.recordiptv 1234 120\` (تسجيل متواصل 120 دقيقة، كل جزء ~${RECORD_TARGET_MB} MB تلقائياً عبر فحص معدل البت)\nأو: \`.recordiptv 1234 120 10\` (كل جزء 10 دقائق بالضبط، بدون فحص)\n\n🔍 للحصول على ID القناة استخدم: \`.iptv [اسم القناة]\``
                            }, { quoted: mek });
                            return;
                        }

                        const streamId = args[1];
                        const duration = parseInt(args[2]);
                        const manualSegmentMinutes = args[3] && !isNaN(parseInt(args[3])) ? parseInt(args[3]) : null;

                        if (duration < 1 || duration > 360) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ المدة يجب أن تكون بين 1 و 360 دقيقة.`
                            }, { quoted: mek });
                            return;
                        }
                        if (manualSegmentMinutes !== null && (manualSegmentMinutes < 1 || manualSegmentMinutes > duration)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ مدة الجزء يجب أن تكون بين 1 دقيقة والمدة الكلية.`
                            }, { quoted: mek });
                            return;
                        }

                        let channel;
                        try {
                            const channels = await fetchFixedIptvChannels();
                            channel = channels.find(ch => ch.id === streamId);
                            if (!channel) throw new Error('لم يتم العثور على قناة بهذا الـ ID. تأكد منه عبر أمر .iptv');
                        } catch (e) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ ${e.message}`
                            }, { quoted: mek });
                            return;
                        }

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        if (activeIptvRecordings.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ يوجد تسجيل IPTV ثابت نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stoprecordiptv\` قبل بدء تسجيل جديد.`
                            }, { quoted: mek });
                            return;
                        }

                        const streamUrl = channel.url;
                        const totalDurationSec = duration * 60;

                        let segmentTimeSec;
                        let segmentMinutes;
                        let bitrateNote = '';

                        if (manualSegmentMinutes !== null) {
                            segmentMinutes = manualSegmentMinutes;
                            segmentTimeSec = manualSegmentMinutes * 60;
                        } else {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري فحص معدل بت القناة لتقدير حجم الجزء بدقة (~${RECORD_TARGET_MB} MB)...`
                            }, { quoted: mek });

                            const bitrate = await probeStreamBitrate(streamUrl);
                            segmentTimeSec = computeSegmentTimeSec(bitrate);
                            segmentMinutes = Math.round(segmentTimeSec / 60);

                            bitrateNote = bitrate
                                ? `\n📊 معدل البت المُقاس: ~${(bitrate / 1000000).toFixed(2)} Mbps`
                                : `\n⚠️ تعذر قياس معدل البت، تم استخدام تقدير احتياطي (${RECORD_DEFAULT_SEGMENT_MIN} دقائق)`;
                        }

                        const segDir = path.join(tmpDir, `rec_iptv_${streamId}_${Date.now()}`);
                        fs.mkdirSync(segDir, { recursive: true });

                        await XeonBotInc.sendMessage(chatId, {
                            text: `🎙️ *بدأ تسجيل IPTV الثابت!*\n📺 القناة: ${channel.name}\n🆔 ID: \`${streamId}\`\n⏱️ المدة الكلية: *${duration} دقيقة*\n📦 كل جزء: *~${segmentMinutes} دقيقة* (تقدير لـ ~${RECORD_TARGET_MB} MB)${bitrateNote}\n🔗 اتصال واحد متواصل بالبث — بدون أي انقطاع بين الأجزاء\n\n🛑 لإلغاء التسجيل في أي وقت: \`.stoprecordiptv\``
                        }, { quoted: mek });

                        const control = { proc: null, cancelled: false };
                        activeIptvRecordings.set(chatId, control);

                        const MAX_RECONNECT_ATTEMPTS = 15;

                        (async () => {
                            let segmentIndex = 0;
                            let abortedBySize = false;
                            let wasCancelled = false;
                            let remainingSec = totalDurationSec;
                            let attempt = 0;
                            let reconnectedCount = 0;

                            const onSegmentReady = async (filePath) => {
                                segmentIndex++;
                                try {
                                    const sizeMB = (fs.statSync(filePath).size / 1024 / 1024).toFixed(2);
                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: filePath },
                                        mimetype: 'video/mp4',
                                        fileName: `IptvMatch_${streamId}_part${segmentIndex}.mp4`,
                                        caption: `📦 *الجزء ${segmentIndex}*\n📺 ${channel.name}\n⚖️ ${sizeMB} MB`
                                    }, { quoted: mek });
                                } catch (e) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `⚠️ فشل إرسال الجزء ${segmentIndex}: ${e.message}`
                                    }, { quoted: mek });
                                } finally {
                                    try { fs.unlinkSync(filePath); } catch (_) {}
                                }
                            };

                            try {
                                while (remainingSec > 60 && attempt < MAX_RECONNECT_ATTEMPTS && !control.cancelled) {
                                    attempt++;
                                    const startTs = Date.now();

                                    const result = await recordContinuousSegmented(
                                        streamUrl, segDir, `iptv_part_a${attempt}`, remainingSec, segmentTimeSec,
                                        onSegmentReady, control
                                    );

                                    const elapsedSec = Math.floor((Date.now() - startTs) / 1000);
                                    remainingSec -= elapsedSec;

                                    abortedBySize = result.abortedBySize;
                                    wasCancelled = result.cancelled;

                                    if (wasCancelled || abortedBySize) break;
                                    if (remainingSec <= 60) break;

                                    reconnectedCount++;
                                    const backoffMs = Math.min(3000 * Math.pow(2, Math.min(reconnectedCount - 1, 5)), 60000);
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `⚠️ *انقطع الاتصال بالبث بشكل غير متوقع.*\n⏱️ الوقت المتبقي: ~${Math.ceil(remainingSec / 60)} دقيقة\n🔄 جاري إعادة الاتصال بعد ${Math.round(backoffMs / 1000)} ثانية... (محاولة ${attempt + 1}/${MAX_RECONNECT_ATTEMPTS})`
                                    }, { quoted: mek });
                                    await new Promise(r => setTimeout(r, backoffMs));
                                }

                                if (!wasCancelled && !abortedBySize && attempt >= MAX_RECONNECT_ATTEMPTS && remainingSec > 60) {
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ تعذر إكمال التسجيل بعد ${MAX_RECONNECT_ATTEMPTS} محاولات إعادة اتصال. قد تكون القناة غير مستقرة حالياً.`
                                    }, { quoted: mek });
                                }
                            } catch (err) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ خطأ في التسجيل: ${err.message}`
                                }, { quoted: mek });
                            } finally {
                                activeIptvRecordings.delete(chatId);
                                try { fs.rmSync(segDir, { recursive: true, force: true }); } catch (_) {}
                            }

                            if (wasCancelled) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🛑 *تم إلغاء تسجيل IPTV الثابت بطلبك.*\n📦 عدد الأجزاء المُرسلة قبل الإلغاء: ${segmentIndex}`
                                }, { quoted: mek });
                            } else if (abortedBySize) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🛑 *تم إيقاف التسجيل مبكراً!*\nجودة البث كانت أعلى من المتوقع وتجاوز حجم أحد الأجزاء الحد الآمن للتخزين المتاح.\n📦 عدد الأجزاء المُرسلة قبل التوقف: ${segmentIndex}\n\n💡 جرّب تقليل مدة الجزء (مثال: \`.recordiptv ${streamId} ${duration} 3\`) للحصول على أجزاء أصغر تلائم جودة هذا البث.`
                                }, { quoted: mek });
                            } else {
                                const reconnectNote = reconnectedCount > 0 ? `\n🔄 حدثت ${reconnectedCount} إعادة اتصال بسبب انقطاعات مؤقتة في البث.` : '';
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `✅ *اكتمل التسجيل الكامل!*\n📺 القناة: ${channel.name}\n📦 عدد الأجزاء المُرسلة: ${segmentIndex}${reconnectNote}`
                                }, { quoted: mek });
                            }
                        })();
                        return;
                    }

                    // ── أمر .download (يدعم الروابط المباشرة و Google Drive تلقائياً) ──
                    if (command === '.download') {
                        if (!query || (!query.startsWith('http://') && !query.startsWith('https://'))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ الصيغة خاطئة!\n`.download [رابط مباشر أو رابط Google Drive]`'
                            }, { quoted: mek });
                            return;
                        }

                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        let result;
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚡ *بدأ التحميل...*`
                            }, { quoted: mek });

                            const _dlUrl = query.split(' ')[0];
                            const _dlStart = Date.now();
                            console.log(`[DOWNLOAD] start: ${_dlUrl}`);
                            result = await smartDownloadUrl(_dlUrl, tmpDir, 'File');
                            console.log(`[DOWNLOAD] done: ${result.sizeMB} MB | ${result.fileExt} | ${((Date.now() - _dlStart) / 1000).toFixed(1)}s`);

                            await XeonBotInc.sendMessage(chatId, {
                                document: { url: result.outputPath },
                                mimetype: result.mimeType,
                                fileName: `File${result.fileExt}`,
                                caption: `✅ *اكتمل التحميل!*\n⚖️ *الحجم:* ${result.sizeMB} MB${result.isGoogleDrive ? '\n☁️ المصدر: Google Drive' : ''}`
                            }, { quoted: mek });

                        } catch (err) {
                            console.log(`[DOWNLOAD] failed: ${err.message}`);
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل التحميل:\n\`${err.message}\`\n\n💡 إذا كان الخطأ 503/502: السيرفر مزدحم أو مطفأ مؤقتاً — جرّب بعد قليل أو تأكد أن الرابط يعمل في المتصفح.`
                            }, { quoted: mek });
                        } finally {
                            if (result?.outputPath && fs.existsSync(result.outputPath)) {
                                try { fs.unlinkSync(result.outputPath); } catch (_) {}
                            }
                        }
                        return;
                    }

                    // ── أمر .setremotedl (ضبط مستودع/رمز GitHub الخاص بالتحميل عن بُعد) ──
                    if (command === '.setremotedl') {
                        const partsArr = query.split(' ').filter(Boolean);
                        const [ownerRepo, token, workflowFile] = partsArr;

                        if (!ownerRepo || !ownerRepo.includes('/') || !token) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ الصيغة الصحيحة:\n`.setremotedl [owner/repo] [GitHub Token] [اسم ملف workflow - اختياري]`\n💡 مثال:\n`.setremotedl myuser/file-splitter ghp_xxx remote-download.yml`'
                            }, { quoted: mek });
                            return;
                        }

                        const [rdOwner, rdRepo] = ownerRepo.split('/');
                        const oldRemoteDlConfig = { ...REMOTE_DL_CONFIG };

                        try {
                            await axios.get(`https://api.github.com/repos/${rdOwner}/${rdRepo}`, {
                                headers: { Authorization: `Bearer ${token}`, 'User-Agent': 'KnightBot-RemoteDL' },
                                timeout: 15000
                            });

                            REMOTE_DL_CONFIG.owner = rdOwner;
                            REMOTE_DL_CONFIG.repo = rdRepo;
                            REMOTE_DL_CONFIG.token = token;
                            if (workflowFile) REMOTE_DL_CONFIG.workflowFile = workflowFile;
                            saveRemoteDlConfig();

                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ تم ضبط إعدادات Remote Downloader بنجاح!\n📁 المستودع: ${rdOwner}/${rdRepo}\n⚙️ ملف الـ workflow: ${REMOTE_DL_CONFIG.workflowFile}`
                            }, { quoted: mek });
                        } catch (e) {
                            Object.assign(REMOTE_DL_CONFIG, oldRemoteDlConfig);
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل التحقق من المستودع/الرمز:\n\`${e.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .remotedl (تحميل عن بُعد عبر GitHub Actions ثم إعادة إرسال الأجزاء) ──
                    // يدعم: إلغاء (.stopremotedl)، إعادة محاولة تلقائية لكل جزء فاشل، وتنظيف الـ Release بعد الانتهاء.
                    if (command === '.remotedl') {
                        if (!query || (!query.startsWith('http://') && !query.startsWith('https://'))) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ الصيغة الصحيحة:\n`.remotedl [رابط مباشر] [حجم الجزء بالميجا - اختياري]`'
                            }, { quoted: mek });
                            return;
                        }

                        if (activeRemoteDl.has(chatId)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚠️ يوجد تحميل عن بُعد نشط بالفعل في هذه المحادثة. أوقفه أولاً بأمر \`.stopremotedl\` قبل بدء تحميل جديد.`
                            }, { quoted: mek });
                            return;
                        }

                        const rdParts = query.split(' ').filter(Boolean);
                        const fileUrl = rdParts[0];
                        const chunkSizeMb = rdParts[1] && !isNaN(parseInt(rdParts[1])) ? parseInt(rdParts[1]) : 100;

                        const control = { cancelled: false, runId: null };
                        activeRemoteDl.set(chatId, control);

                        let dispatchTime, run, release, links;
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🚀 *جاري تشغيل التحميل عن بُعد على GitHub Actions...*\n📦 حجم الجزء: ${chunkSizeMb} MB\n\n🛑 لإلغاء التحميل في أي وقت: \`.stopremotedl\``
                            }, { quoted: mek });

                            console.log(`[REMOTEDL] start: ${fileUrl} | chunk:${chunkSizeMb}MB`);
                            dispatchTime = await triggerRemoteDownload(fileUrl, chunkSizeMb);
                            run = await findTriggeredRun(dispatchTime);
                            control.runId = run.id;

                            await XeonBotInc.sendMessage(chatId, {
                                text: `⏳ بدأ التشغيل بنجاح.\n🔗 السجل: ${run.html_url}\nجاري الانتظار حتى الاكتمال (قد يستغرق عدة دقائق حسب حجم الملف)...`
                            }, { quoted: mek });

                            const completedRun = await waitForRunCompletion(run.id, 55 * 60 * 1000, async (r) => {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `⏳ لا يزال التحميل عن بُعد قيد التشغيل...\n🔗 ${r.html_url}`
                                }, { quoted: mek });
                            }, control);

                            if (completedRun.conclusion !== 'success') {
                                throw new Error(`فشل تشغيل الـ workflow (${completedRun.conclusion}).\n🔗 راجع السجل: ${completedRun.html_url}`);
                            }

                            const result = await fetchRemoteDlResult();
                            release = result.release;
                            links = result.links;

                            await XeonBotInc.sendMessage(chatId, {
                                text: `✅ *اكتمل التحميل عن بُعد!*\n📦 عدد الأجزاء: ${links.length}\n⬇️ جاري تحميل الأجزاء وإرسالها...`
                            }, { quoted: mek });

                        } catch (err) {
                            activeRemoteDl.delete(chatId);
                            if (err.isCancelled) {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `🛑 *تم إلغاء التحميل عن بُعد بطلبك.*`
                                }, { quoted: mek });
                            } else {
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ فشل التحميل عن بُعد:\n\`${err.message}\``
                                }, { quoted: mek });
                            }
                            return;
                        }

                        // ── مرحلة تحميل وإرسال الأجزاء: مع إعادة محاولة تلقائية ودعم الإلغاء ──
                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        const PART_MAX_RETRIES = 3;      // عدد محاولات تحميل كل جزء قبل اعتباره فشل نهائياً
                        const PART_RETRY_BASE_MS = 4000; // أساس التأخير التصاعدي بين المحاولات

                        let successCount = 0, failCount = 0, wasCancelledMidway = false;
                        const failedParts = [];

                        for (let i = 0; i < links.length; i++) {
                            if (control.cancelled) {
                                wasCancelledMidway = true;
                                break;
                            }

                            let result, lastErr, succeeded = false;

                            for (let attempt = 1; attempt <= PART_MAX_RETRIES; attempt++) {
                                if (control.cancelled) { wasCancelledMidway = true; break; }
                                try {
                                    if (attempt > 1) {
                                        await XeonBotInc.sendMessage(chatId, {
                                            text: `🔁 إعادة محاولة تحميل الجزء ${i + 1}/${links.length} — المحاولة ${attempt}/${PART_MAX_RETRIES}...`
                                        }, { quoted: mek });
                                    }

                                    result = await smartDownloadUrl(links[i], tmpDir, `remote${i + 1}`);
                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: result.outputPath },
                                        mimetype: result.mimeType,
                                        fileName: `Part_${i + 1}${result.fileExt}`,
                                        caption: `✅ *الجزء ${i + 1}/${links.length}*\n⚖️ الحجم: ${result.sizeMB} MB${attempt > 1 ? `\n🔁 نجح بعد ${attempt} محاولات` : ''}`
                                    }, { quoted: mek });

                                    succeeded = true;
                                    break;
                                } catch (err) {
                                    lastErr = err;
                                    if (result?.outputPath && fs.existsSync(result.outputPath)) {
                                        try { fs.unlinkSync(result.outputPath); } catch (_) {}
                                    }
                                    if (attempt < PART_MAX_RETRIES) {
                                        const backoffMs = PART_RETRY_BASE_MS * attempt;
                                        await XeonBotInc.sendMessage(chatId, {
                                            text: `⚠️ فشلت المحاولة ${attempt}/${PART_MAX_RETRIES} للجزء ${i + 1}:\n\`${err.message}\`\n🔄 إعادة المحاولة بعد ${Math.round(backoffMs / 1000)} ثانية...`
                                        }, { quoted: mek });
                                        await new Promise(r => setTimeout(r, backoffMs));
                                    }
                                } finally {
                                    if (result?.outputPath && fs.existsSync(result.outputPath)) {
                                        try { fs.unlinkSync(result.outputPath); } catch (_) {}
                                    }
                                }
                            }

                            if (wasCancelledMidway) break;

                            if (succeeded) {
                                successCount++;
                            } else {
                                failCount++;
                                failedParts.push({ index: i + 1, url: links[i], error: lastErr?.message || 'خطأ غير معروف' });
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `❌ فشل تحميل/إرسال الجزء ${i + 1} نهائياً بعد ${PART_MAX_RETRIES} محاولات:\n\`${lastErr?.message || 'خطأ غير معروف'}\`\n🔗 الرابط المباشر: ${links[i]}`
                                }, { quoted: mek });
                            }

                            if (i < links.length - 1) await new Promise(r => setTimeout(r, 2000));
                        }

                        activeRemoteDl.delete(chatId);

                        if (wasCancelledMidway) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🛑 *تم إلغاء إرسال الأجزاء بطلبك.*\n✅ تم إرسال: ${successCount}/${links.length} قبل الإلغاء`
                            }, { quoted: mek });
                        } else {
                            let summaryText = `🏁 *اكتمل!*\n✅ نجح: ${successCount}\n❌ فشل: ${failCount}`;
                            if (failedParts.length > 0) {
                                summaryText += `\n\n📋 *الأجزاء التي فشلت نهائياً:*\n`;
                                failedParts.forEach(f => {
                                    summaryText += `${f.index}. \`${f.error}\`\n🔗 ${f.url}\n`;
                                });
                            }
                            await XeonBotInc.sendMessage(chatId, { text: summaryText }, { quoted: mek });
                        }

                        if (release) cleanupRemoteDlRelease(release).catch(() => {});
                        return;
                    }

                    // ── أمر .batchdl: تحميل عدة روابط دفعة واحدة من ملف txt مرفق (رابط لكل سطر) ──
                    // الاستخدام: أرسل ملف .txt واجعل التعليق عليه .batchdl (أو .batchdl Part لتحديد بادئة التسمية)
                    // أو أرسل .batchdl كرد (Reply) على ملف txt أرسلته سابقاً
                    // صيغة كل سطر داخل الملف: رابط | اسم مخصص  (أو رابط فقط وسيُسمّى تلقائياً)
                    if (command === '.batchdl') {
                        let docMessage = mek.message?.documentMessage;

                        if (!docMessage && isReply) {
                            const quoted = mek.message.extendedTextMessage.contextInfo.quotedMessage;
                            if (quoted?.documentMessage) docMessage = quoted.documentMessage;
                        }

                        if (!docMessage || !(docMessage.fileName || '').toLowerCase().endsWith('.txt')) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ أرفق ملف نصي (.txt) يحتوي على رابط في كل سطر، ثم استخدم `.batchdl` كتعليق على الملف أو كرد عليه.\n\n💡 صيغة كل سطر:\n`رابط | اسم مخصص`\nأو رابط فقط (سيُسمّى تلقائياً Part 1, Part 2 ...)\n\n📌 مثال: `.batchdl Part` لتحديد بادئة التسمية.'
                            }, { quoted: mek });
                            return;
                        }

                        // ── إعدادات إعادة المحاولة والفاصل الزمني ──
                        const BATCHDL_SLEEP_MS = 5000;      // فاصل 5 ثوانٍ بين كل رابط والذي يليه
                        const BATCHDL_MAX_RETRIES = 3;       // عدد محاولات التحميل لكل رابط قبل اعتباره فشل نهائياً
                        const BATCHDL_RETRY_BASE_MS = 4000;  // أساس التأخير بين المحاولات (تصاعدي)

                        try {
                            const stream = await downloadContentFromMessage(docMessage, 'document');
                            let buffer = Buffer.from([]);
                            for await (const chunk of stream) buffer = Buffer.concat([buffer, chunk]);

                            const lines = buffer.toString('utf8').split(/\r?\n/).map(l => l.trim()).filter(Boolean);
                            if (lines.length === 0) throw new Error('الملف فارغ.');

                            const namePrefix = query || 'Part';
                            const jobs = lines.map((line, i) => {
                                const [rawUrl, customName] = line.split('|').map(s => s?.trim());
                                return { url: rawUrl, name: customName || `${namePrefix} ${i + 1}` };
                            }).filter(j => /^https?:\/\//i.test(j.url));

                            if (jobs.length === 0) throw new Error('لم يتم العثور على أي روابط صحيحة في الملف.');

                            await XeonBotInc.sendMessage(chatId, {
                                text: `📦 *بدء التحميل المجمّع!*\n🔗 عدد الروابط: ${jobs.length}\n⏱️ فاصل ${BATCHDL_SLEEP_MS / 1000} ثوانٍ بين كل رابط\n🔁 حتى ${BATCHDL_MAX_RETRIES} محاولات لكل رابط عند الفشل\n⏳ سيتم إرسال كل ملف فور اكتمال تحميله...`
                            }, { quoted: mek });

                            const tmpDir = path.join(process.cwd(), 'dltmp');
                            if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                            let successCount = 0, failCount = 0;
                            const failedJobs = []; // لتقرير نهائي بالروابط التي فشلت بعد كل المحاولات

                            for (let i = 0; i < jobs.length; i++) {
                                const { url, name } = jobs[i];
                                let result;
                                let lastErr;
                                let succeeded = false;

                                // ── حلقة إعادة المحاولة لهذا الرابط ──
                                for (let attempt = 1; attempt <= BATCHDL_MAX_RETRIES; attempt++) {
                                    try {
                                        if (attempt === 1) {
                                            await XeonBotInc.sendMessage(chatId, {
                                                text: `⬇️ (${i + 1}/${jobs.length}) جاري تحميل: *${name}*...`
                                            }, { quoted: mek });
                                        } else {
                                            await XeonBotInc.sendMessage(chatId, {
                                                text: `🔁 (${i + 1}/${jobs.length}) إعادة محاولة تحميل *${name}* — المحاولة ${attempt}/${BATCHDL_MAX_RETRIES}...`
                                            }, { quoted: mek });
                                        }

                                        result = await smartDownloadUrl(url, tmpDir, `batch${i + 1}`);
                                        const cleanName = name.replace(/[^\w\s\u0600-\u06FF-]/g, '').trim() || `Part_${i + 1}`;

                                        await XeonBotInc.sendMessage(chatId, {
                                            document: { url: result.outputPath },
                                            mimetype: result.mimeType,
                                            fileName: `${cleanName}${result.fileExt}`,
                                            caption: `✅ *${name}*\n⚖️ الحجم: ${result.sizeMB} MB${result.isGoogleDrive ? '\n☁️ المصدر: Google Drive' : ''}${attempt > 1 ? `\n🔁 نجح بعد ${attempt} محاولات` : ''}`
                                        }, { quoted: mek });

                                        succeeded = true;
                                        break; // نجح التحميل، لا داعي لمزيد من المحاولات

                                    } catch (err) {
                                        lastErr = err;
                                        if (result?.outputPath && fs.existsSync(result.outputPath)) {
                                            try { fs.unlinkSync(result.outputPath); } catch (_) {}
                                        }

                                        if (attempt < BATCHDL_MAX_RETRIES) {
                                            // تأخير تصاعدي بسيط قبل إعادة المحاولة: 4، 8، 12 ثانية...
                                            const backoffMs = BATCHDL_RETRY_BASE_MS * attempt;
                                            await XeonBotInc.sendMessage(chatId, {
                                                text: `⚠️ فشلت المحاولة ${attempt}/${BATCHDL_MAX_RETRIES} لـ *${name}*:\n\`${err.message}\`\n🔄 إعادة المحاولة بعد ${Math.round(backoffMs / 1000)} ثانية...`
                                            }, { quoted: mek });
                                            await new Promise(r => setTimeout(r, backoffMs));
                                        }
                                    } finally {
                                        if (result?.outputPath && fs.existsSync(result.outputPath)) {
                                            try { fs.unlinkSync(result.outputPath); } catch (_) {}
                                        }
                                    }
                                }

                                if (succeeded) {
                                    successCount++;
                                } else {
                                    failCount++;
                                    failedJobs.push({ name, url, error: lastErr?.message || 'خطأ غير معروف' });
                                    await XeonBotInc.sendMessage(chatId, {
                                        text: `❌ فشل تحميل *${name}* نهائياً بعد ${BATCHDL_MAX_RETRIES} محاولات:\n\`${lastErr?.message || 'خطأ غير معروف'}\``
                                    }, { quoted: mek });
                                }

                                // ── فاصل sleep 5 ثوانٍ قبل الانتقال للرابط التالي (إن وُجد رابط آخر) ──
                                if (i < jobs.length - 1) {
                                    await new Promise(r => setTimeout(r, BATCHDL_SLEEP_MS));
                                }
                            }

                            let summaryText = `🏁 *اكتمل التحميل المجمّع!*\n✅ نجح: ${successCount}\n❌ فشل: ${failCount}`;
                            if (failedJobs.length > 0) {
                                summaryText += `\n\n📋 *الروابط التي فشلت نهائياً:*\n`;
                                failedJobs.forEach((f, idx) => {
                                    summaryText += `${idx + 1}. ${f.name} — \`${f.error}\`\n`;
                                });
                            }

                            await XeonBotInc.sendMessage(chatId, {
                                text: summaryText
                            }, { quoted: mek });

                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ خطأ في معالجة ملف الروابط:\n\`${err.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .apk ──
                    if (command === '.apk') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى إدخال اسم التطبيق.\nمثال: `.apk mt manager`'
                            }, { quoted: mek });
                            return;
                        }
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري البحث عن *${query}* في قاعدة البيانات...`
                            }, { quoted: mek });

                            const searchUrl = `https://ws75.aptoide.com/api/7/apps/search/query=${encodeURIComponent(query)}/limit=1`;
                            const searchResponse = await axios.get(searchUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } });
                            const appList = searchResponse.data?.datalist?.list;
                            if (!appList || appList.length === 0) throw new Error('لم يتم العثور على هذا التطبيق!');

                            const app = appList[0];
                            const apkUrl = app.file?.path;
                            const appName = app.name || query;
                            if (!apkUrl) throw new Error('رابط الحزمة المباشر غير متوفر حالياً.');

                            await XeonBotInc.sendMessage(chatId, {
                                text: `📦 *تم العثور على:* ${appName}\n🆔 *الحزمة:* ${app.package}\n\nجاري تحميل ملف الـ APK...`
                            }, { quoted: mek });

                            const tmpDir = path.join(process.cwd(), 'dltmp');
                            if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                            const cleanName = appName.replace(/[^\w\s-]/g, '').replace(/\s+/g, '_');
                            const outputPath = path.join(tmpDir, `${cleanName}_${randomBytes(2).toString('hex')}.apk`);

                            const response = await axios({
                                method: 'GET', url: apkUrl, responseType: 'stream',
                                timeout: 600000, headers: { 'User-Agent': 'Mozilla/5.0' }
                            });
                            const writer = fs.createWriteStream(outputPath);
                            trackStream(response.data, `APK ${cleanName}`, response.headers['content-length']);
                            response.data.pipe(writer);
                            await new Promise((resolve, reject) => { writer.on('finish', resolve); writer.on('error', reject); });

                            const sizeMB = (fs.statSync(outputPath).size / 1024 / 1024).toFixed(2);
                            await XeonBotInc.sendMessage(chatId, {
                                document: { url: outputPath },
                                mimetype: 'application/vnd.android.package-archive',
                                fileName: `${cleanName}.apk`,
                                caption: `🤖 *تم تحميل الـ APK بنجاح!*\n📱 *التطبيق:* ${appName}\n⚖ *الحجم:* ${sizeMB} MB`
                            }, { quoted: mek });

                            try { if (fs.existsSync(outputPath)) fs.unlinkSync(outputPath); } catch (_) {}
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ تعذر تحميل الـ APK:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .anime ──
                    if (command === '.anime') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى كتابة اسم الأنمي.\n💡 *مثال:* `.anime Naruto`'
                            }, { quoted: mek });
                            return;
                        }
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري البحث عن *${query}* في خادم الميديا...`
                            }, { quoted: mek });

                            const searchUrl = `http://103.155.92.42/search?query=${encodeURIComponent(query)}`;
                            const searchRes = await axios.get(searchUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } });
                            const htmlSearch = searchRes.data;

                            const regexLink = /href="https?:\/\/103\.155\.92\.42\/anime\/([^"]+)"/g;
                            let foundAnimes = [];
                            let match;
                            while ((match = regexLink.exec(htmlSearch)) !== null) {
                                if (!foundAnimes.includes(match[1])) foundAnimes.push(match[1]);
                            }
                            if (foundAnimes.length === 0) {
                                const regexFallback = /href="\/anime\/([^"]+)"/g;
                                while ((match = regexFallback.exec(htmlSearch)) !== null) {
                                    if (!foundAnimes.includes(match[1])) foundAnimes.push(match[1]);
                                }
                            }
                            if (foundAnimes.length === 0) throw new Error('لم يتم العثور على أي نتائج.');

                            let responseText = `🔍 *نتائج البحث:*\n\n`;
                            foundAnimes.slice(0, 15).forEach((anime, index) => {
                                responseText += `*_${index + 1}_* - ${anime.replace(/-/g, ' ')}\n`;
                            });
                            responseText += `\n💡 *طريقة الاختيار:*\nقم **بالرد (Reply)** على هذه الرسالة واكتب:\n[رقم الأنمي] [رقم الحلقة]\n\n🍿 *مثال:* \`1 12\` أو \`2 5\``;

                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: responseText }, { quoted: mek });
                            animeCache.set(sentMsg.key.id, {
                                results: foundAnimes.slice(0, 15),
                                timestamp: Date.now()
                            });
                            setTimeout(() => animeCache.delete(sentMsg.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل البحث:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .series (akwam.it) ──
                    if (command === '.series') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى كتابة اسم المسلسل.\n💡 *مثال:* `.series breaking bad`\nأو: `.series مسلسل عربي`'
                            }, { quoted: mek });
                            return;
                        }
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري البحث عن *${query}* في akwam.it...`
                            }, { quoted: mek });

                            const html = await akwamFetch(`https://akwam.it/search?q=${encodeURIComponent(query)}`);
                            const results = extractAkwamSeries(html);

                            if (results.length === 0) throw new Error('لم يتم العثور على مسلسلات مطابقة. جرّب اسماً مختلفاً.');

                            let resText = `📺 *نتائج البحث في akwam.it:*\n\n`;
                            results.slice(0, 12).forEach((s, i) => {
                                resText += `*${i + 1}* - ${s.name}\n`;
                            });
                            resText += `\n💡 **رد (Reply)** على هذه الرسالة برقم المسلسل المطلوب.`;

                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: resText }, { quoted: mek });
                            akwamCache.set(sentMsg.key.id, {
                                stage: 'series_list',
                                results: results.slice(0, 12),
                                timestamp: Date.now()
                            });
                            setTimeout(() => akwamCache.delete(sentMsg.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل البحث:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .manga (3asq.online) ──
                    if (command === '.manga') {
                        if (!query) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى كتابة اسم المانجا.\n💡 *مثال:* `.manga naruto`\nأو: `.manga بلاك كلوفر`'
                            }, { quoted: mek });
                            return;
                        }
                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري البحث عن *${query}* في 3asq.org...`
                            }, { quoted: mek });

                            const searchSlug = query.trim().replace(/\s+/g, '+');
                            const searchRes  = await axios.get(
                                `https://3asq.online/?s=${encodeURIComponent(searchSlug)}&post_type=wp-manga`,
                                { headers: { 'User-Agent': 'Mozilla/5.0' }, timeout: 15000 }
                            );

                            const titleRegex = /<h3[^>]*class="[^"]*h4[^"]*"[^>]*>\s*<a[^>]*href="([^"]+)"[^>]*>([^<]+)<\/a>/gi;
                            const results = [];
                            let m;
                            while ((m = titleRegex.exec(searchRes.data)) !== null) {
                                const url  = m[1].trim();
                                const name = m[2].trim();
                                if (!results.some(r => r.url === url)) {
                                    results.push({ url, name });
                                }
                            }

                            if (results.length === 0) throw new Error('لم يتم العثور على نتائج. جرّب اسماً مختلفاً.');

                            let resText = `📚 *نتائج البحث في 3asq.org:*\n\n`;
                            results.slice(0, 12).forEach((r, i) => {
                                resText += `*${i + 1}* - ${r.name}\n`;
                            });
                            resText += `\n💡 **رد (Reply)** برقم المانجا المطلوبة.`;

                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: resText }, { quoted: mek });
                            mangaCache.set(sentMsg.key.id, {
                                stage: 'manga_list',
                                results: results.slice(0, 12),
                                timestamp: Date.now()
                            });
                            setTimeout(() => mangaCache.delete(sentMsg.key.id), 300000);
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, { text: `❌ فشل البحث:\n\`${err.message}\`` }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .okru (تحميل فيديو من ok.ru وإرساله) ──
                    if (command === '.okru') {
                        if (!query || !/ok\.ru\//i.test(query)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى إرسال رابط فيديو صحيح من ok.ru\n💡 *مثال:* `.okru https://ok.ru/video/123456789`'
                            }, { quoted: mek });
                            return;
                        }

                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `🔍 جاري استخراج رابط الفيديو من ok.ru...`
                            }, { quoted: mek });

                            const pageUrl = query.trim();
                            const headers = {
                                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
                                'Accept-Language': 'en-US,en;q=0.9'
                            };

                            const pageRes = await axios.get(pageUrl, { headers, timeout: 15000 });
                            const html = pageRes.data;

                            // ok.ru يضع بيانات الفيديو داخل خاصية data-options كـ JSON مُشفّر بـ HTML entities
                            const optionsMatch = html.match(/data-options="([^"]+)"/);
                            if (!optionsMatch) {
                                throw new Error('لم يتم العثور على بيانات الفيديو (قد يكون خاصاً أو محذوفاً أو الرابط غير صحيح).');
                            }

                            const decodedOptions = optionsMatch[1]
                                .replace(/&quot;/g, '"')
                                .replace(/&amp;/g, '&')
                                .replace(/&#x2F;/g, '/');

                            let options;
                            try {
                                options = JSON.parse(decodedOptions);
                            } catch (e) {
                                throw new Error('فشل تحليل بيانات الفيديو (بنية غير متوقعة، ربما تغيّر تصميم الموقع).');
                            }

                            const metadataRaw = options?.flashvars?.metadata;
                            if (!metadataRaw) throw new Error('لم يتم العثور على معلومات الفيديو (metadata).');

                            const metadata = typeof metadataRaw === 'string' ? JSON.parse(metadataRaw) : metadataRaw;
                            const videos = metadata?.videos || [];
                            if (videos.length === 0) throw new Error('لا توجد روابط فيديو متاحة (ربما الفيديو محمي أو يتطلب تسجيل دخول).');

                            // ترتيب الجودات من الأعلى للأقل واختيار أفضل جودة متاحة
                            const qualityOrder = ['ultra', 'quad', 'full', 'hd', 'sd', 'low', 'lowest', 'mobile'];
                            videos.sort((a, b) => {
                                const ai = qualityOrder.indexOf(a.name);
                                const bi = qualityOrder.indexOf(b.name);
                                return (ai === -1 ? 999 : ai) - (bi === -1 ? 999 : bi);
                            });

                            const title = metadata?.movie?.title || 'ok.ru video';

                            // أسماء عرض مفهومة للجودات
                            const qualityLabels = {
                                ultra: '2160p (Ultra HD)',
                                quad: '1440p (Quad HD)',
                                full: '1080p (Full HD)',
                                hd: '720p (HD)',
                                sd: '480p (SD)',
                                low: '360p',
                                lowest: '240p',
                                mobile: '144p (Mobile)'
                            };

                            let listText = `🎬 *${title}*\n\n📺 *اختر الجودة المطلوبة (رد بالرقم):*\n\n`;
                            videos.forEach((v, i) => {
                                listText += `*${i + 1}* - ${qualityLabels[v.name] || v.name || 'غير معروفة'}\n`;
                            });
                            listText += `\n💡 **رد (Reply)** على هذه الرسالة برقم الجودة.`;

                            const sentMsg = await XeonBotInc.sendMessage(chatId, { text: listText }, { quoted: mek });
                            okruCache.set(sentMsg.key.id, {
                                title,
                                videos,
                                timestamp: Date.now()
                            });
                            setTimeout(() => okruCache.delete(sentMsg.key.id), 300000);

                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل استخراج روابط الفيديو من ok.ru:\n\`${err.message}\``
                            }, { quoted: mek });
                        }
                        return;
                    }

                    // ── أمر .m3u8 (تحميل فيديو من رابط m3u8/HLS وإرساله - بأجزاء إن تجاوز الحجم) ──
                    if (command === '.m3u8' || command === '.hls') {
                        if (!query || !/^https?:\/\//i.test(query)) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: '❌ يرجى إرسال رابط m3u8 صحيح\n💡 *مثال:* `.m3u8 https://example.com/playlist.m3u8`\n💡 *مع Referer مخصص (لو ظهر خطأ 403):* `.m3u8 https://example.com/playlist.m3u8 https://example.com`'
                            }, { quoted: mek });
                            return;
                        }

                        // args[1] = الرابط، args[2] (اختياري) = Referer مخصص لتفادي حظر 403
                        const m3u8Url = args[1];
                        const customReferer = args[2] && /^https?:\/\//i.test(args[2]) ? args[2] : null;
                        let refererToUse = customReferer;
                        if (!refererToUse) {
                            try { refererToUse = new URL(m3u8Url).origin + '/'; } catch (_) { refererToUse = null; }
                        }
                        const HLS_USER_AGENT = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';
                        const tmpDir = path.join(process.cwd(), 'dltmp');
                        if (!fs.existsSync(tmpDir)) fs.mkdirSync(tmpDir, { recursive: true });

                        const fileId = randomBytes(4).toString('hex');
                        const outputPath = path.join(tmpDir, `M3U8_${fileId}.mp4`);
                        const segDir = path.join(tmpDir, `m3u8_${fileId}_parts`);

                        try {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `⚡ *جاري تحميل فيديو m3u8...*\nقد يستغرق هذا بعض الوقت حسب طول الفيديو وسرعة السيرفر.`
                            }, { quoted: mek });

                            // تحميل ودمج الفيديو من رابط m3u8 (فيديو كامل VOD وليس بثاً مباشراً - بدون إعادة ترميز)
                            await new Promise((resolve, reject) => {
                                const args = ['-y'];
                                if (refererToUse) {
                                    args.push('-headers', `Referer: ${refererToUse}\r\nOrigin: ${refererToUse}\r\n`);
                                }
                                args.push(
                                    '-user_agent', HLS_USER_AGENT,
                                    '-reconnect', '1',
                                    '-reconnect_streamed', '1',
                                    '-reconnect_delay_max', '5',
                                    '-i', m3u8Url,
                                    '-c', 'copy',
                                    '-bsf:a', 'aac_adtstoasc',
                                    outputPath
                                );
                                const proc = spawn('ffmpeg', args);
                                let stderr = '';
                                proc.stderr.on('data', (d) => { stderr += d.toString(); });
                                proc.on('close', (code) => {
                                    if (code === 0 && fs.existsSync(outputPath)) resolve();
                                    else reject(new Error(`فشل تحميل الفيديو (ffmpeg code ${code}):\n${stderr.slice(-500)}`));
                                });
                                proc.on('error', reject);
                            });

                            const totalBytes = fs.statSync(outputPath).size;

                            if (totalBytes <= MAX_DOWNLOAD_BYTES) {
                                // الحجم ضمن الحد المسموح - إرسال كملف واحد
                                const sizeMB = (totalBytes / 1024 / 1024).toFixed(2);
                                await XeonBotInc.sendMessage(chatId, {
                                    document: { url: outputPath },
                                    mimetype: 'video/mp4',
                                    fileName: `Video_${fileId}.mp4`,
                                    caption: `✅ *اكتمل تحميل الفيديو!*\n⚖️ *الحجم:* ${sizeMB} MB`
                                }, { quoted: mek });
                            } else {
                                // الحجم أكبر من 200 ميجا - يتم تقسيمه لأجزاء وإرسالها مثل التسجيل
                                await XeonBotInc.sendMessage(chatId, {
                                    text: `📦 حجم الفيديو *${(totalBytes / 1024 / 1024).toFixed(1)} MB* أكبر من ${MAX_DOWNLOAD_MB} MB — جاري تقسيمه وإرساله كأجزاء...`
                                }, { quoted: mek });

                                fs.mkdirSync(segDir, { recursive: true });

                                // فحص مدة الفيديو لحساب معدل البت الفعلي وبالتالي مدة كل جزء (~100 ميجا للجزء)
                                const durationSec = await new Promise((resolve) => {
                                    const p = spawn('ffprobe', [
                                        '-v', 'quiet', '-print_format', 'json', '-show_format', outputPath
                                    ]);
                                    let out = '';
                                    p.stdout.on('data', (d) => { out += d.toString(); });
                                    p.on('close', () => {
                                        try {
                                            const data = JSON.parse(out);
                                            const dur = parseFloat(data?.format?.duration);
                                            resolve(dur && dur > 0 ? dur : null);
                                        } catch (_) { resolve(null); }
                                    });
                                    p.on('error', () => resolve(null));
                                });

                                const bitrateBps = durationSec ? (totalBytes * 8) / durationSec : null;
                                const segmentTimeSec = computeSegmentTimeSec(bitrateBps);

                                const pattern = path.join(segDir, `part_%03d.mp4`);
                                await new Promise((resolve, reject) => {
                                    const args = [
                                        '-y', '-i', outputPath,
                                        '-c', 'copy',
                                        '-f', 'segment',
                                        '-segment_time', String(segmentTimeSec),
                                        '-reset_timestamps', '1',
                                        pattern
                                    ];
                                    const proc = spawn('ffmpeg', args);
                                    let stderr = '';
                                    proc.stderr.on('data', (d) => { stderr += d.toString(); });
                                    proc.on('close', (code) => {
                                        if (code === 0) resolve();
                                        else reject(new Error(`فشل تقسيم الفيديو (ffmpeg code ${code}):\n${stderr.slice(-500)}`));
                                    });
                                    proc.on('error', reject);
                                });

                                const parts = fs.readdirSync(segDir)
                                    .filter(f => f.startsWith('part_') && f.endsWith('.mp4'))
                                    .sort();
                                if (parts.length === 0) throw new Error('فشل إنشاء أجزاء الفيديو.');

                                for (let i = 0; i < parts.length; i++) {
                                    const partPath = path.join(segDir, parts[i]);
                                    const partSizeMB = (fs.statSync(partPath).size / 1024 / 1024).toFixed(2);
                                    await XeonBotInc.sendMessage(chatId, {
                                        document: { url: partPath },
                                        mimetype: 'video/mp4',
                                        fileName: `Video_${fileId}_part${i + 1}.mp4`,
                                        caption: `📦 *الجزء ${i + 1}/${parts.length}*\n⚖️ ${partSizeMB} MB`
                                    }, { quoted: mek });
                                    try { fs.unlinkSync(partPath); } catch (_) {}
                                }

                                await XeonBotInc.sendMessage(chatId, {
                                    text: `✅ *اكتمل إرسال الفيديو بالكامل!*\n📦 عدد الأجزاء: ${parts.length}`
                                }, { quoted: mek });
                            }
                        } catch (err) {
                            await XeonBotInc.sendMessage(chatId, {
                                text: `❌ فشل تحميل/إرسال فيديو m3u8:\n\`${err.message}\``
                            }, { quoted: mek });
                        } finally {
                            if (fs.existsSync(outputPath)) {
                                try { fs.unlinkSync(outputPath); } catch (_) {}
                            }
                            if (fs.existsSync(segDir)) {
                                try { fs.rmSync(segDir, { recursive: true, force: true }); } catch (_) {}
                            }
                        }
                        return;
                    }
                }

                // ============================================================
                // باقي معالجات البوت الأصلية
                // ============================================================
                if (mek.key && mek.key.remoteJid === 'status@broadcast') {
                    await handleStatus(XeonBotInc, chatUpdate);
                    return;
                }
                if (!XeonBotInc.public && !mek.key.fromMe && chatUpdate.type === 'notify') {
                    const isGroup = mek.key?.remoteJid?.endsWith('@g.us')
                    if (!isGroup) return
                }
                if (mek.key.id.startsWith('BAE5') && mek.key.id.length === 16) return

                if (XeonBotInc?.msgRetryCounterCache) {
                    XeonBotInc.msgRetryCounterCache.clear()
                }

                try {
                    await handleMessages(XeonBotInc, chatUpdate, true)
                } catch (err) {
                    console.error("Error in handleMessages:", err)
                }

            } catch (err) {
                console.error("Error in messages.upsert:", err)
            }
        })

        XeonBotInc.decodeJid = (jid) => {
            if (!jid) return jid
            if (/:\d+@/gi.test(jid)) {
                let decode = jidDecode(jid) || {}
                return decode.user && decode.server && decode.user + '@' + decode.server || jid
            } else return jid
        }

        XeonBotInc.ev.on('connection.update', async (s) => {
            const { connection, lastDisconnect, qr } = s
            if (qr) console.log(chalk.yellow('📱 QR Code generated.'))
            if (connection == "open") {
                console.log(chalk.green(`🤖 Bot Connected Successfully! ✅`));
            }
            if (connection === 'close') {
                const shouldReconnect = (lastDisconnect?.error)?.output?.statusCode !== DisconnectReason.loggedOut
                if (shouldReconnect) {
                    await delay(5000)
                    startXeonBotInc()
                }
            }
        })

        return XeonBotInc
    } catch (error) {
        console.error('Error in startXeonBotInc:', error)
        await delay(5000)
        startXeonBotInc()
    }
}

startXeonBotInc().catch(error => {
    process.exit(1)
})

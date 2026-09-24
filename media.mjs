// Camera, recording and transcription helpers.
// Recordings (audio/video) stay on this device: they live in a separate IndexedDB database and are
// never sent to the cloud. Pages only carry a reference (mediaId), so a page synced to another device
// shows "not on this device" for the recording. Photos are ordinary image blocks (they do sync).
const DB_NAME='yohaku-media-v1';
function openMediaDb(){return new Promise((resolve,reject)=>{
 const r=indexedDB.open(DB_NAME,1);r.onupgradeneeded=()=>r.result.createObjectStore('media');
 r.onsuccess=()=>resolve(r.result);r.onerror=()=>reject(r.error);
});}
const req=(store,fn)=>new Promise((resolve,reject)=>{const r=fn(store);r.onsuccess=()=>resolve(r.result);r.onerror=()=>reject(r.error);});
async function withStore(mode,fn){const db=await openMediaDb();try{const tx=db.transaction('media',mode);const out=await fn(tx.objectStore('media'));await new Promise((res,rej)=>{tx.oncomplete=res;tx.onerror=()=>rej(tx.error);tx.onabort=()=>rej(tx.error);});return out;}finally{db.close();}}
export const putMedia=(id,record)=>withStore('readwrite',s=>req(s,x=>x.put(record,id)));
export const getMedia=id=>withStore('readonly',s=>req(s,x=>x.get(id)));
export const deleteMedia=id=>withStore('readwrite',s=>req(s,x=>x.delete(id)));
export const listMediaIds=()=>withStore('readonly',s=>req(s,x=>x.getAllKeys()));
export async function mediaUsage(){const ids=await listMediaIds();let bytes=0;for(const id of ids){const r=await getMedia(id);bytes+=r?.blob?.size||0;}return {count:ids.length,bytes};}

// ---- camera / recorder ----
export function stopStream(stream){for(const t of stream?.getTracks?.()||[])t.stop();}
export async function openCamera(facing='environment',withAudio=false){
 const video={width:{ideal:1920},height:{ideal:1080},facingMode:facing};
 try{return await navigator.mediaDevices.getUserMedia({video,audio:withAudio});}
 catch(e){ // some laptops have one camera only: retry without the facing constraint
  if(e.name==='OverconstrainedError'||e.name==='NotFoundError')return navigator.mediaDevices.getUserMedia({video:true,audio:withAudio});
  throw e;
 }
}
// A still from the preview element, scaled so the long edge is at most `maxEdge`, as a JPEG file.
export function takePhoto(video,maxEdge=1600,quality=.86){
 const vw=video.videoWidth||1280,vh=video.videoHeight||720,k=Math.min(1,maxEdge/Math.max(vw,vh));
 const c=document.createElement('canvas');c.width=Math.round(vw*k);c.height=Math.round(vh*k);
 c.getContext('2d').drawImage(video,0,0,c.width,c.height);
 return new Promise(resolve=>c.toBlob(b=>resolve(new File([b],'camera-'+stamp()+'.jpg',{type:'image/jpeg'})),'image/jpeg',quality));
}
export function pickMimeType(kind){
 const list=kind==='video'?['video/webm;codecs=vp9,opus','video/webm;codecs=vp8,opus','video/webm','video/mp4']:['audio/webm;codecs=opus','audio/webm','audio/mp4','audio/ogg;codecs=opus'];
 return list.find(t=>typeof MediaRecorder!=='undefined'&&MediaRecorder.isTypeSupported(t))||'';
}
export function makeRecorder(stream,kind){
 const mimeType=pickMimeType(kind);
 const opts=mimeType?{mimeType}:{};
 if(kind==='audio')opts.audioBitsPerSecond=48000;else{opts.videoBitsPerSecond=2500000;opts.audioBitsPerSecond=64000;}
 return new MediaRecorder(stream,opts);
}
export const stamp=(d=new Date())=>d.getFullYear()+String(d.getMonth()+1).padStart(2,'0')+String(d.getDate()).padStart(2,'0')+'-'+String(d.getHours()).padStart(2,'0')+String(d.getMinutes()).padStart(2,'0')+String(d.getSeconds()).padStart(2,'0');
export const fmtTime=s=>{s=Math.max(0,Math.round(s));const h=Math.floor(s/3600),m=Math.floor(s%3600/60),x=s%60;return (h?h+':':'')+String(m).padStart(h?2:1,'0')+':'+String(x).padStart(2,'0');};
export const extOf=type=>/mp4/.test(type)?(type.startsWith('audio')?'m4a':'mp4'):/ogg/.test(type)?'ogg':/wav/.test(type)?'wav':/mpeg|mp3/.test(type)?'mp3':'webm';

// ---- transcription: decode → 16 kHz mono → ≤10-minute WAV parts → speech-to-text API ----
export function encodeWav(samples,rate){ // 16-bit PCM mono
 const buf=new ArrayBuffer(44+samples.length*2),v=new DataView(buf);
 const str=(o,s)=>{for(let i=0;i<s.length;i++)v.setUint8(o+i,s.charCodeAt(i));};
 str(0,'RIFF');v.setUint32(4,36+samples.length*2,true);str(8,'WAVE');str(12,'fmt ');v.setUint32(16,16,true);v.setUint16(20,1,true);v.setUint16(22,1,true);
 v.setUint32(24,rate,true);v.setUint32(28,rate*2,true);v.setUint16(32,2,true);v.setUint16(34,16,true);str(36,'data');v.setUint32(40,samples.length*2,true);
 let o=44;for(let i=0;i<samples.length;i++,o+=2){const x=Math.max(-1,Math.min(1,samples[i]));v.setInt16(o,x<0?x*32768:x*32767,true);}
 return new Blob([buf],{type:'audio/wav'});
}
export function splitSamples(samples,rate,seconds=600){
 const n=Math.max(1,Math.round(rate*seconds)),out=[];
 for(let i=0;i<samples.length;i+=n)out.push(samples.subarray(i,Math.min(samples.length,i+n)));
 return out.length?out:[samples];
}
export async function decodeToMono16k(blob,rate=16000){
 const buf=await blob.arrayBuffer();
 const AC=window.AudioContext||window.webkitAudioContext,OAC=window.OfflineAudioContext||window.webkitOfflineAudioContext;
 const ctx=new AC();let audio;
 try{audio=await ctx.decodeAudioData(buf);}finally{try{await ctx.close();}catch{}}
 const len=Math.max(1,Math.ceil(audio.duration*rate)),off=new OAC(1,len,rate);
 const src=off.createBufferSource();src.buffer=audio;src.connect(off.destination);src.start();
 const out=await off.startRendering();
 return {samples:out.getChannelData(0),rate,duration:audio.duration};
}
export const TRANSCRIBE_MODELS=[['gpt-4o-mini-transcribe','標準（安い・速い）'],['gpt-4o-transcribe','高精度'],['whisper-1','Whisper（従来）']];
export async function transcribeBlob(blob,{apiKey,model='gpt-4o-mini-transcribe',language='ja',onProgress=()=>{},fetchImpl=(...a)=>fetch(...a),chunkSeconds=600}={}){
 if(!apiKey)throw new Error('API キーがありません。');
 const {samples,rate}=await decodeToMono16k(blob);
 const parts=splitSamples(samples,rate,chunkSeconds),texts=[];
 for(let i=0;i<parts.length;i++){
  onProgress(i+1,parts.length);
  const fd=new FormData();fd.append('file',new File([encodeWav(parts[i],rate)],'part'+(i+1)+'.wav',{type:'audio/wav'}));
  fd.append('model',model);fd.append('language',language);fd.append('response_format','json');
  const r=await fetchImpl('https://api.openai.com/v1/audio/transcriptions',{method:'POST',headers:{Authorization:'Bearer '+apiKey},body:fd});
  if(!r.ok){const t=await r.text().catch(()=>'');throw new Error('文字起こしサービスの応答 '+r.status+(t?'：'+t.slice(0,160):''));}
  const j=await r.json();texts.push(String(j.text||'').trim());
 }
 return texts.filter(Boolean).join('\n');
}

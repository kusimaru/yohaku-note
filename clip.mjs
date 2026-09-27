// 余白ノート・日記カレンダーで共通のクリップボード形式 (kusimaru-clip v1)。
// 日記カレンダーの src/lib/clip.ts と同じ形式。片方を直したらもう片方も合わせる。
// コピーするとき text/html の data 属性に JSON (UTF-8 → base64) を埋め込み、同時に text/plain も入れる。
// 対応していないアプリには普通の文章として貼られる。
// 座標は選んだ範囲の左上を (0,0) とした相対値。unit はコピー元のページ幅 (余白ノート 1200 / 日記 1000)。
// 線の width は unit 基準の太さ (余白ノートの width と同じ意味)。
export const CLIP_ATTR='data-kusimaru-clip';
const HEX=/^#[0-9a-f]{6}$/i,IMG=/^data:image\/(png|jpeg|webp);base64,[A-Za-z0-9+/=]+$/;
const MAX_STROKES=20000,MAX_POINTS=2000000,MAX_TEXT=200000,MAX_IMAGE=16000000;
const fin=v=>typeof v==='number'&&Number.isFinite(v);
const clampNum=(v,lo,hi)=>Math.max(lo,Math.min(hi,v));

function toBase64(str) {
 const bytes=new TextEncoder().encode(str);let s='';
 for(let i=0;i<bytes.length;i+=8192)s+=String.fromCharCode(...bytes.subarray(i,i+8192));
 return btoa(s);
}
function fromBase64(b64) {
 const s=atob(b64),bytes=new Uint8Array(s.length);
 for(let i=0;i<s.length;i++)bytes[i]=s.charCodeAt(i);
 return new TextDecoder().decode(bytes);
}
const escapeHtml=s=>s.replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));

// 文章だけを取り出す (text/plain 用)。上から順に並べる
export function clipText(clip) {
 return [...clip.texts].sort((a,b)=>a.y-b.y||a.x-b.x).map(t=>t.text).filter(Boolean).join('\n\n');
}
// {from, unit, texts, images, strokes} (座標はページ上の絶対値) から、左上を (0,0) にそろえたクリップを作る
export function makeClip({from,unit,texts=[],images=[],strokes=[]}) {
 let x0=Infinity,y0=Infinity,x1=-Infinity,y1=-Infinity;
 const add=(ax,ay,bx,by)=>{x0=Math.min(x0,ax);y0=Math.min(y0,ay);x1=Math.max(x1,bx);y1=Math.max(y1,by);};
 for(const b of [...texts,...images])add(b.x,b.y,b.x+b.width,b.y+b.height);
 for(const s of strokes)for(const p of s.points)add(p[0]-s.width/2,p[1]-s.width/2,p[0]+s.width/2,p[1]+s.width/2);
 if(x0===Infinity)return null;
 x0=Math.max(0,x0);y0=Math.max(0,y0);
 const box=b=>({x:b.x-x0,y:b.y-y0,width:b.width,height:b.height});
 return {
  kclip:1,from,unit,origin:{x:x0,y:y0},width:x1-x0,height:y1-y0,
  texts:texts.map(t=>({...box(t),text:t.text,...(t.runs?{runs:t.runs}:{})})),
  images:images.map(im=>({...box(im),src:im.src,name:im.name||'image'})),
  strokes:strokes.map(s=>({points:s.points.map(p=>[p[0]-x0,p[1]-y0,p[2]]),color:s.color,width:s.width,pressure:!!s.pressure})),
 };
}
export function encodeClip(clip) {
 const text=clipText(clip);
 const html='<meta charset="utf-8"><div '+CLIP_ATTR+'="'+toBase64(JSON.stringify(clip))+'">'+escapeHtml(text).replace(/\n/g,'<br>')+'</div>';
 return {text,html};
}
// text/html から取り出す。形式が違う・壊れているときは null
export function decodeClip(html) {
 if(!html)return null;
 const m=html.match(/data-kusimaru-clip="([A-Za-z0-9+/=]+)"/);if(!m)return null;
 try{return sanitizeClip(JSON.parse(fromBase64(m[1])));}catch{return null;}
}
// 他のアプリから来たデータなので、形と値の範囲を確かめて作り直す
export function sanitizeClip(c) {
 if(!c||typeof c!=='object'||c.kclip!==1||!fin(c.unit)||c.unit<100||c.unit>10000)return null;
 const box=b=>b&&[b.x,b.y,b.width,b.height].every(fin)&&b.width>0&&b.height>0?{x:Math.max(0,b.x),y:Math.max(0,b.y),width:b.width,height:b.height}:null;
 const texts=[],images=[],strokes=[];let chars=0,points=0;
 for(const t of Array.isArray(c.texts)?c.texts:[]){
  const b=box(t);if(!b||typeof t.text!=='string')continue;
  chars+=t.text.length;if(chars>MAX_TEXT)break;
  const text={...b,text:t.text};
  if(Array.isArray(t.runs))text.runs=t.runs.filter(r=>r&&typeof r==='object'&&(r.hr===true||typeof r.text==='string')).map(r=>r.hr===true?{hr:true}:{text:r.text,...(r.bold===true?{bold:true}:{}),...(fin(r.size)?{size:r.size}:{}),...(typeof r.color==='string'&&HEX.test(r.color)?{color:r.color.toLowerCase()}:{})});
  texts.push(text);
 }
 for(const im of Array.isArray(c.images)?c.images:[]){
  const b=box(im);if(!b||typeof im.src!=='string'||im.src.length>MAX_IMAGE||!IMG.test(im.src))continue;
  images.push({...b,src:im.src,name:typeof im.name==='string'?im.name.slice(0,100):'image'});
 }
 for(const s of Array.isArray(c.strokes)?c.strokes:[]){
  if(strokes.length>=MAX_STROKES)break;
  if(!s||typeof s.color!=='string'||!HEX.test(s.color)||!fin(s.width)||!Array.isArray(s.points))continue;
  const pts=s.points.filter(p=>Array.isArray(p)&&fin(p[0])&&fin(p[1])).map(p=>[Math.max(0,p[0]),Math.max(0,p[1]),fin(p[2])?clampNum(p[2],0,1):.5]);
  if(!pts.length)continue;
  points+=pts.length;if(points>MAX_POINTS)break;
  strokes.push({points:pts,color:s.color.toLowerCase(),width:clampNum(s.width,.1,200),pressure:s.pressure===true});
 }
 if(!texts.length&&!images.length&&!strokes.length)return null;
 const origin=c.origin&&fin(c.origin.x)&&fin(c.origin.y)?{x:Math.max(0,c.origin.x),y:Math.max(0,c.origin.y)}:{x:0,y:0};
 let width=0,height=0;
 for(const b of [...texts,...images]){width=Math.max(width,b.x+b.width);height=Math.max(height,b.y+b.height);}
 for(const s of strokes)for(const p of s.points){width=Math.max(width,p[0]+s.width/2);height=Math.max(height,p[1]+s.width/2);}
 return {kclip:1,from:typeof c.from==='string'?c.from.slice(0,40):'',unit:c.unit,origin,width,height,texts,images,strokes};
}
// 貼り付け先のページ幅 unit に合わせて拡大縮小し、(x, y) を左上にして絶対座標へ
export function placeClip(clip,unit,x,y) {
 const k=unit/clip.unit;
 const box=b=>({x:x+b.x*k,y:y+b.y*k,width:b.width*k,height:b.height*k});
 return {
  scale:k,width:clip.width*k,height:clip.height*k,
  texts:clip.texts.map(t=>({...box(t),text:t.text,...(t.runs?{runs:t.runs}:{})})),
  images:clip.images.map(im=>({...box(im),src:im.src,name:im.name})),
  strokes:clip.strokes.map(s=>({points:s.points.map(p=>[x+p[0]*k,y+p[1]*k,p[2]]),color:s.color,width:s.width*k,pressure:s.pressure})),
 };
}

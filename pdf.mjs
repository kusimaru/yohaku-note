// PDF helpers. pdf.js (vendor/pdfjs, Mozilla, Apache-2.0) is loaded only when a PDF is used, so the
// app itself starts as before. Everything happens on this device: the PDF is never sent anywhere.
const BASE=new URL('./vendor/pdfjs/',import.meta.url).href;
let lib=null;
export async function loadPdfjs(){
 if(lib)return lib;
 const m=await import(BASE+'pdf.min.mjs');
 m.GlobalWorkerOptions.workerSrc=BASE+'pdf.worker.min.mjs';
 lib=m;return m;
}
export const isPdf=f=>!!f&&(f.type==='application/pdf'||/\.pdf$/i.test(f.name||''));
export const MAX_PDF_BYTES=200*1024*1024;
// Opens a PDF (File/Blob). Japanese PDFs whose fonts are not embedded need the character maps (cmaps).
export async function openPdf(file){
 if(file.size>MAX_PDF_BYTES)throw new Error('200MB以下のPDFを選んでください。');
 const m=await loadPdfjs();
 const data=new Uint8Array(await file.arrayBuffer());
 const task=m.getDocument({data,cMapUrl:BASE+'cmaps/',cMapPacked:true,standardFontDataUrl:BASE+'standard_fonts/',wasmUrl:BASE+'wasm/',isEvalSupported:false,enableXfa:false,verbosity:0});
 try{return await task.promise;}
 catch(e){
  if(e?.name==='PasswordException')throw new Error('パスワード付きのPDFは読み込めません。');
  if(e?.name==='InvalidPDFException')throw new Error('PDFとして読めないファイルです。');
  throw e;
 }
}
// One page as a JPEG data URL, `width` pixels wide (white background; the long edge stays ≤ maxEdge).
export async function renderPdfPage(pdf,n,width=1800,maxEdge=3000,quality=.85){
 const pg=await pdf.getPage(n);
 try{
  const v1=pg.getViewport({scale:1});
  const k=Math.min(width/v1.width,maxEdge/Math.max(v1.width,v1.height));
  const v=pg.getViewport({scale:k});
  const c=document.createElement('canvas');c.width=Math.max(1,Math.round(v.width));c.height=Math.max(1,Math.round(v.height));
  const ctx=c.getContext('2d');ctx.fillStyle='#ffffff';ctx.fillRect(0,0,c.width,c.height);
  await pg.render({canvas:c,canvasContext:ctx,viewport:v}).promise;
  const src=c.toDataURL('image/jpeg',quality),out={src,width:c.width,height:c.height};
  c.width=c.height=1;return out;
 }finally{pg.cleanup();}
}
// Stand-in picture for a PDF whose first page cannot be drawn (the file itself can still be opened).
export function pdfPlaceholder(name){
 const c=document.createElement('canvas');c.width=420;c.height=540;const x=c.getContext('2d');
 x.fillStyle='#ffffff';x.fillRect(0,0,420,540);x.strokeStyle='#c9d3cc';x.lineWidth=4;x.strokeRect(2,2,416,536);
 x.fillStyle='#b8402f';x.font='bold 96px sans-serif';x.textAlign='center';x.fillText('PDF',210,250);
 x.fillStyle='#33433c';x.font='26px sans-serif';const t=String(name||'').slice(0,40);
 x.fillText(t.length>18?t.slice(0,18)+'…':t,210,330);
 return {src:c.toDataURL('image/jpeg',.85),width:420,height:540};
}

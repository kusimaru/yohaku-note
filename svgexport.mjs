import { PAGE_WIDTH, inkWidth, blockRuns, ensureLayers, DEFAULT_TEXT_COLOR } from './model.mjs';
const esc=s=>String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
const num=v=>String(Math.round(v*100)/100);
const idOf=s=>String(s).replace(/[^\w\u3040-\u30ff\u3400-\u9fff\-]/g,'_').slice(0,40)||'layer';
// Variable-width stroke → closed outline (left side, end cap, right side, start cap).
export function strokeOutline(s) {
 const pts=[];for(const p of s.points)if(!pts.length||Math.hypot(p[0]-pts.at(-1)[0],p[1]-pts.at(-1)[1])>.05)pts.push(p);
 const r=i=>inkWidth(s.width,pts[i][2],s.pressure)/2;
 if(pts.length===1){const [x,y]=pts[0],rr=r(0);return 'M'+num(x-rr)+' '+num(y)+'a'+num(rr)+' '+num(rr)+' 0 1 0 '+num(rr*2)+' 0a'+num(rr)+' '+num(rr)+' 0 1 0 '+num(-rr*2)+' 0Z';}
 const left=[],right=[],normals=[];
 for(let i=0;i<pts.length;i++){
  const a=pts[Math.max(0,i-1)],b=pts[Math.min(pts.length-1,i+1)];let dx=b[0]-a[0],dy=b[1]-a[1];const len=Math.hypot(dx,dy)||1;dx/=len;dy/=len;
  const nx=-dy,ny=dx,rr=r(i);normals.push([nx,ny]);
  left.push([pts[i][0]+nx*rr,pts[i][1]+ny*rr]);right.push([pts[i][0]-nx*rr,pts[i][1]-ny*rr]);
 }
 const cap=(c,rr,n,forward)=>{const a0=Math.atan2(n[1],n[0])+(forward?0:Math.PI),out=[];for(let k=1;k<6;k++){const a=a0-k*Math.PI/6;out.push([c[0]+Math.cos(a)*rr,c[1]+Math.sin(a)*rr]);}return out;};
 const last=pts.length-1;
 const ring=[...left,...cap(pts[last],r(last),normals[last],true),...right.reverse(),...cap(pts[0],r(0),normals[0],false)];
 return 'M'+ring.map(q=>num(q[0])+' '+num(q[1])).join('L')+'Z';
}
function textElement(b) {
 const runs=blockRuns(b);if(!runs.length)return '';
 const lines=[[]];
 for(const r of runs){
  if(r.hr){lines.push([{hr:true}]);lines.push([]);continue;}
  const parts=r.text.split('\n');
  parts.forEach((t,i)=>{if(i>0)lines.push([]);if(t)lines.at(-1).push({...r,text:t});});
 }
 let y=b.y+8,out='';const lineHeight=size=>Math.round(size*1.8);
 for(const line of lines){
  if(line[0]?.hr){out+='<line x1="'+num(b.x+10)+'" y1="'+num(y+6)+'" x2="'+num(b.x+b.width-10)+'" y2="'+num(y+6)+'" stroke="#9fb2a6" stroke-width="1.5"/>';y+=16;continue;}
  const size=Math.max(15,...line.map(r=>r.size||15)),lh=lineHeight(size);y+=lh;
  if(!line.length)continue;
  out+='<text x="'+num(b.x+10)+'" y="'+num(y-lh*.3)+'" font-size="15" font-family="Yu Gothic UI, Meiryo, sans-serif" fill="'+DEFAULT_TEXT_COLOR+'" xml:space="preserve">';
  for(const r of line){
   const attrs=[];if(r.bold)attrs.push('font-weight="bold"');if(r.size)attrs.push('font-size="'+r.size+'"');if(r.color)attrs.push('fill="'+r.color+'"');
   out+=attrs.length?'<tspan '+attrs.join(' ')+'>'+esc(r.text)+'</tspan>':esc(r.text);
  }
  out+='</text>';
 }
 return out;
}
// Page → SVG text. Ink layers become groups (bottom first) so Illustrator can edit them
// as separate groups/layers; text and images are grouped below the ink.
export function pageToSvg(page,{includeText=true,includeImages=true,includeHidden=false}={}) {
 ensureLayers(page);
 const H=page.height;
 let out='<?xml version="1.0" encoding="UTF-8"?>\n<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="'+PAGE_WIDTH+'" height="'+H+'" viewBox="0 0 '+PAGE_WIDTH+' '+H+'">\n';
 out+='<title>'+esc(page.title||'名称未設定')+'</title>\n';
 if(includeImages&&page.blocks.some(b=>b.type==='image')){
  out+='<g id="images">\n';
  for(const b of page.blocks)if(b.type==='image')out+='<image x="'+num(b.x)+'" y="'+num(b.y)+'" width="'+num(b.width)+'" height="'+num(b.height)+'" preserveAspectRatio="none" xlink:href="'+b.src+'"/>\n';
  out+='</g>\n';
 }
 if(includeText&&page.blocks.some(b=>b.type==='text'&&b.text)){
  out+='<g id="text">\n';for(const b of page.blocks)if(b.type==='text'&&b.text)out+=textElement(b)+'\n';out+='</g>\n';
 }
 const used=new Set();
 for(const L of page.layers){
  if(!L.visible&&!includeHidden)continue;
  const strokes=page.strokes.filter(s=>s.layer===L.id);if(!strokes.length)continue;
  let id=idOf(L.name);while(used.has(id))id+='_';used.add(id);
  out+='<g id="'+esc(id)+'" data-name="'+esc(L.name)+'"'+(L.opacity<1?' opacity="'+num(L.opacity)+'"':'')+(L.visible?'':' display="none"')+'>\n';
  for(const s of strokes){
   if(s.pressure)out+='<path d="'+strokeOutline(s)+'" fill="'+s.color+'"/>\n';
   else out+='<path d="M'+s.points.map(p=>num(p[0])+' '+num(p[1])).join('L')+'" fill="none" stroke="'+s.color+'" stroke-width="'+num(s.width)+'" stroke-linecap="round" stroke-linejoin="round"/>\n';
  }
  out+='</g>\n';
 }
 return out+'</svg>\n';
}

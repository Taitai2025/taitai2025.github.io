// MusicXML contents are decoded locally. MXL lookups select two known ZIP
// members and never extract an archive onto a filesystem.
const maxFileBytes = 24 * 1024 * 1024;
const maxContainerBytes = 64 * 1024;
const zipError = () => new Error('MXL 文件不完整，或使用了不支持的压缩格式。');
const utf8 = new TextDecoder('utf-8',{fatal:true});
const scoreExtensions = /\.(?:mxl|musicxml|xml)$/iu;

function xmlText(bytes) {
  const [a,b,c,d] = bytes;
  const littleEndian = (a===255&&b===254) || (a===60&&b===0&&c&&d===0);
  const bigEndian = (a===254&&b===255) || (a===0&&b===60&&c===0&&d);
  const declaration = new TextDecoder('windows-1252').decode(bytes.subarray(0,160));
  const specified = /^\s*<\?xml\b[^>]*?\bencoding=["']([a-z][a-z\d._-]*)["']/iu.exec(declaration)?.[1];
  const encoding = littleEndian ? 'utf-16le' : bigEndian ? 'utf-16be' : specified ?? 'utf-8';
  try { return new TextDecoder(encoding,{fatal:true}).decode(bytes); }
  catch { throw new Error('无法读取这份 XML 的文字编码，请用制谱软件另存为 UTF-8 MusicXML。'); }
}

function readDirectory(bytes) {
  const view = new DataView(bytes.buffer,bytes.byteOffset,bytes.byteLength);
  const word = i=>view.getUint16(i,true);
  const long = i=>view.getUint32(i,true);
  const earliest = Math.max(0,bytes.length-65557);
  let end = bytes.length-22;
  while (end>=earliest && (long(end)!==0x06054b50 || end+22+word(end+20)!==bytes.length)) end--;
  if (end<earliest || word(end+4) || word(end+6) || word(end+8)!==word(end+10)) throw zipError();
  const count=word(end+10),size=long(end+12),start=long(end+16);
  if (!count || count>5000 || start+size!==end) throw zipError();
  let cursor=start;
  const items=new Map();
  for (let n=0;n<count;n++) {
    if (cursor+46>end || long(cursor)!==0x02014b50) throw zipError();
    const nameLen=word(cursor+28);
    const next=cursor+46+nameLen+word(cursor+30)+word(cursor+32);
    if (!nameLen || next>end || word(cursor+34)) throw zipError();
    let name;
    try {name=utf8.decode(bytes.subarray(cursor+46,cursor+46+nameLen));}
    catch {throw new Error('MXL 内部文件名的 UTF-8 编码无效。');}
    if (items.has(name)) throw zipError();
    items.set(name,{
      offset:long(cursor+42),method:word(cursor+10),encrypted:Boolean(word(cursor+8)&1),
      compressed:long(cursor+20),length:long(cursor+24),checksum:long(cursor+16),
    });
    cursor=next;
  }
  if (cursor!==end) throw zipError();
  return {items,start,word,long};
}

const crcTable=Uint32Array.from({length:256},(_,value)=>{
  for (let i=0;i<8;i++) value=(value>>>1)^((value&1)?0xedb88320:0);
  return value>>>0;
});
function crc32(bytes) {
  let checksum=0xffffffff;
  for (const byte of bytes) checksum=(checksum>>>8)^crcTable[(checksum^byte)&255];
  return (checksum^0xffffffff)>>>0;
}
async function inflateRaw(compressed,length) {
  let decoder;
  try {decoder=new DecompressionStream('deflate-raw');}
  catch {throw new Error('此浏览器暂时无法解压 MXL，请先在制谱软件中另存为 .musicxml。');}
  const reader=new Blob([compressed]).stream().pipeThrough(decoder).getReader();
  const decoded=new Uint8Array(length);
  let position=0;
  try {
    for (;;) {
      const chunk=await reader.read();
      if (chunk.done) break;
      if (position+chunk.value.length>length) throw zipError();
      decoded.set(chunk.value,position);
      position+=chunk.value.length;
    }
  } catch {throw zipError();}
  finally {await reader.cancel().catch(()=>{});}
  if (position!==length) throw zipError();
  return decoded;
}
async function readMember(bytes,zip,name,maximum) {
  const entry=zip.items.get(name);
  if (!entry) throw new Error('在 MXL 中找不到主谱件或目录。');
  const {offset,compressed,length,method,encrypted,checksum}=entry;
  const {word,long,start}=zip;
  if (length>maximum) throw new Error('MXL 解压后的谱件超出读取上限，请按乐章导出。');
  if (encrypted) throw new Error('MXL 谱件带有压缩包密码，请先在制谱软件中另存为 MusicXML。');
  if (offset+30>start || long(offset)!==0x04034b50 || word(offset+8)!==method || ![0,8].includes(method)) {
    throw zipError();
  }
  const localNameEnd=offset+30+word(offset+26);
  const payload=localNameEnd+word(offset+28);
  if (payload+compressed>start || utf8.decode(bytes.subarray(offset+30,localNameEnd))!==name) throw zipError();
  const content=bytes.subarray(payload,payload+compressed);
  const data=method===0?content:await inflateRaw(content,length);
  if (data.length!==length || crc32(data)!==checksum) throw zipError();
  return data;
}
function primaryPath(container) {
  if (/<!DOCTYPE|<!ENTITY/iu.test(container)) throw zipError();
  const document=new DOMParser().parseFromString(container,'application/xml');
  const first=document.getElementsByTagNameNS('*','rootfile')[0];
  const path=first?.getAttribute('full-path');
  if (!path || document.documentElement.localName!=='container' || document.querySelector('parsererror')
      || path.includes('\\') || path.includes('\0') || /^\w+:/u.test(path)
      || path.split('/').some(segment=>!segment||segment==='.'||segment==='..')) {
    throw new Error('MXL 缺少有效的主谱件路径。');
  }
  return path;
}

export async function readScoreFile(file) {
  if (!scoreExtensions.test(file.name??'')) throw new Error('请选择 .mxl、.musicxml 或 .xml 乐谱文件。');
  if (file.size>maxFileBytes) throw new Error('文件超出 24 MiB 读取上限，请按乐章导出。');
  const bytes=new Uint8Array(await file.arrayBuffer());
  const isZip=bytes[0]===80 && bytes[1]===75 && bytes[2]===3 && bytes[3]===4;
  if (!isZip && !/\.mxl$/iu.test(file.name)) return xmlText(bytes);
  const zip=readDirectory(bytes);
  const container=xmlText(await readMember(bytes,zip,'META-INF/container.xml',maxContainerBytes));
  const path=primaryPath(container);
  return xmlText(await readMember(bytes,zip,path,maxFileBytes));
}

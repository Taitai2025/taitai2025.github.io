// Sounding-pitch working ranges. Chinese profiles are conservative starting
// values under concert-pitch notation; edit them against your actual players.
const defined = (label, family, role, low, high, program, short, chromatic=0, diatonic=0, poly=1, staves=1, sound='') => ({
  name:label, label, family, role, low, high, program, short, chromatic, diatonic, poly, staves,sound,
});
export const profiles = {
  bangdi: defined('梆笛','吹管','lead',74,95,74,'梆笛'),
  qudi: defined('曲笛','吹管','lead',67,87,74,'曲笛'),
  fluteg: defined('新笛','吹管','lead',60,83,74,'新笛'),
  sheng: defined('高音笙','吹管','lead',60,88,22,'高笙',0,0,4),
  altoSheng: defined('中音笙','吹管','inner',52,79,22,'中笙',0,0,4),
  bassSheng: defined('低音笙','吹管','bass',40,64,22,'低笙',0,0,3),
  suona: defined('高音唢呐','吹管','lead',62,86,69,'高唢',0,0,1),
  altoSuona: defined('中音唢呐','吹管','inner',55,77,69,'中唢'),
  yangqin: defined('扬琴','弹拨','inner',53,87,16,'扬琴',0,0,3),
  pipa: defined('琵琶','弹拨','inner',45,79,107,'琵琶',0,0,3),
  liuqin: defined('柳琴','弹拨','lead',62,91,107,'柳琴',0,0,2),
  zhongruan: defined('中阮','弹拨','inner',43,74,107,'中阮',0,0,3),
  daruan: defined('大阮','弹拨','bass',38,67,107,'大阮',0,0,3),
  guzheng: defined('古筝','弹拨','inner',48,84,108,'筝',0,0,3),
  gaohu: defined('高胡','拉弦','lead',67,88,111,'高胡'),
  erhu: defined('二胡','拉弦','lead',62,83,111,'二胡'),
  zhonghu: defined('中胡','拉弦','inner',55,76,111,'中胡'),
  violin: defined('小提琴','西洋弦乐','lead',55,93,41,'Vln.',0,0,2,1,'strings.violin'),
  viola: defined('中提琴','西洋弦乐','inner',48,84,42,'Vla.',0,0,2,1,'strings.viola'),
  cello: defined('大提琴','西洋弦乐','bass',36,76,43,'Vc.',0,0,2,1,'strings.cello'),
  doublebass: defined('低音提琴','西洋弦乐','bass',28,60,44,'Cb.',-12,-7,2,1,'strings.contrabass'),
  flute: defined('长笛','西洋吹管','lead',60,93,74,'Fl.',0,0,1,1,'wind.flutes.flute'),
  oboe: defined('双簧管','西洋吹管','lead',58,86,69,'Ob.',0,0,1,1,'wind.reed.oboe'),
  clarinet: defined('降 B 单簧管','西洋吹管','lead',50,89,72,'Cl. in B♭',-2,-1,1,1,'wind.reed.clarinet.bflat'),
  bassoon: defined('大管','西洋吹管','bass',34,70,71,'Bsn.',0,0,1,1,'wind.reed.bassoon'),
  trumpet: defined('降 B 小号','西洋吹管','lead',54,80,57,'Tpt. in B♭',-2,-1,1,1,'brass.trumpet.bflat'),
  horn: defined('F 调圆号','西洋吹管','inner',41,72,61,'Hn. in F',-7,-4,1,1,'brass.french-horn'),
  trombone: defined('长号','西洋吹管','bass',40,70,58,'Tbn.',0,0,1,1,'brass.trombone.tenor'),
  piano: defined('钢琴','键盘','any',21,108,1,'Pno.',0,0,8,2,'keyboard.piano.grand'),
  marimba: defined('马林巴','打击','inner',48,88,13,'Mar.',0,0,2,1,'pitched-percussion.marimba'),
  percussion: defined('无固定音高打击乐','打击','perc',0,127,null,'Perc.'),
};
export const roles = {
  any:'通用／暂未指定', lead:'旋律及高声部',inner:'中声部与和声',bass:'低音支撑',perc:'无固定音高打击乐',
};
export const presets={
  mixed:{title:'中西室内合奏',ids:['flute','clarinet','erhu','zhongruan','cello','piano']},
  chinese:{title:'民乐小合奏',ids:['qudi','sheng','pipa','zhongruan','erhu','cello']},
  western:{title:'西洋室内合奏',ids:['flute','clarinet','violin','viola','cello','piano']},
};
export const sampleXML=`<?xml version="1.0" encoding="UTF-8"?>
<score-partwise version="4.0">
 <work><work-title>国乐谱汇编制演示</work-title></work>
 <part-list>
  <score-part id="P1"><part-name>旋律</part-name><score-instrument id="P1-I1"><instrument-name>长笛</instrument-name></score-instrument><midi-instrument id="P1-I1"><midi-channel>1</midi-channel><midi-program>74</midi-program></midi-instrument></score-part>
  <score-part id="P2"><part-name>中声部</part-name><score-instrument id="P2-I1"><instrument-name>中提琴</instrument-name></score-instrument><midi-instrument id="P2-I1"><midi-channel>2</midi-channel><midi-program>42</midi-program></midi-instrument></score-part>
  <score-part id="P3"><part-name>低音</part-name><score-instrument id="P3-I1"><instrument-name>大提琴</instrument-name></score-instrument><midi-instrument id="P3-I1"><midi-channel>3</midi-channel><midi-program>43</midi-program></midi-instrument></score-part>
 </part-list>
 <part id="P1"><measure number="1"><attributes><divisions>2</divisions><key><fifths>0</fifths><mode>major</mode></key><time><beats>4</beats><beat-type>4</beat-type></time><clef><sign>G</sign><line>2</line></clef></attributes><note><pitch><step>E</step><octave>5</octave></pitch><duration>2</duration><type>quarter</type></note><note><pitch><step>G</step><octave>5</octave></pitch><duration>2</duration><type>quarter</type></note><note><pitch><step>A</step><octave>5</octave></pitch><duration>4</duration><type>half</type></note></measure></part>
 <part id="P2"><measure number="1"><attributes><divisions>2</divisions><key><fifths>0</fifths></key><time><beats>4</beats><beat-type>4</beat-type></time><clef><sign>C</sign><line>3</line></clef></attributes><note><pitch><step>G</step><octave>3</octave></pitch><duration>4</duration><type>half</type></note><note><pitch><step>C</step><octave>4</octave></pitch><duration>4</duration><type>half</type></note></measure></part>
 <part id="P3"><measure number="1"><attributes><divisions>2</divisions><key><fifths>0</fifths></key><time><beats>4</beats><beat-type>4</beat-type></time><clef><sign>F</sign><line>4</line></clef></attributes><note><pitch><step>C</step><octave>3</octave></pitch><duration>8</duration><type>whole</type></note></measure></part>
</score-partwise>`;

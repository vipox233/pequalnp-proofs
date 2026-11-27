import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_29324_aux
def certWord0 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2147483647 48) 281474976710655) 48) 281474976710655)
def certWord1 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2654435769 48) 139957886120860) 48) 211520108480565)
def certWord2 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294967295 48) 281474976710655) 48) 281474976710655)
def certWord3 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3266489917 48) 43795434378838) 48) 114012561308153)
def certWord4 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 43690 48) 187649984473770) 48) 187649984473770) 48) 187649984473770) 48) 187649984473770) 48) 187649984473770)
def certWord5 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 52428 48) 225179981368524) 48) 225179981368524) 48) 225179981368524) 48) 225179981368524) 48) 225179981368524)
def certWord6 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 61680 48) 264917625139440) 48) 264917625139440) 48) 264917625139440) 48) 264917625139440) 48) 264917625139440)
def certWord7 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 65280 48) 280379743338240) 48) 280379743338240) 48) 280379743338240) 48) 280379743338240) 48) 280379743338240)
def certWord8 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 65535 48) 4294901760) 48) 281470681808895) 48) 4294901760) 48) 281470681808895) 48) 4294901760)
def certWord9 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 65535 48) 281470681743360) 48) 281474976645120) 48) 4294967295) 48) 65535) 48) 281470681743360)
def certWord10 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 65535 48) 281474976710655) 48) 0) 48) 4294967295) 48) 281474976645120) 48) 0)
def certWord11 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 65535 48) 281474976710655) 48) 281474976710655) 48) 281470681743360) 48) 0) 48) 0)
def certWord12 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 12885098496 48) 196608) 48) 12884901890) 48) 8590065666)
def certWord13 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294901760 48) 65535) 48) 0) 48) 281470681743360) 48) 4294901760)
def certWord14 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 240 48) 1030807879920) 48) 1030807879920) 48) 1030807879920) 48) 1030807879920) 48) 1030807879920)
def certWord15 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3084 48) 13245881256972) 48) 13245881256972) 48) 13245881256972) 48) 13245881256972) 48) 13245881256972)
def certWord16 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 204 48) 876186697932) 48) 876186697932) 48) 876186697932) 48) 876186697932) 48) 876186697932)
def certWord17 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 187647121205930 48) 2863267840) 48) 187647121205930) 48) 2863267840) 48) 187647121205930)
def certWord18 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2863311530 48) 43690) 48) 187647121162240) 48) 187649984430080) 48) 2863311530)
def certWord19 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 264913582878960 48) 4042260480) 48) 264913582878960) 48) 4042260480) 48) 264913582878960)
def certWord20 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4278255360 48) 65280) 48) 280375465082880) 48) 280379743272960) 48) 4278255360)
def certWord21 : Nat := (Nat.lor (Nat.shiftLeft 87309715459120 48) 189438437474296)
def certWord22 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3530094567 48) 109793691519225) 48) 68432804836032) 48) 50375965024575) 48) 232113235261255) 48) 20676116480696) 48) 232525249135261)
def certWord23 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 231348277582162 48) 168025118095253) 48) 71251456633540) 48) 271463725627207)
def certWord24 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 572662306 48) 37383965778466) 48) 35322383704096) 48) 18764998447377) 48) 18764762645251) 48) 3311470313472) 48) 56294136361779) 48) 286326784) 48) 18764712116275) 48) 3342336) 48) 858993459)
def certWord25 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 857879330 48) 56221979783970) 48) 56213389849376) 48) 56080243700481) 48) 56080243634944) 48) 56075948667442) 48) 55191171904050) 48) 54087348465969) 48) 54087331622960) 48) 52983525024290) 48) 37529996894754)
def certWord26 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 13107 48) 56294991999744) 48) 56294995329024) 48) 858993202) 48) 56294978499379) 48) 52983575556144) 48) 56294709015347) 48) 37530283221538) 48) 56294706787123) 48) 858980352)
def certWord27 : Nat := (Nat.lor (Nat.shiftLeft 370110240432 48) 116894875194981)
def certWord28 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 94610769843554 48) 81594381014025) 48) 141863315069633) 48) 150909492630290) 48) 148073704854955) 48) 6756107993482) 48) 81478558093958)
def certWord29 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 86 48) 13509082841874) 48) 147014059073963) 48) 8457468007817) 48) 71290826412118)
def certWord30 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281474723210191 48) 280379759984880) 48) 34085917491199)
def certWord31 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 247256164917440 48) 250567333044416) 48) 30907658403824) 48) 30907389968399)
def certWord32 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 16769216 48) 280375466983231) 48) 31882347609871) 48) 1095216725760)
def certWord33 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 40820610966805 48) 240632532804430) 48) 119850983227552) 48) 5497977597431)
def certWord34 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 261606456749559 48) 258294550161634) 48) 137980117180081) 48) 101553178748255)
def certWord35 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 16775914 48) 281002681303039) 48) 245189846761311) 48) 202307162799876)
def certWord36 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 39250 48) 168024650976623) 48) 72228575912592) 48) 134256396837748)
def certWord37 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 168580030232871 48) 81112215676613) 48) 111575592949503) 48) 214049743404845) 48) 90001710075929) 48) 53873108263892) 48) 86034465441540) 48) 15450084574659) 48) 60374985422438) 48) 87532197790828) 48) 47025444168467) 48) 88021559838953) 48) 25848154754962) 48) 195296705997671) 48) 12179051382889) 48) 72516335272250) 48) 4213307867989) 48) 37748496936033)
def certWord38 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 26829 48) 112997667907573) 48) 60374985416142) 48) 150534449873396)
def certWord39 : Nat := (Nat.lor (Nat.shiftLeft 211594248192 48) 12582912)
def certWord40 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 20971520 48) 67108944) 48) 5368709632) 48) 34359746560) 48) 549755879424) 48) 4398046511104) 48) 83886088) 48) 805306368) 48) 12884903936) 48) 288102547456) 48) 0) 48) 35184388866052)
def certWord41 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4042322160 48) 61680) 48) 264913582817280) 48) 264917625077760) 48) 4042322160)
def certWord42 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 280375465148160 48) 4278190080) 48) 280375465148160) 48) 4278190080) 48) 280375465148160)
def certWord43 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 8738 48) 37529996894754) 48) 37529996894754) 48) 37529996894754) 48) 37529996894754) 48) 37529996894754)
def certWord44 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1018929287 48) 59373976814944) 48) 179314956792527)
def certWord45 : Nat := (Nat.lor (Nat.shiftLeft 185615955151902 48) 264064245014153)
def certWord46 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4042260480 48) 61166) 48) 0) 48) 225176545394688) 48) 2863267840) 48) 21845) 48) 0) 48) 56294136348672) 48) 84213760) 48) 255)
def certWord47 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281406257233920 48) 4293787648) 48) 65450) 48) 0) 48) 280375465082880) 48) 4244373504) 48) 64250)
def certWord48 : Nat := (Nat.lor (Nat.shiftLeft 183979584681285 48) 7980130727237)
def certWord49 : Nat := (Nat.lor (Nat.shiftLeft 30787382771719 48) 280992998982143)
def certWord50 : Nat := (Nat.lor (Nat.shiftLeft 172790817460815 48) 240841469853915)
def certWord51 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2832274706 48) 28371181046953) 48) 87557354373132)
def certWord52 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 43217 48) 23168337171229) 48) 83695762030469) 48) 174311688560959) 48) 17271611393997) 48) 139238593425413)
def certWord53 : Nat := (Nat.lor (Nat.shiftLeft 2199023517696 48) 52776562327555)
def certWord54 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2570 48) 11038234380810) 48) 11038234380810) 48) 11038234380810) 48) 11038234380810) 48) 11038234380810)
def certWord55 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 170 48) 730155581610) 48) 730155581610) 48) 730155581610) 48) 730155581610) 48) 730155581610)
def certWord56 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1426063360 48) 20560) 48) 0) 48) 75058848464896)
def certWord57 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 179296673426929 48) 75670305005393) 48) 98302288155456) 48) 204613409718834) 48) 55385135133048) 48) 188837641920841) 48) 46357210408788) 48) 61427106585615) 48) 31165603715848) 48) 265940532614063) 48) 22229914095834) 48) 23382063237153) 48) 14213850532674) 48) 270140737715887) 48) 8304414557896) 48) 104522421702154) 48) 5081469092994) 48) 78142684838342) 48) 1816684003647) 48) 266597226791548)
def certWord58 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 777259665 48) 50096658197737) 48) 157690466718251) 48) 46484060318256) 48) 151930869828830) 48) 43701742348012) 48) 267723126298329) 48) 41431593330086) 48) 124249739346306) 48) 38851086131943) 48) 143718763562248) 48) 35559962189737) 48) 233483528099034) 48) 31362786204614) 48) 261701409089747) 48) 28081517827843) 48) 239384681696152) 48) 25173983893217) 48) 61624529032294) 48) 21670384702356) 48) 113237138341842) 48) 21026431308458) 48) 145226036328648) 48) 19958488502198) 48) 242202035751945) 48) 14504923761714) 48) 9268743073519) 48) 12986096356183) 48) 102649893099732) 48) 11288741677353) 48) 182050916142389) 48) 8798650369972) 48) 205475654808064) 48) 7266094941718) 48) 102761478352330) 48) 5206731392163) 48) 121637842601505) 48) 4337937613688) 48) 114546833775674) 48) 2953911796315) 48) 127646466419099) 48) 1825327939714) 48) 149963083708552)
def certWord59 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4020056158 48) 252341333444785) 48) 186168571846424) 48) 203636954871797) 48) 182555994225526) 48) 171881014334965) 48) 246417405934171) 48) 144726464101281) 48) 239167313379816) 48) 134868685255875) 48) 86974839038656) 48) 109450441678789) 48) 108999269161244) 48) 102118817749351) 48) 220964673791247) 48) 96099453654325) 48) 61470958036455) 48) 87487323066047) 48) 25487622291423) 48) 82665980381428) 48) 126509470380999) 48) 78919510476103) 48) 218292801712418) 48) 69322999610657) 48) 153086528603562) 48) 60388565595837) 48) 137938032695229)
def certWord60 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 460724847 48) 30045604289264) 48) 158609290379629) 48) 28533582141882) 48) 52888653445120) 48) 26804074387545) 48) 103053850451832) 48) 26470239180636) 48) 48881396134918) 48) 23729433941321) 48) 197770706458846) 48) 22084904030873) 48) 3320316411768) 48) 19304974192712) 48) 108461080756420) 48) 17762380353470) 48) 103590554535216) 48) 15067592854946) 48) 85706294101771) 48) 14401230212226) 48) 101803805950894) 48) 12814001376141) 48) 28286847605438) 48) 12032747637017) 48) 168740827504707) 48) 9921268222152) 48) 66391745990956) 48) 8940042586143) 48) 261851401852613) 48) 8425015281551) 48) 151522267476613) 48) 6749495887369) 48) 220641152274229) 48) 5277975577309) 48) 175827418074045) 48) 2816843252297) 48) 186483222458588) 48) 2139150287309) 48) 255640775785323) 48) 1464978309400) 48) 171150168144123) 48) 744144568400) 48) 111462995362809)
def certWord61 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1068837018 48) 69878537863021) 48) 265777919201670) 48) 64896267401569) 48) 193699685930403) 48) 62425326303263) 48) 227685726259950) 48) 58734342911329) 48) 3763277418933) 48) 57467337126234) 48) 147185060875772) 48) 53719875203229) 48) 82416923482952) 48) 51907178606226) 48) 74402477535318) 48) 49345846193262) 48) 141670230172783) 48) 47833544862503) 48) 201537768993630) 48) 46712049838689) 48) 142134059452506) 48) 45160092739620) 48) 42645399972898) 48) 43664547915679) 48) 7748781458464) 48) 42522642097695) 48) 277129103343929) 48) 41480033019121) 48) 49826534213018) 48) 39560374788997) 48) 243327667301085) 48) 36680899764341) 48) 267869062410414) 48) 35128994242311) 48) 70545355813185) 48) 33934728437464) 48) 222746104171868) 48) 32906557595108) 48) 176605247923677) 48) 31875283360976) 48) 61805057519788) 48) 31295498689549) 48) 234436963927320)
def certWord62 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3335938548 48) 217971380765166) 48) 202471956115902) 48) 189398658231306) 48) 169739952633647) 48) 169991350161481) 48) 6092555653061) 48) 146802770539084) 48) 214492430470041) 48) 109984330376194) 48) 41108786320542) 48) 104819955687192) 48) 79351075409159) 48) 100220244219757) 48) 78620823948346) 48) 84568592698502) 48) 54345445104866) 48) 79972782458542) 48) 214307166494040) 48) 77532235122283) 48) 189284679926556) 48) 76587682251671) 48) 230073878348397)
def certWord63 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3766170702 48) 245047087573864) 48) 30299560330225) 48) 156073396374145) 48) 264752496728375) 48) 131740434724592) 48) 244312441581060) 48) 113268157600074) 48) 222570608917201) 48) 72404482670713) 48) 192840758841217) 48) 63979357288784) 48) 3574263874220) 48) 54055070019529) 48) 130799698500472) 48) 47834702096548) 48) 184984891469679) 48) 42585404941852) 48) 53451474691349) 48) 38238984281779) 48) 275750289203539) 48) 27642057922229) 48) 16394251008200) 48) 22067978965783) 48) 243177058617239) 48) 19344822374791) 48) 26637647948383) 48) 15934682238589) 48) 228806017282811) 48) 14626922564779) 48) 244134712379869) 48) 11788383881717) 48) 222303378873199) 48) 6773658551267) 48) 110311948854540)
def certWord64 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 130776892143182 48) 104871822542589) 48) 102108767341294) 48) 126964647557539) 48) 68339372068478) 48) 23171433930416)
def certWord65 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 65537 48) 4295032832) 48) 281470681808895) 48) 1431633920) 48) 93823560584975) 48) 252641280) 48) 219043332147) 48) 65535) 48) 281470681743360) 48) 93824992215040) 48) 858993459)
def certWord66 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 5570645 48) 408028119125) 48) 365077790805) 48) 219046674483) 48) 219046608946) 48) 214751641617) 48) 73015558161) 48) 64425492495) 48) 64424837125) 48) 21475164163) 48) 12885098499)
def certWord67 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 84215559 48) 5519150875909) 48) 5519117845775) 48) 5519117190405) 48) 5519083504387) 48) 3311470313729) 48) 1103823438081) 48) 1095233372415) 48) 1095222362199) 48) 373667856469) 48) 511106678903)
def certWord68 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1414812756 48) 92721168790323) 48) 56294995342131) 48) 18773588513043) 48) 18773588381969) 48) 18911029563665) 48) 18764998447377) 48) 16557351571215) 48) 16557351505678) 48) 16553056535815) 48) 5527707256071)
def certWord69 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2863308960 48) 187649816046250) 48) 150120560232584) 48) 187641394408104) 48) 187641393883808) 48) 187607034145416) 48) 187503953357448) 48) 185442337597608) 48) 185440939627861) 48) 93824992236884) 48) 93820697204052)
def certWord70 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3149633945 48) 206414410264485) 48) 193126151335845) 48) 187654279506603) 48) 187654279441066) 48) 187649984473770) 48) 187649983818400) 48) 187649984473736) 48) 187503955585706) 48) 186919828892330) 48) 186919840033280)
def certWord71 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4008505068 48) 262701388197600) 48) 262649847803616) 48) 262409325964968) 48) 262409263180008) 48) 258294650822109) 48) 243944979815901) 48) 225252996926685) 48) 225252995878093) 48) 225184276401356) 48) 225179981368524)
def certWord72 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4042322160 48) 264917625139424) 48) 264848904614112) 48) 262709978263278) 48) 262709978263278) 48) 262701388197614) 48) 262709976035020) 48) 262709978263040) 48) 261687776046830) 48) 260502331387630) 48) 262563949375180)
def certWord73 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4210752240 48) 275955858864890) 48) 273748246329592) 48) 275947269454584) 48) 275947266308808) 48) 275741107877365) 48) 270436742329845) 48) 266021448577521) 48) 266021432062197) 48) 264939100303601) 48) 264921920172273)
def certWord74 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4276944620 48) 280293842681344) 48) 279280214932992) 48) 278167801429245) 48) 278167801363708) 48) 278163506396328) 48) 277802723638440) 48) 275955859520250) 48) 275955859520250) 48) 275947269454586) 48) 275955843136000)
def certWord75 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4279369489 48) 280452758896389) 48) 280401218502405) 48) 280384038371073) 48) 280384038305536) 48) 280379743338238) 48) 280371153272574) 48) 280371153272572) 48) 280362563337980) 48) 280371153141486) 48) 280293842812652)
def certWord76 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4291624908 48) 281255930036138) 48) 281109898919850) 48) 281109898919840) 48) 281066949246890) 48) 280963867803562) 48) 281066949246880) 48) 281109896691626) 48) 280963869900712) 48) 281101308854101) 48) 280744821129045)
def certWord77 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294901758 48) 281470681677820) 48) 281462091612156) 48) 281453501546490) 48) 281453501546488) 48) 281453501415408) 48) 281410551218160) 48) 281401961152494) 48) 281401961152494) 48) 281393371086813) 48) 281328945594333)
def certWord78 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294963440 48) 281474724069375) 48) 262710264590062) 48) 281474117730303) 48) 225180840340138) 48) 281473545076735) 48) 187651416107656) 48) 281473544945663) 48) 187642826129408) 48) 281472113442815) 48) 4294901760)
def certWord79 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294967292 48) 281474976514047) 48) 281410552201200) 48) 281474973368319) 48) 281255933378474) 48) 281474971140095) 48) 280379760049920) 48) 281474959867903) 48) 280371170114812) 48) 281474926182399) 48) 275955943734010)
def certWord80 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294967295 48) 187649950810111) 48) 281473545052320) 48) 281474976688810) 48) 150121991897087) 48) 187641394429951) 48) 281473542826632) 48) 281474976666965) 48) 93827855548415) 48) 5519117254655) 48) 281470681743360)
def certWord81 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294967295 48) 281255930036223) 48) 281474971140010) 48) 281474976710400) 48) 280379760050175) 48) 280371153272831) 48) 281474926181628) 48) 281474976709370) 48) 275955943735295) 48) 264917625143295) 48) 281473545054890)
def certWord82 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294967295 48) 281462091612159) 48) 281474975727600)
def certWord83 : Nat := (Nat.lor (Nat.shiftLeft 517147086661 48) 96235280467109)
def certWord84 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 32875 48) 104815442028422) 48) 147497296295544) 48) 114771530166375) 48) 147908539437318) 48) 517147082525) 48) 87993251832576) 48) 269897496223295) 48) 66415336178675) 48) 231954011678804) 48) 77083120731781) 48) 250145966418004) 48) 77228686149253) 48) 270293616982120) 48) 92677612660614) 48) 147010875381368) 48) 114767235266919) 48) 147908828898054)
def certWord85 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 120 48) 114788877876583) 48) 147905321304774) 48) 517145048846) 48) 96235274105602) 48) 218241991660607) 48) 53221196665843) 48) 232368340751434) 48) 60565070710308) 48) 179645705644127) 48) 103677463365606) 48) 215448463702120) 48) 109273819146118) 48) 147496222578296) 48) 114732706042215) 48) 147911245820886)
def certWord86 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 132389653131304 48) 15874325382131) 48) 2409040472148) 48) 36413169098759) 48) 147909621576454) 48) 517146423340) 48) 26832917652804) 48) 216207974230111) 48) 92630367762310) 48) 146526886347111) 48) 132389789455434) 48) 67583567283187) 48) 20618384271459) 48) 92630585602055) 48) 147906913026422) 48) 132389485359148) 48) 12607985968611) 48) 268086615238740) 48) 90431344637830) 48) 235871918138119)
def certWord87 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 132389485293612 48) 12575790499381) 48) 269114437825896) 48) 104858392555527) 48) 147566027276390) 48) 132389486217796) 48) 48891869681205) 48) 75607924303970) 48) 103716150210567) 48) 148181790908838) 48) 132415592090698) 48) 67551371887940) 48) 215303866312805) 48) 104781266581382) 48) 146532261364423) 48) 132389485361964) 48) 31299683628516) 48) 20902649559144) 48) 92664659601286) 48) 147494611919559)
def certWord88 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 517147418186 48) 33397666207429) 48) 74711047891038) 48) 94829391147015) 48) 147909895176358) 48) 132389502861104) 48) 48891869672932) 48) 215310057105492) 48) 84933786498950) 48) 146532270854711) 48) 132389486217008) 48) 48891869656547) 48) 268078563031144) 48) 103711635437446) 48) 147291158868679) 48) 132389788731952) 48) 41195288262115) 48) 267192717279352) 48) 114745407264646) 48) 146529860187095)
def certWord89 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 132389486676528 48) 43394311472131) 48) 267193262041172) 48) 69506195880007) 48) 147905318159047) 48) 132389485359148) 48) 35697730147829) 48) 57117813800552) 48) 69476130383814) 48) 147563331388103) 48) 132389739055664) 48) 36765046310371) 48) 2824586422366) 48) 69475979130758) 48) 147217059148551) 48) 132406918266672) 48) 42294799844339) 48) 3026995642488) 48) 114732706060167) 48) 95134430839495)
def certWord90 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 137887296536368 48) 48859677361475) 48) 3030745380968) 48) 109260951025542) 48) 182953861907143) 48) 517147419210) 48) 53223075693763) 48) 267193254180968) 48) 111459974275079) 48) 147909613155078) 48) 517163200556) 48) 29031940834580) 48) 126455774214248) 48) 104858392557446) 48) 147288463966919) 48) 132389485359148) 48) 19205055661220) 48) 39389262542892) 48) 33097320392791) 48) 147909626819543)
def certWord91 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 132389502992176 48) 48891869652292) 48) 216207973705822) 48) 83834274412422) 48) 147704830542535) 48) 132389739121708) 48) 36797241767395) 48) 267191382992994) 48) 92630367760391) 48) 147906913026454) 48) 517063265324) 48) 7009512883683) 48) 2412269562211) 48) 92630367891463) 48) 147911793222406) 48) 517146492720) 48) 48823150196197) 48) 57874801784936) 48) 92630199001095) 48) 147910988964822)
def certWord92 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 132389805506352 48) 41163092820497) 48) 248082243549288) 48) 103672726579078) 48) 146600990278343) 48) 132389789389631) 48) 53289916122099) 48) 3104312944741) 48) 92630367434630) 48) 146526886346871)
def certWord93 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2020106836 48) 81635469983751) 48) 147909635199745) 48) 184135588467775) 48) 67277114840966) 48) 147700781875912) 48) 141254635770956) 48) 52967684671109) 48) 74711002298112) 48) 132389737017388) 48) 14811589412453) 48) 74711002775672) 48) 121394368097306) 48) 131419665200451) 48) 267193270958191) 48) 114620599702128) 48) 7173499515650) 48) 211273744152168) 48) 92630299865095) 48) 147911514256339) 48) 8278422085460) 48) 69531972142982) 48) 146528512705223)
def certWord94 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2020632670 48) 92677864456199) 48) 147906913026657) 48) 183620461941827) 48) 69411477127175) 48) 144047861735526) 48) 142354147136586) 48) 52967684671110) 48) 58568922564472) 48) 119195345825836) 48) 23671836411477) 48) 74711002806380) 48) 114711383191596) 48) 149011847005171) 48) 3033723338872) 48) 114620532396656) 48) 8271658480595) 48) 444401734730) 48) 69532032665639) 48) 147911514256130) 48) 219904345658431) 48) 48533641594502) 48) 41735336166088)
def certWord95 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2020103231 48) 67277106874246) 48) 147288453481152) 48) 61574671262527) 48) 52965778917254) 48) 146738697667271) 48) 517145047084) 48) 19814702089861) 48) 76089422694520) 48) 120294857456940) 48) 30268891415859) 48) 267193159288440) 48) 114775992250412) 48) 140737614611780) 48) 179229631543400) 48) 92630367868040) 48) 43458726544371) 48) 3060222421087) 48) 92686454128647) 48) 184196203278865) 48) 253987193907294) 48) 69476085139334) 48) 146944856097479)
def certWord96 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2020106078 48) 81635251619718) 48) 146526888460992) 48) 255603912498772) 48) 81635257616262) 48) 146526886347080) 48) 517146426672) 48) 36397431916422) 48) 143769225733632) 48) 132389671291978) 48) 48859674215747) 48) 266914505359480) 48) 114676871474194) 48) 123177623876403) 48) 3028606285928) 48) 92630367144560) 48) 8273000710914) 48) 211548622055508) 48) 81635250501510) 48) 147774075302658) 48) 220419472970835) 48) 67277114803846) 48) 111342514258456)
def certWord97 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 7890992 48) 48520682960774) 48) 271052231082689) 48) 202310147729492) 48) 69476135962245) 48) 252080016261656) 48) 556205096752) 48) 48457700574934) 48) 146526882084728) 48) 130212189978416) 48) 48960589162037) 48) 75466917050479) 48) 114771529510956) 48) 140769810068963) 48) 267190309254248) 48) 92630367866496) 48) 8268952097538) 48) 18036840491110) 48) 92630367897478) 48) 146462209200898) 48) 219904345658442) 48) 52965880071974) 48) 146530391753416)
def certWord98 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 7893864 48) 103672980731782) 48) 271055205954514) 48) 219902333446237) 48) 69476135470726) 48) 93750328213543) 48) 2020365375) 48) 52945672963718) 48) 111342527891320) 48) 114758644609068) 48) 4947928602243) 48) 268086509271144) 48) 112559622074412) 48) 149011847005171) 48) 3033991772275) 48) 120208352877168) 48) 8274358650163) 48) 3055742117983) 48) 92630585999367) 48) 145079746564384) 48) 113766844748863) 48) 52965730125446) 48) 40979154535112)
def certWord99 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 8419432 48) 92565690546312) 48) 7173489029890) 48) 220419473105748) 48) 83769788729221) 48) 74711002333287) 48) 132389738400816) 48) 48522393528198) 48) 146522855548672) 48) 132389484375066) 48) 14807009228101) 48) 57118816731240) 48) 103715678460418) 48) 123177594516226) 48) 212344911198312) 48) 91595532676208) 48) 32322700275) 48) 3051446886228) 48) 91531074373510) 48) 146526886347281) 48) 272678891579476) 48) 69506200242054) 48) 146526886346887)
def certWord100 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2020370534 48) 92630367895559) 48) 147909635207987) 48) 8213728810047) 48) 52966266996534) 48) 146529854935816) 48) 517332292652) 48) 33098897524358) 48) 59321870325624) 48) 114711265751084) 48) 21440602997747) 48) 3029313454200) 48) 114706751695890) 48) 123145428567541) 48) 250636406882427) 48) 114711046663271) 48) 147906940388339) 48) 3060054648916) 48) 69476130588550) 48) 147704818955219) 48) 9313240440383) 48) 52965780457093) 48) 252080002613576)
def certWord101 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2020107092 48) 69476129734663) 48) 147910987916034) 48) 218804834030655) 48) 56264531902471) 48) 147906897240486) 48) 132389671289663) 48) 52967810496134) 48) 58565956126840) 48) 114711047518768) 48) 48960589087731) 48) 232214951918200) 48) 114775824478252) 48) 140737614612021) 48) 269117391470696) 48) 92686454369415) 48) 147906928771778) 48) 19002955423839) 48) 92630367895552) 48) 8268936253856) 48) 112152206140756) 48) 69475951970181) 48) 74711002308711)
def certWord102 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 7891028 48) 69475946690438) 48) 147219745600467) 48) 8798113130068) 48) 69475952461446) 48) 93750328214040) 48) 517147087916) 48) 33099023287861) 48) 74711002257408) 48) 114788709380140) 48) 2712381322564) 48) 180264119072872) 48) 109256438197281) 48) 149011850150899) 48) 3033731197029) 48) 92630586240128) 48) 8274354455298) 48) 19410977318758) 48) 92630367897478) 48) 146532270801601) 48) 62089797585983) 48) 52965779965830) 48) 58565956079719)
def certWord103 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 517147612223 48) 52965679302534) 48) 147838209295047)
def certWord104 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 7891028 48) 69476130516998) 48) 147219734004416) 48) 42882973586499) 48) 69476136519558) 48) 147288467174087) 48) 2020103231) 48) 52919903159940) 48) 215448490682112) 48) 132437066919980) 48) 29102824654148) 48) 180264119042048) 48) 114710794738178) 48) 105585437934915) 48) 267190301390963) 48) 120208604802160) 48) 9174159541235) 48) 3053730494568) 48) 92630367170567) 48) 147901275882001) 48) 43398252221516) 48) 69476138112902) 48) 146529854882504)
def certWord105 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2020829268 48) 83834274873351) 48) 147909635207938) 48) 25288775324735) 48) 52918399008775) 48) 147906912981414) 48) 448090026028) 48) 36294353192581) 48) 74711002412800) 48) 114775824478252) 48) 2712381285700) 48) 180264119042168) 48) 114711046663182) 48) 132386033886531) 48) 267193270958197) 48) 114711046663280) 48) 9172012098547) 48) 3053730166888) 48) 92630367170567) 48) 147906928771776) 48) 8213729010516) 48) 69476137568167) 48) 147906928771783)
def certWord106 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 7891028 48) 81635469979648) 48) 8274342756833) 48) 183070706131796) 48) 69476137568134) 48) 147700770341575) 48) 517146427184) 48) 48522125084293) 48) 74711002392320) 48) 132389485359148) 48) 1580674221621) 48) 250632863154296) 48) 114775824478241) 48) 131419655717875) 48) 3027557181535) 48) 92677864434816) 48) 8277585118195) 48) 3055741855060) 48) 81635251619718) 48) 146529854882498) 48) 26390299169866) 48) 69458721769350) 48) 218270020059431)
def certWord107 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 7891046 48) 92630367891463) 48) 184196203279106) 48) 25805914989396) 48) 69476138059398) 48) 58565956125208)
def certWord108 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1926 48) 146526886347287) 48) 132389738397488) 48) 48859674133491) 48) 3025368283240) 48) 92565875091463) 48) 147906928771783) 48) 517146427184) 48) 48826656654659) 48) 267193254180968) 48) 92630367168390) 48) 146529854882503)
def certWord109 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 51542753343 48) 280375532191743) 48) 211110519358448) 48) 244797344768) 48) 1957431410687) 48) 281406261428223) 48) 140737755807519)
def certWord110 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 17576078999491 48) 280444125708528) 48) 215242763942912) 48) 263913376517180) 48) 54700707610876) 48) 17523730824963) 48) 140738293710879)
def certWord111 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 264981295546364 48) 70304312327951) 48) 277351330201663) 48) 1065687715776) 48) 68169787969532) 48) 140673059913503) 48) 277351556433919)
def certWord112 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 17524536244287 48) 215500251594736) 48) 281217219951679) 48) 264978544136188) 48) 70094877094143) 48) 158325635038435) 48) 281217262942463)
def certWord113 : Nat := (Nat.lor (Nat.shiftLeft 68719476735 48) 145134729510880)
def certWord114 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 280444121628732 48) 70304312197120) 48) 211119125561344) 48) 520093696) 48) 0) 48) 0) 48) 0)
def certWord115 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1030855079936 48) 0) 48) 0) 48) 16777215) 48) 281440684019708) 48) 138538729357059) 48) 140753595465952)
def certWord116 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 16493681164288 48) 15) 48) 257764885440) 48) 16496432574467) 48) 211346754633728) 48) 251673603) 48) 140753595465952)
def certWord117 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 16493681164291 48) 211170664382704) 48) 4123638366208) 48) 16777215) 48) 281441686781711) 48) 263887081701151) 48) 140996007479040)
def certWord118 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1030855079936 48) 255) 48) 215500512575424) 48) 280409287950336) 48) 62918400) 48) 125279632867356) 48) 257698037760)
def certWord119 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 280444121628732 48) 70304312200960) 48) 277093573443599) 48) 240519213119) 48) 213304248897520) 48) 138542743551007) 48) 140753595465952)
def certWord120 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 264929752791100 48) 1030851002112) 48) 65974456008719) 48) 240533898176) 48) 15394169483267) 48) 140801916797152) 48) 4398046511072)
def certWord121 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281423433957375 48) 278176240373744) 48) 70098102516751) 48) 264153390318588) 48) 17318318764275) 48) 158325635038435) 48) 145135534866400)
def certWord122 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 16509853351936 48) 67070143229967) 48) 70364507930639) 48) 281200618898431) 48) 263882790731772) 48) 4194303) 48) 140737756774400)
def certWord123 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281423437101119 48) 212205743116047) 48) 70368266272783) 48) 281441152795647) 48) 279276020367356) 48) 140673051262751) 48) 140995454813983)
def certWord124 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281457796841535 48) 280375465086975) 48) 211106232795120) 48) 16776192) 48) 1073741823) 48) 279344672686051) 48) 145135266430976)
def certWord125 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281473966815295 48) 281406316085247) 48) 277080688558064) 48) 280409824820287) 48) 213271969730304) 48) 125344321617948) 48) 4397778075679)
def certWord126 : Nat := (Nat.lor (Nat.shiftLeft 68719475967 48) 145135533833984)
def certWord127 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 34361835549 48) 242992136812134) 48) 3674259792) 48) 106115957760) 48) 294205290359) 48) 280306747283675) 48) 89156878)
def certWord128 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 11717391194690 48) 186962747326608) 48) 213593092531216) 48) 158609284007968) 48) 35184374644892) 48) 3917152788992) 48) 805355544)
def certWord129 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 194401010066728 48) 55666484615692) 48) 184933809274937) 48) 859471612416) 48) 35184421309372) 48) 61231918656265) 48) 105753648726866)
def certWord130 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 121915793322039 48) 74616715472064) 48) 267196632870956) 48) 229682147232560) 48) 45080718586077) 48) 153772939294050) 48) 271043475067032)
def certWord131 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1100657738368 48) 4471396667665) 48) 4690718508033) 48) 17630942466112) 48) 72607500337424) 48) 20061502552795) 48) 4104091743936)
def certWord132 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 224418290272876 48) 126107916984593) 48) 215809842234449) 48) 19006288368708) 48) 2497595117584) 48) 144384205258784) 48) 88235826038796)
def certWord133 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 57109371091404 48) 237715194667797) 48) 13556638289089) 48) 56364666649531) 48) 261375783742201) 48) 50655641779787) 48) 145735793185505)
def certWord134 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 87004168179857 48) 220207846269759) 48) 84651389276115) 48) 69389344044235) 48) 218516342780097) 48) 150921917561935) 48) 225175526136557)
def certWord135 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 104597433340819 48) 224709307708915) 48) 26168121972933) 48) 109050929867711) 48) 191249320169258) 48) 127702171642525) 48) 10156070053698)
def certWord136 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 131880725772765 48) 18091539449599) 48) 171518974607302) 48) 280615503352213) 48) 85112692498230) 48) 272635721665725) 48) 243528231824404)
def certWord137 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 277403099144509 48) 56026972311364) 48) 207889068445967) 48) 75026711705087) 48) 246290067587059) 48) 280890846477823) 48) 208768822378479)
def certWord138 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 271527225309565 48) 94512229384021) 48) 137786684069215) 48) 76127053104085) 48) 104881978668375) 48) 223060556600566) 48) 175903337266884)
def certWord139 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281440614875135 48) 278176240402423) 48) 140591459466703) 48) 272128859399165) 48) 158268437428215) 48) 281472820706559) 48) 246273155251941)
def certWord140 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 228337640919726 48) 281474938960559) 48) 211103206762111) 48) 281239820541951) 48) 266147956457468) 48) 161596143828955) 48) 37530229522440)
def certWord141 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281457796840447 48) 275977418371055) 48) 211106160703359) 48) 281465312824319) 48) 280526862680063) 48) 281470677549023) 48) 192959995703167)
def certWord142 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281468105412351 48) 281035213484031) 48) 253330071224313) 48) 168814629092962) 48) 107810121576171) 48) 119915485475394) 48) 74766665416720)
def certWord143 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281474908536191 48) 281465847545855) 48) 280594279038975) 48) 281474976710591) 48) 261670882500542) 48) 272678882896541) 48) 83562776348991)
def certWord144 : Nat := (Nat.lor (Nat.shiftLeft 68719476479 48) 246290604539862)
def certWord145 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1660453089 48) 89813548023927) 48) 158876213831891) 48) 67138433923788) 48) 88666090990049) 48) 45515000587566) 48) 82128980682552) 48) 40149840438389) 48) 257793112638134) 48) 34814272607079) 48) 281277669226339) 48) 15911589907946) 48) 178735218814700) 48) 7033796231354) 48) 138448278514981)
def certWord146 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 225016827 48) 14507291315120) 48) 232499660768174) 48) 12791443819392) 48) 135596595494932) 48) 11705185929892) 48) 7104050203021) 48) 11123855919621) 48) 106901900628257) 48) 10755710912924) 48) 182523383426707) 48) 10231843785008) 48) 48224045919474) 48) 9820364277982) 48) 109783796955624) 48) 8893333833730) 48) 14323848592645) 48) 8653836126156) 48) 275775678921066) 48) 7873867941653) 48) 185336544861582) 48) 7503268021940) 48) 175024321929433) 48) 6999790585421) 48) 82639562754526) 48) 5618679547131) 48) 236304883417511) 48) 4963449046061) 48) 52175328841289) 48) 4160370312020) 48) 129862686032073) 48) 3158813967025) 48) 27599501360835) 48) 2623906775595) 48) 240127360543182) 48) 1609864839477) 48) 108177360328569) 48) 1192035418274) 48) 80298718499438) 48) 590270431337) 48) 39264595790259) 48) 309999304771) 48) 51436530413147)
def certWord147 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 577018277 48) 36250082287524) 48) 103238659018482) 48) 34705499299695) 48) 209951408990628) 48) 34116001668860) 48) 136309889170559) 48) 32099625344249) 48) 44552179071996) 48) 31199826811970) 48) 233204310187560) 48) 30320433634186) 48) 226894988637362) 48) 29444182055556) 48) 86337868710507) 48) 28450571688399) 48) 9277554812107) 48) 27782615210138) 48) 179358221911830) 48) 24790757479970) 48) 41279293189535) 48) 23238442095831) 48) 97891243182791) 48) 21942914651088) 48) 150315593195157) 48) 21428147720943) 48) 224124592610859) 48) 19666206790097) 48) 154133787294189) 48) 19234388447613) 48) 211828080345950) 48) 18937707958560) 48) 8903753026063) 48) 18553679515791) 48) 247824184857188) 48) 17885039759395) 48) 111970063338612) 48) 17322575007637) 48) 257792783252331) 48) 16621583732491) 48) 40669294364206) 48) 15798065958386) 48) 210659785847429)
def certWord148 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1208677319 48) 77550421820478) 48) 15463024896651) 48) 74167411622583) 48) 133742093551899) 48) 72007874330337) 48) 75437860529423) 48) 68524867795565) 48) 40618442173833) 48) 60290786801299) 48) 9930860603301) 48) 58517122331602) 48) 46747288228520) 48) 56278826300197) 48) 50153190058783) 48) 55713665659531) 48) 262139881529937) 48) 54870326915546) 48) 272649645934484) 48) 53843620737254) 48) 198724631703799) 48) 50887437266464) 48) 256367364185416) 48) 49992115367246) 48) 80720371744731) 48) 48283771284257) 48) 56479526668378) 48) 45956511705250) 48) 60095852075526) 48) 43664547915613) 48) 215642372671501) 48) 42399449949806) 48) 211652336447191) 48) 41402167141751) 48) 151909323775121) 48) 40964374930729) 48) 133629939064825) 48) 40730222011534) 48) 119911792577890) 48) 38559159100157) 48) 57557442331318) 48) 38312528913056) 48) 141270642279693)
def certWord149 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 49480 48) 217706480183620) 48) 155456393677922) 48) 187778089727572) 48) 136487913552399) 48) 236555905136544) 48) 129987857315104) 48) 209913983723560) 48) 114082087134916) 48) 20407054623654) 48) 107440236421391) 48) 144991123608524) 48) 104958697168466) 48) 83160734006796) 48) 101002340555098) 48) 169949017835337) 48) 93248139711599) 48) 168660469502539) 48) 91593482064664) 48) 92484923642629) 48) 88984071327957) 48) 195263449491122) 48) 87785757167116) 48) 125388559163452) 48) 82665980381937) 48) 173028299982035)
def certWord150 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 57184639 48) 3727677129566) 48) 134106113570171) 48) 3481051136806) 48) 214671108216116) 48) 3461111153442) 48) 90799955662327) 48) 3394481292042) 48) 233908264127347) 48) 3281012327156) 48) 56461689274260) 48) 3187492324065) 48) 38976875536056) 48) 3032476680879) 48) 235385726551681) 48) 2868271121035) 48) 261889968343738) 48) 2654634377769) 48) 17879983394261) 48) 2206811095552) 48) 236128744400252) 48) 2116786651626) 48) 256383809856009) 48) 2094268613085) 48) 56955591892941) 48) 1940154024363) 48) 115483108240818) 48) 1779755385216) 48) 176089388790902) 48) 1611192795504) 48) 6279263084732) 48) 1313237958912) 48) 154137799996366) 48) 828498772146) 48) 163444991804025) 48) 729660194958) 48) 153051167444215) 48) 355123658830) 48) 71098892741305) 48) 189571727391) 48) 34329675420073) 48) 94789435408) 48) 90980292778625)
def certWord151 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 114866114 48) 7188396902025) 48) 170089404129712) 48) 7131684537978) 48) 61813275734838) 48) 6966389376573) 48) 82033979966969) 48) 6787190621733) 48) 190825499455419) 48) 6683070105074) 48) 260318067539087) 48) 6518666429927) 48) 28089185087747) 48) 6440985298395) 48) 126731694127888) 48) 6148949738871) 48) 45861751083825) 48) 5883668268361) 48) 253549187757921) 48) 5758876976412) 48) 56513265049264) 48) 5552780215557) 48) 222591058398928) 48) 5417845130451) 48) 26328228996697) 48) 4966763791487) 48) 74646606894739) 48) 4910175552622) 48) 31387694557219) 48) 4786807571539) 48) 55516819582516) 48) 4700984640571) 48) 151075545213668) 48) 4595795231775) 48) 63552700135023) 48) 4430550008839) 48) 133264311756867) 48) 4271587656661) 48) 2950706330145) 48) 4161106674610) 48) 215302476118667) 48) 3833424839538) 48) 90331809837676)
def certWord152 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 179876457 48) 11784812300981) 48) 90091410835368) 48) 11573748763244) 48) 242584222149991) 48) 11385066883664) 48) 199587302708310) 48) 11211278256677) 48) 191615841111148) 48) 11128242440731) 48) 143151429456282) 48) 10954057517557) 48) 222303378660715) 48) 10813005826499) 48) 256749013623592) 48) 10444110891351) 48) 141772732166759) 48) 10138020350248) 48) 70167034083553) 48) 10035679922458) 48) 25031219873007) 48) 9846717155571) 48) 25997586025725) 48) 9738829629625) 48) 213640409060093) 48) 9464269703298) 48) 146522951736165) 48) 9256061765722) 48) 36017735800899) 48) 9064997718068) 48) 112768798208848) 48) 8925706848278) 48) 81660348813884) 48) 8787318802401) 48) 276269606670918) 48) 8379413497738) 48) 15805604985577) 48) 8185713395537) 48) 86578072585825) 48) 7848618428181) 48) 74204268024180) 48) 7582813914849) 48) 267009642009512)
def certWord153 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 276082213 48) 18049124995159) 48) 100914825663986) 48) 17911166341164) 48) 69290978231850) 48) 17651105730562) 48) 16355498297127) 48) 17220945055650) 48) 46450332890429) 48) 17119544676235) 48) 46587767841181) 48) 16850196631320) 48) 145037003475950) 48) 16549283499737) 48) 196095570856234) 48) 16213829422742) 48) 27496622507359) 48) 15783532629589) 48) 151865985514655) 48) 15472584494605) 48) 123811256192551) 48) 15301128752592) 48) 177884890886168) 48) 15056922348970) 48) 206390586764858) 48) 14615380626718) 48) 104359333242471) 48) 14232445717717) 48) 138607399486652) 48) 13980189330603) 48) 244134742893174) 48) 13854502489231) 48) 83764957456826) 48) 13275644038128) 48) 169788845788155) 48) 12947048500149) 48) 171017203372573) 48) 12635196885835) 48) 175827560407770) 48) 12323908422441) 48) 125709583941380) 48) 12179860622054) 48) 92183062950511)
def certWord154 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 379021664 48) 24730276861546) 48) 199235317680444) 48) 24491735062049) 48) 246578737807002) 48) 24258305857026) 48) 258712019087528) 48) 23976308184507) 48) 43860568142575) 48) 23695013320072) 48) 38358713759944) 48) 23602878092658) 48) 259996204286121) 48) 23519161685344) 48) 35270629180635) 48) 23416056452320) 48) 232405325098039) 48) 22709152978012) 48) 47910699940938) 48) 22171973129210) 48) 230481165026739) 48) 21587107582881) 48) 18614717280457) 48) 21513347666818) 48) 114203507656701) 48) 21427072799603) 48) 116458363668299) 48) 21262801638224) 48) 84641240833323) 48) 20656628175505) 48) 117888568944299) 48) 20007158747689) 48) 77786454159723) 48) 19514045370790) 48) 123261562503252) 48) 19304974193031) 48) 26637679413028) 48) 18927358578973) 48) 255155702750589) 48) 18580698894555) 48) 72387658395906) 48) 18319393231008) 48) 131623846200922)
def certWord155 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 481570343 48) 31530178190504) 48) 188184471729633) 48) 31385096625264) 48) 10063584765960) 48) 31190145113133) 48) 4918210114027) 48) 30806454311937) 48) 232972379624827) 48) 30546704997319) 48) 95473293439591) 48) 30438793026390) 48) 30919926024098) 48) 29840022903582) 48) 157514085416408) 48) 29780983356169) 48) 148666450588996) 48) 29392029358778) 48) 113340338929824) 48) 28977342192215) 48) 96104626927993) 48) 28720931805700) 48) 239114141097546) 48) 27842885196081) 48) 128200900602635) 48) 27416046016714) 48) 256671954717175) 48) 26962224289914) 48) 50848527612890) 48) 26701720328264) 48) 225718118607700) 48) 26508713007108) 48) 170587913351733) 48) 26038745307052) 48) 26929837990927) 48) 25753160390501) 48) 161761745080987) 48) 25665453692708) 48) 76927545206113) 48) 25245893990123) 48) 15410726170992) 48) 24899137509019) 48) 256216653281486)
def certWord156 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 602137882 48) 39393986028497) 48) 275849170026627) 48) 39098454844302) 48) 254769460447575) 48) 38619705189117) 48) 140935642567230) 48) 38280807719626) 48) 238938204299245) 48) 38238984282819) 48) 1886071600763) 48) 38037037064808) 48) 271262119361954) 48) 37583222677997) 48) 222131981568291) 48) 37110109053348) 48) 214744634205479) 48) 36762606379362) 48) 200532582641729) 48) 36129648287917) 48) 88309367732038) 48) 35713806901279) 48) 274040926412783) 48) 35166489812972) 48) 5330589878987) 48) 34930284044201) 48) 202907668542843) 48) 34591577284440) 48) 91384544881819) 48) 34445626253122) 48) 132903985934221) 48) 33537799036536) 48) 223849909751298) 48) 33225210076701) 48) 11077224554835) 48) 33014943063545) 48) 179920975303493) 48) 32665368075665) 48) 35760393274728) 48) 32446003813731) 48) 62715605290142) 48) 32158341471514) 48) 37860619218700)
def certWord157 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 717704593 48) 46907018783396) 48) 261826215422683) 48) 46778479487575) 48) 129167554438228) 48) 46372492290600) 48) 1040088811610) 48) 46222065936881) 48) 218721909354255) 48) 45787557931415) 48) 225950336513304) 48) 45416657398069) 48) 123450936069145) 48) 45214734887179) 48) 170154405511332) 48) 44775765649588) 48) 18726739290174) 48) 44630256920715) 48) 91655279617907) 48) 44155668539417) 48) 86771896067763) 48) 44022145099743) 48) 139256392403739) 48) 43251277768510) 48) 63768037414227) 48) 43001352824603) 48) 265390980213591) 48) 42922653132491) 48) 25233583589342) 48) 42585404942009) 48) 278649537087484) 48) 42482157168096) 48) 53756445421185) 48) 41472189212001) 48) 96091930020339) 48) 40860589696287) 48) 30847077731813) 48) 40740772848906) 48) 204883442169079) 48) 40432583124115) 48) 21879173124048) 48) 39795379610625) 48) 4480254533142)
def certWord158 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 920723950 48) 60047045703128) 48) 170055833020248) 48) 58686932006225) 48) 21205134329375) 48) 57268026618879) 48) 83898762342036) 48) 56929810199430) 48) 86995423997236) 48) 56050121519806) 48) 173972794491364) 48) 55647240139404) 48) 241077362334598) 48) 55463227241055) 48) 281102159102512) 48) 55140804932123) 48) 150771370992738) 48) 54971601924595) 48) 26084163489649) 48) 53895502639339) 48) 248297173034997) 48) 53328616501331) 48) 31856578038770) 48) 52762042707933) 48) 94004744371523) 48) 52066584440660) 48) 248331504034021) 48) 51659218890476) 48) 257415357117170) 48) 51031657229916) 48) 16708199851506) 48) 50728518626753) 48) 252643617257897) 48) 49366999510215) 48) 213263057078684) 48) 48979318221852) 48) 211837116410041) 48) 48355803343836) 48) 33295321427870) 48) 47919245962113) 48) 108221016705392) 48) 47467554482905) 48) 278842879792955)
def certWord159 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1286284325 48) 84275167382576) 48) 147743854762321) 48) 82508536498759) 48) 53112807088275) 48) 81096687176120) 48) 217708829871784) 48) 80502361508119) 48) 73909014825978) 48) 79708456765525) 48) 154177647993318) 48) 78145492698845) 48) 182713373369656) 48) 76463135737133) 48) 236683922100108) 48) 75715472737411) 48) 128145791239146) 48) 75068973859887) 48) 189220217906660) 48) 74175578719051) 48) 92222664757351) 48) 73752842093324) 48) 115677478180018) 48) 73355787190817) 48) 42280764151573) 48) 72444594241886) 48) 237220719462836) 48) 70617666895882) 48) 263321222645154) 48) 70245121212097) 48) 14015522901566) 48) 68359784709454) 48) 94352868707789) 48) 66992086269103) 48) 142104297402625) 48) 65567686540155) 48) 153558959196141) 48) 63812180130127) 48) 22128628449878) 48) 62626961045442) 48) 17988252327531) 48) 60767498286907) 48) 72298108145929)
def certWord160 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1909425283 48) 124031010893935) 48) 232634489508281) 48) 120117178887243) 48) 120965256642676) 48) 116155447863579) 48) 225496134716771) 48) 114440401282979) 48) 253353268914709) 48) 113268157605256) 48) 78573834787085) 48) 111410560918654) 48) 26935423033316) 48) 109691971396283) 48) 100976324463369) 48) 106756885471466) 48) 94924671981550) 48) 104654628019953) 48) 172543304084714) 48) 103039186263063) 48) 96767157896192) 48) 101196139682798) 48) 84934516499764) 48) 98716793985337) 48) 237165289994622) 48) 97675652716629) 48) 196766813222590) 48) 96501710739283) 48) 16906452056381) 48) 94513492809069) 48) 219006088281440) 48) 92245448545136) 48) 210806981567673) 48) 91246334923452) 48) 209020262039498) 48) 89717045875018) 48) 222570829718089) 48) 86896171437752) 48) 82327250892491) 48) 86092305550923) 48) 23198427968808) 48) 85604973366710) 48) 164983873133952)
def certWord161 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3830175747 48) 250053318861077) 48) 34122986370126) 48) 245761959254109) 48) 1536869075049) 48) 225468793275966) 48) 117341666433617) 48) 203003948083852) 48) 133189746180231) 48) 175489687134006) 48) 227545724965468) 48) 170911895231340) 48) 273458784714102) 48) 156073396374837) 48) 173922729455818) 48) 150088623097979) 48) 191991603378349) 48) 146440238432749) 48) 145236483101988) 48) 141309402971659) 48) 182392181735951) 48) 137344752383985) 48) 47212290717136) 48) 131651112564532) 48) 72453795853980) 48) 129173412148353) 48) 225376058849301)
def certWord162 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 34307988 48) 2244693197319) 48) 273589449893866) 48) 2166851174891) 48) 127680819934751) 48) 2077871833542) 48) 97345462630826) 48) 1886698340779) 48) 244795983717594) 48) 1812047593888) 48) 215134939067930) 48) 1772205441433) 48) 270952333149848) 48) 1683169476997) 48) 202658056390973) 48) 1551433007463) 48) 162152218755927) 48) 1534011244900) 48) 219086304824126) 48) 1437998776642) 48) 115203928791252) 48) 1367928930617) 48) 12408180843570) 48) 1327847178544) 48) 241768023749630) 48) 1281380843812) 48) 216870097693613) 48) 1191928791313) 48) 143864242061481) 48) 1136148021493) 48) 180122352799871) 48) 925263593668) 48) 233693477926235) 48) 800740671673) 48) 19821285403943) 48) 650978066581) 48) 92638159289905) 48) 562000756829) 48) 272674594579968) 48) 324389634118) 48) 107266812091060) 48) 195544612880) 48) 52394306586665)
def certWord163 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 82774093 48) 5375126668476) 48) 182901261723253) 48) 5130920395919) 48) 192741028768983) 48) 4957681222786) 48) 48275507183227) 48) 4839135511648) 48) 150117769619923) 48) 4751909848138) 48) 56135294041478) 48) 4683649385538) 48) 137692425892201) 48) 4494472381460) 48) 215169339026958) 48) 4336731161581) 48) 245448856265812) 48) 4270365475795) 48) 30567345964085) 48) 4086354084779) 48) 220658300627618) 48) 3978573579146) 48) 277558025330016) 48) 3817006039925) 48) 218592417363050) 48) 3679233246013) 48) 10917861066165) 48) 3549563716387) 48) 214280264909575) 48) 3146373595862) 48) 67083139833313) 48) 2905554223771) 48) 239895442036056) 48) 2841698632340) 48) 128320780754974) 48) 2794926768759) 48) 17837038295236) 48) 2502610715194) 48) 68135398292962) 48) 2411820417583) 48) 47970524482111) 48) 2273489846798) 48) 73044543116109)
def certWord164 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 133281494 48) 8716807178212) 48) 183730243297294) 48) 8652065933272) 48) 50835362953395) 48) 8403312117647) 48) 63286469032399) 48) 8206602209102) 48) 205144940515995) 48) 7910655985453) 48) 208056925580889) 48) 7837410002709) 48) 74204268046131) 48) 7737201133318) 48) 199050376662840) 48) 7689315747579) 48) 101507372680097) 48) 7493888575162) 48) 30490085236530) 48) 7360790529712) 48) 134153415431113) 48) 7315234817693) 48) 16793432552441) 48) 7204805609099) 48) 215079187026707) 48) 7149932250742) 48) 155147211856674) 48) 6957872252497) 48) 248412424484309) 48) 6926574880312) 48) 184022272329069) 48) 6773658551848) 48) 203182121163018) 48) 6672137455118) 48) 1803987802856) 48) 6584437638606) 48) 33457890276083) 48) 6176679789972) 48) 54468867574794) 48) 5956517102938) 48) 118665738101909) 48) 5594709755145) 48) 275011134400223)
def certWord165 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 190762854 48) 12285970352937) 48) 20354036758962) 48) 12224679054062) 48) 158475886497344) 48) 11984365357795) 48) 87600335134832) 48) 11884339989198) 48) 62586443313769) 48) 11740187003563) 48) 96658417270160) 48) 11621082204813) 48) 242743137304390) 48) 11510261222006) 48) 131894325985492) 48) 11454803675731) 48) 216423574880532) 48) 11267346860567) 48) 48692213235135) 48) 11060223347212) 48) 255585081194016) 48) 10944030575086) 48) 30163721221303) 48) 10857862793695) 48) 9169918812968) 48) 10708728088994) 48) 162487362766787) 48) 10447816296785) 48) 84774219576150) 48) 10087228246301) 48) 1559225040004) 48) 9943575824624) 48) 149924572757318) 48) 9785085135028) 48) 117583464982628) 48) 9456097364086) 48) 157002670397519) 48) 9191931381846) 48) 222264696291203) 48) 9087497340984) 48) 74758338506547) 48) 8918312618000) 48) 191869207890101)
def certWord166 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 244431685 48) 16015119093388) 48) 190305949705095) 48) 15934682238589) 48) 197109175129325) 48) 15738414566954) 48) 190022474995786) 48) 15418071846397) 48) 26027736405743) 48) 15347624578548) 48) 58622240074155) 48) 15001371020700) 48) 209195200238975) 48) 14929021832594) 48) 240402431503497) 48) 14846685875575) 48) 212407832968929) 48) 14707788483927) 48) 16866559790114) 48) 14601908718915) 48) 32985571188961) 48) 14491728416045) 48) 12326774623194) 48) 14242032979173) 48) 55332277941572) 48) 13952043322502) 48) 91139415580459) 48) 13725821635679) 48) 86414948727102) 48) 13510046911540) 48) 147416366635373) 48) 13361952656419) 48) 46922721037917) 48) 13290760571923) 48) 182149765134058) 48) 13142939274227) 48) 146561663700277) 48) 13048488790999) 48) 13172863128523) 48) 12786001644441) 48) 7542156895338) 48) 12709589158794) 48) 236171854172191)
def certWord167 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 313667804 48) 20514263077510) 48) 100906272445835) 48) 20306842030702) 48) 272919710470728) 48) 20190834070103) 48) 9990400673910) 48) 19966430089764) 48) 99403026536437) 48) 19792851374589) 48) 47360903694342) 48) 19458769031579) 48) 160163919501370) 48) 19209932378474) 48) 101919865431917) 48) 19019882828072) 48) 45638606782244) 48) 18622790045920) 48) 219322787968511) 48) 18492696170687) 48) 119460499270210) 48) 18261122683031) 48) 98376504054011) 48) 18156390256758) 48) 66460599520760) 48) 17851665223735) 48) 98952022139160) 48) 17583566163958) 48) 89090773005108) 48) 17365421133760) 48) 45552686442358) 48) 17224815808407) 48) 274981247748281) 48) 17067624501125) 48) 13860118183600) 48) 16914324787030) 48) 33982038356810) 48) 16820898041628) 48) 112167619242601) 48) 16568702799613) 48) 200064120670728) 48) 16290208550565) 48) 133500714149074)
def certWord168 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 382279117 48) 25028517369525) 48) 16394269621446) 48) 24865094243982) 48) 212742993116251) 48) 24644104164954) 48) 22209650808842) 48) 24536189769284) 48) 118318129762353) 48) 24242857907705) 48) 253098495970481) 48) 24025952032196) 48) 14070677401187) 48) 23859668981170) 48) 247708307645937) 48) 23800439051640) 48) 38006524264517) 48) 23412828411198) 48) 187020410927676) 48) 23207379604713) 48) 8792148465632) 48) 22931520361681) 48) 157879049469109) 48) 22650850448525) 48) 223282808698002) 48) 22423831843891) 48) 232491212812899) 48) 22067978966026) 48) 220933452380650) 48) 21892975105001) 48) 14478666188470) 48) 21633745294250) 48) 114504158015354) 48) 21557917651834) 48) 147717134893289) 48) 21115918422807) 48) 243177072070576) 48) 20829262910191) 48) 189412669721252) 48) 20661359022793) 48) 27191752725757) 48) 20626149282491) 48) 142129372009408)
def certWord169 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 482943104 48) 31492877065292) 48) 90667981686) 48) 30947392560153) 48) 69544580405120) 48) 30745744120723) 48) 148078046847181) 48) 30055633001298) 48) 267396532066049) 48) 29960740608807) 48) 231314508214356) 48) 29787042487015) 48) 25048699632226) 48) 29511951325892) 48) 86548333579224) 48) 28794969332262) 48) 106494150629753) 48) 28585632995836) 48) 33917790696149) 48) 28304137525641) 48) 25061561526191) 48) 27950128830818) 48) 274186841302965) 48) 27790799214859) 48) 159459670811729) 48) 27416046016751) 48) 31877661846612) 48) 27117077862568) 48) 51381103728580) 48) 26750630631498) 48) 53519994225413) 48) 26508713007119) 48) 60439182407725) 48) 26271530424278) 48) 281423837022865) 48) 26094716655543) 48) 249928838924853) 48) 25992906479522) 48) 162633628147436) 48) 25775522060075) 48) 17042818830735) 48) 25289686259410) 48) 32470335137870)
def certWord170 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 576164072 48) 37755235148331) 48) 59696319474031) 48) 37275146527198) 48) 45050479897824) 48) 37061576237477) 48) 274225631449472) 48) 36583631298875) 48) 244001942938445) 48) 36188930842836) 48) 92406770733488) 48) 35777062903930) 48) 211875576464417) 48) 35616137551970) 48) 249057101792836) 48) 35101614940140) 48) 194618388584020) 48) 34994359574455) 48) 47902301985528) 48) 34824131518377) 48) 63428597401565) 48) 34077001326326) 48) 180711268437993) 48) 33815499382462) 48) 189790824954571) 48) 33698553273939) 48) 229897221780079) 48) 33186407390745) 48) 59296821028595) 48) 32874517831118) 48) 79702207733244) 48) 32680181636508) 48) 163638750519707) 48) 32541324090775) 48) 104333841876135) 48) 32520846056837) 48) 240359749868315) 48) 32418656427374) 48) 171425518169732) 48) 31968281500944) 48) 16647779455156) 48) 31810882182351) 48) 92569913265106)
def certWord171 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 694892714 48) 45507080169818) 48) 124924110999115) 48) 45241538652445) 48) 46858782777910) 48) 45173167171753) 48) 243117305669694) 48) 44513142253690) 48) 48323353484889) 48) 44243794208793) 48) 108693409978513) 48) 44016335726597) 48) 173899601724183) 48) 43709858326393) 48) 102053379884128) 48) 43227586897724) 48) 257922027859866) 48) 42680889779902) 48) 192891925107089) 48) 42524464326298) 48) 213555010942281) 48) 42396720703048) 48) 250311335729961) 48) 41831421322761) 48) 102684711248473) 48) 41344180888979) 48) 189266950499308) 48) 40952407074061) 48) 234046274354794) 48) 40728006173945) 48) 230640362481514) 48) 40457273484482) 48) 222600180464783) 48) 40093387007039) 48) 90774739694355) 48) 39534989681642) 48) 111162945853478) 48) 39438768939811) 48) 248911121319297) 48) 38185164677769) 48) 259532568169780) 48) 37962961134202) 48) 60001270951783)
def certWord172 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 802402654 48) 52361419173776) 48) 91019740267207) 48) 51940846677820) 48) 142812749052165) 48) 51802395062031) 48) 145892237305784) 48) 51617617751750) 48) 155199426171665) 48) 51171944574601) 48) 219065587272412) 48) 50863634132505) 48) 9050266154378) 48) 50154300779926) 48) 240892595198840) 48) 49977870724464) 48) 227427869626171) 48) 49760218983686) 48) 187703709812203) 48) 49401605467372) 48) 4244178965934) 48) 49191741435031) 48) 144496331073381) 48) 48906715868257) 48) 30147119471298) 48) 48704113355800) 48) 237980575705957) 48) 47996353260423) 48) 107804409029229) 48) 47661570992972) 48) 226697688079833) 48) 47227733945072) 48) 6782473486434) 48) 47115751074478) 48) 195636475464605) 48) 46781800655454) 48) 90564388899131) 48) 46307467078165) 48) 5274925278598) 48) 46099733359081) 48) 73410283361597) 48) 45832324000146) 48) 203625096949055)
def certWord173 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 980972745 48) 63979357288983) 48) 174728827758882) 48) 63421481695654) 48) 234085271660302) 48) 63170630924647) 48) 40596993039886) 48) 63029167798608) 48) 3574374274080) 48) 62823762180240) 48) 239166194583924) 48) 60905586177855) 48) 203818592622294) 48) 59878451263085) 48) 97857445032964) 48) 59542077781505) 48) 231465279025102) 48) 58859103728943) 48) 122768231151825) 48) 58032145249423) 48) 27196614473381) 48) 57663033062483) 48) 200958101978642) 48) 57366728356837) 48) 82223721344343) 48) 56744708420504) 48) 230370024300118) 48) 56486177551058) 48) 266692551436220) 48) 55758135440005) 48) 77112688768319) 48) 55409131139676) 48) 83971749896928) 48) 55320702628431) 48) 37757896355203) 48) 54681896956345) 48) 239621352196482) 48) 54087790047512) 48) 91917418097316) 48) 53729849061526) 48) 208426986905025) 48) 52968346300443) 48) 46751525697653)
def certWord174 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1119890582 48) 73381550637751) 48) 133742101357293) 48) 72657874797069) 48) 49096875965304) 48) 72387963077011) 48) 192858010395649) 48) 71657691037950) 48) 9183726241264) 48) 70846054481995) 48) 52859240791890) 48) 70622001315866) 48) 31126698848109) 48) 69930803085187) 48) 167878449604607) 48) 69570457583417) 48) 201688429776052) 48) 69439096176420) 48) 243697500657819) 48) 69209488834290) 48) 25259757143201) 48) 68923158838863) 48) 167320084953796) 48) 68386126315055) 48) 51398916906954) 48) 68339372080655) 48) 163278517762342) 48) 68145154375158) 48) 272392159088398) 48) 67954332417474) 48) 162509710209005) 48) 67663932833153) 48) 82803705084335) 48) 67338812079358) 48) 179483410550657) 48) 66950884244669) 48) 247047530527863) 48) 66101097675725) 48) 214474488635862) 48) 65622810770294) 48) 110192673348170) 48) 64915288308465) 48) 111025889757459)
def certWord175 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1296725173 48) 84868366159101) 48) 126767244617365) 48) 83996123941858) 48) 87047372648388) 48) 83071355669346) 48) 270614268900861) 48) 82650720520996) 48) 107409799279481) 48) 82102408727163) 48) 105996743756203) 48) 81607137577459) 48) 231942356460201) 48) 80930216233351) 48) 255259728816704) 48) 80637826779467) 48) 35125468630448) 48) 80263526107376) 48) 280376688594114) 48) 79923647432779) 48) 280969382071457) 48) 79196215723962) 48) 98918589946857) 48) 78491865007953) 48) 72272608485052) 48) 78019840591561) 48) 55135676396215) 48) 77404330542666) 48) 106138408043298) 48) 76994978465241) 48) 34021606763861) 48) 76693029668252) 48) 21622032604418) 48) 75995117274386) 48) 194112199934529) 48) 75209875276868) 48) 85075854751598) 48) 74867801015311) 48) 235223613377542) 48) 74500448797559) 48) 241739067457903) 48) 73916971696931) 48) 145338524466679)
def certWord176 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1573948275 48) 103097324166583) 48) 84453499997390) 48) 101649345371209) 48) 27446388428284) 48) 101289358416860) 48) 54770953809053) 48) 99169317968397) 48) 103016300458025) 48) 98942066776564) 48) 108767247161315) 48) 97315082098807) 48) 278933840162907) 48) 96465163212551) 48) 276421259860387) 48) 95407598884476) 48) 139987318086353) 48) 94833690039801) 48) 214878655980330) 48) 94017828246877) 48) 31483537534921) 48) 93239545320638) 48) 210476292205884) 48) 92918142424182) 48) 184740838264253) 48) 91865426318138) 48) 225598846293021) 48) 91203607745198) 48) 270498427354749) 48) 90660300870205) 48) 213379646251454) 48) 90119756141015) 48) 129992842717603) 48) 88590426656789) 48) 197733046496725) 48) 87909978951623) 48) 34116260791645) 48) 87333966139151) 48) 205034474476659) 48) 86829316132435) 48) 125431537428577) 48) 85922548305437) 48) 201392315121296)
def certWord177 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2019712440 48) 131740434724639) 48) 63739310169651) 48) 130434832627278) 48) 104872184963974) 48) 128971499074118) 48) 178341834472566) 48) 124524876558656) 48) 199133755423361) 48) 123929320255460) 48) 218173320073893) 48) 122300370415361) 48) 175021750658103) 48) 119528807623830) 48) 198394945178528) 48) 118634820561719) 48) 244046132240166) 48) 116625529006600) 48) 205631928150292) 48) 116566749899226) 48) 13329056566179) 48) 115676027053875) 48) 162888361029227) 48) 112415686813175) 48) 86871714336820) 48) 110712777172141) 48) 108518325273606) 48) 109984292692883) 48) 175043062466910) 48) 109080323842855) 48) 104545460030922) 48) 108676627587716) 48) 246580016930137) 48) 107978439877151) 48) 6852118229850) 48) 107764502061377) 48) 76976032937990) 48) 106226720465012) 48) 122373823038316) 48) 105255807049623) 48) 55368016464054) 48) 103727323700763) 48) 58078123920598)
def certWord178 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3006547587 48) 196973087273579) 48) 15185695700067) 48) 194765857337334) 48) 2485412165725) 48) 188463627283218) 48) 196360175862769) 48) 187280947324554) 48) 67347874352027) 48) 182516415242970) 48) 98250101437615) 48) 177257122799185) 48) 175830026259876) 48) 171678450817991) 48) 111164948066524) 48) 170312000117362) 48) 200813720879051) 48) 161887576757047) 48) 187499263467541) 48) 160924034175354) 48) 245670244610795) 48) 157795198275244) 48) 81190149246514) 48) 155962636995758) 48) 234108141983430) 48) 153236722518715) 48) 95354894579889) 48) 151899532659165) 48) 223679904947499) 48) 149653887682486) 48) 171203958331836) 48) 146553551488076) 48) 110266885149092) 48) 143415299637848) 48) 105091428876102) 48) 139809104952881) 48) 186090158165971) 48) 137621012511978) 48) 18887066051263) 48) 136665786055736) 48) 126089436597575) 48) 136350727109161) 48) 48633941668246)
def certWord179 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 65266 48) 150547124871679) 48) 262593184131641) 48) 269783658937405) 48) 252621516629065) 48) 123917878968234) 48) 247512642281749) 48) 34122973030555) 48) 245047087586127) 48) 56804585301575) 48) 233685016759473) 48) 199221186029651) 48) 222043937620913) 48) 199826605773706) 48) 209981493591095) 48) 22646221975287)
def certWord180 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 533975941 48) 34347689909947) 48) 21385153042925) 48) 32541324090451) 48) 203878261956813) 48) 30043081415139) 48) 105867079963720) 48) 28011576891750) 48) 126311112700969) 48) 26656765188122) 48) 186097029780123) 48) 25467303171576) 48) 117098347078714) 48) 23264667374517) 48) 240161998346219) 48) 20126857761239) 48) 79190899956392) 48) 18979364081972) 48) 221225457658518) 48) 17326698532744) 48) 167370838269179) 48) 16342736965286) 48) 155585433834674) 48) 14966858124522) 48) 36150954142341) 48) 13341518793750) 48) 139706894865321) 48) 12750101416769) 48) 219292617812158) 48) 11094643509368) 48) 113627786391100) 48) 7355031029347) 48) 74925801348566) 48) 6241379419550) 48) 152930993844495) 48) 6075746157846) 48) 174478819018182) 48) 3203312321169) 48) 228741405937724) 48) 1687843176705) 48) 69501175286122) 48) 432065019943) 48) 57694296751599)
def certWord181 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1326430842 48) 85889534021058) 48) 135632037017119) 48) 82388000000704) 48) 131173831084234) 48) 80352625314040) 48) 151699464432797) 48) 78414320715200) 48) 137208144558499) 48) 72387963077045) 48) 174432601286294) 48) 71310106115913) 48) 59623778779135) 48) 67538555124895) 48) 66929491436575) 48) 66219761613628) 48) 54469764938533) 48) 64369117706886) 48) 31444433331764) 48) 62317902313625) 48) 260688260166747) 48) 59307803293144) 48) 170055830481358) 48) 57367323030116) 48) 265618784789690) 48) 52968346300155) 48) 239024307305093) 48) 49483586022643) 48) 212133479965289) 48) 47968950037263) 48) 95039756963918) 48) 46114820860393) 48) 73410275448683) 48) 43384623277940) 48) 215917256071410) 48) 42904710882986) 48) 92097613557412) 48) 40456363254544) 48) 129996359752858) 48) 37745181073897) 48) 231228718840168) 48) 35741851787338) 48) 192608349344527)
def certWord182 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 59961 48) 269783658937405) 48) 247562983096052) 48) 205925299069408) 48) 195375647732003) 48) 129457570510571) 48) 190789449722408) 48) 114098650766173) 48) 160924034175417) 48) 155110855954733) 48) 143508038254487) 48) 240301258561545) 48) 138526775147754) 48) 18887028473392) 48) 134711961679945) 48) 64319121491419) 48) 130078979748467) 48) 175185045521498) 48) 123681880502075) 48) 77113704164771) 48) 116955886872717) 48) 30053603320106) 48) 109292381627189) 48) 68119844839189) 48) 108382411448964) 48) 246579973506813) 48) 104208552910370) 48) 183980797614030) 48) 102889534938334) 48) 14080433948920) 48) 95176340100672) 48) 53224626388644) 48) 90901883736637) 48) 213379646635947) 48) 89962488484287) 48) 69455251703133)
def certWord183 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 31978 48) 18886550529876) 48) 51659218890477) 48) 275449648470509) 48) 25467303171425) 48) 180569304660545)
def certWord184 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 39 48) 96761926467586) 48) 129193711244290)
def certWord185 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 402854977 48) 52913997092104) 48) 19805291152164) 48) 212480622090528) 48) 8877699979267) 48) 22270479171801) 48) 70437782624088) 48) 4554833788929) 48) 141017803326208) 48) 22015975425) 48) 129193728283651) 48) 33833248) 48) 140737488355328) 48) 18691858169921) 48) 52776576561164) 48) 20890720928341) 48) 137439051794) 48) 74848428621824) 48) 17921408) 48) 72877340637016) 48) 4488261795840) 48) 67179559) 48) 96770247966768) 48) 6)
def certWord186 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 627456 48) 212412171026469) 48) 87969520156672) 48) 829197123801) 48) 88031042338816) 48) 73728) 48) 1536) 48) 14298456096) 48) 1162121728) 48) 528) 48) 35184372088832) 48) 18691697672192) 48) 156590158412) 48) 21990232556116) 48) 71606500065296) 48) 83640310562816) 48) 279443406848) 48) 1324888) 48) 4488261808128) 48) 0) 48) 240) 48) 382789489408) 48) 103148749104) 48) 2703683175444) 48) 1099914486913) 48) 52982716573004) 48) 2199023620608) 48) 142043963818033) 48) 74848395067393) 48) 4952642551808) 48) 1114112) 48) 12288) 48) 97994109288960) 48) 32) 48) 657222537986)
def certWord187 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 141905719459840 48) 4471094509568) 48) 279441310080) 48) 72877323845632) 48) 235937792) 48) 5120) 48) 397360) 48) 383058187009) 48) 103098368304) 48) 52776558137489) 48) 2199023255562) 48) 17729624997888) 48) 8590545664) 48) 212413244768293) 48) 83571507200000) 48) 3306880) 48) 71760649322496) 48) 2165317632) 48) 221140552450359) 48) 96774555516928) 48) 932276605700) 48) 20706511152) 48) 21395383862292) 48) 4398046511104) 48) 1030817329736) 48) 20899310863108) 48) 141976586518593) 48) 74848395068755) 48) 829739237376) 48) 23399283949581) 48) 159430279696384) 48) 98062895875072) 48) 240) 48) 1649573892867)
def certWord188 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1152256 48) 80470507356193) 48) 79246441578496) 48) 18874521) 48) 52828416573445) 48) 160530865074176) 48) 768) 48) 32) 48) 545024) 48) 19629621552) 48) 70368744179793) 48) 2199023255745) 48) 17798344474624) 48) 85899345920) 48) 2268548038656) 48) 17665334706176) 48) 554322362752) 48) 72877324042245) 48) 163831681654784) 48) 134284544) 48) 13176864) 48) 15) 48) 18704) 48) 35190817835027) 48) 18) 48) 17729624997888) 48) 73014444032) 48) 212274463637504) 48) 104290306) 48) 22545358127104) 48) 1179661) 48) 159430279696384) 48) 2162688) 48) 32) 48) 268702208)
def certWord189 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 823812 48) 212413034364994) 48) 79250753323008) 48) 1104078176256) 48) 17465081880) 48) 3455321120768) 48) 68223488) 48) 8458288) 48) 1162609152) 48) 1) 48) 70370239449107) 48) 1099914552577) 48) 52776572370960) 48) 20904265909268) 48) 71743670583344) 48) 13271482499072) 48) 26040336768) 48) 72877323976704) 48) 12288) 48) 98200410325504) 48) 9144060948496) 48) 266496) 48) 104239251760) 48) 70373461724179) 48) 3298534883585) 48) 18141941858304) 48) 60129542144) 48) 216677610461456) 48) 4479670245377) 48) 57454852308992) 48) 35718889472) 48) 1091567989) 48) 140953513100327) 48) 96774542934064) 48) 14)
def certWord190 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 536942928 48) 9152575307776) 48) 18874649) 48) 52828416507921) 48) 163830540795904) 48) 273743872) 48) 14913619701760) 48) 1342722560) 48) 67856) 48) 2703686323220) 48) 1099511627905) 48) 17592196091920) 48) 91259466679060) 48) 212411902590976) 48) 53958660) 48) 22270483366101) 48) 17609685008384) 48) 2543713263989) 48) 140953445990400) 48) 2) 48) 129193442808834) 48) 25666777284928) 48) 52778790570003) 48) 3298691186753) 48) 53120155516928) 48) 8591507988) 48) 142043695284224) 48) 4471060955136) 48) 279443407232) 48) 36593440325632) 48) 24576) 48) 2163200) 48) 17371168) 48) 1206978876162)
def certWord191 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 532 48) 141974975807488) 48) 5020816769025) 48) 5227520458752) 48) 6081975877632) 48) 1462455250944) 48) 0) 48) 96) 48) 92803584) 48) 0) 48) 35184374531090) 48) 3531872539777) 48) 70712341561344) 48) 64424509440) 48) 70438805831680) 48) 8869107466240) 48) 1104075030528) 48) 76175573516288) 48) 4312821761) 48) 140880431480832) 48) 4198480) 48) 1207691907842) 48) 3600) 48) 1049618) 48) 3536234747137) 48) 70506208301636) 48) 20903605829632) 48) 146303766010128) 48) 4479684444161) 48) 92909271515136) 48) 1310720) 48) 2232430593) 48) 140815876947968) 48) 6124631830544) 48) 640218829573)
def certWord192 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1 48) 1170378622240) 48) 74848428624978) 48) 22854330482821) 48) 17901742653445) 48) 160530865070081) 48) 140816006971392) 48) 14929323175984) 48) 6) 48) 35703228720) 48) 35188016943123) 48) 3536234751233) 48) 70506183131136) 48) 85899972864) 48) 71674414235648) 48) 17665334712324) 48) 40137276784640) 48) 69005213696) 48) 77824) 48) 68223488) 48) 9144060948528) 48) 1207691907843) 48) 41076393264) 48) 35184372088832) 48) 2199023473920) 48) 35321811042304) 48) 25769803776) 48) 141906256369936) 48) 4479650891154) 48) 554858184704) 48) 1310720) 48) 2165321728) 48) 80402929876992) 48) 6117518290976) 48) 8448)
def certWord193 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 26038239232 48) 1310725) 48) 163830607904768) 48) 139526656) 48) 13546675580944) 48) 8448)
def certWord194 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 221071630401536 48) 67108864) 48) 279444455424) 48) 1310720) 48) 24576) 48) 160188989440) 48) 320) 48) 20) 48) 54820896) 48) 87962428641427) 48) 4398046511104) 48) 412316869956) 48) 2207613190144) 48) 1610612756) 48) 79173511020544) 48) 6291456) 48) 52828399730688) 48) 3239051264) 48) 4608) 48) 9734987856) 48) 541331970) 48) 0) 48) 105553118447634) 48) 2199184015621) 48) 52776558141764) 48) 19791209299968) 48) 71537512153136) 48) 79242280828928) 48) 550029492608) 48) 54202806042648) 48) 3455321112576) 48) 349168599040) 48) 26397749882896) 48) 15)
def certWord195 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 853 48) 138244259840) 48) 100663296) 48) 13631488) 48) 393216) 48) 2165309440) 48) 238937898680320) 48) 19331660984320) 48) 6) 48) 1) 48) 87960935532562) 48) 402928833) 48) 52845286330440) 48) 20895015895040) 48) 4563402789) 48) 83571473645568) 48) 16777216) 48) 524288) 48) 303046656) 48) 343736975360) 48) 4263968) 48) 6) 48) 1552) 48) 70368746619906) 48) 2199023408384) 48) 35184372102472) 48) 90168543412224) 48) 4831838208) 48) 8869157797888) 48) 8839582711808) 48) 34644951040) 48) 4296015872) 48) 3328) 48) 272) 48) 1112019456)
def certWord196 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 56 48) 2337267515392) 48) 5020816769024) 48) 8388608) 48) 1179648) 48) 12288) 48) 207300461824) 48) 21818843168) 48) 1162084866) 48) 4720160) 48) 52776558136337) 48) 2199116906761) 48) 52913997096260) 48) 2216203124736) 48) 536870960) 48) 13271465721861) 48) 39862130442624) 48) 71812171956233) 48) 163831614545920) 48) 256) 48) 10011811840) 48) 790787) 48) 1) 48) 70368744341602) 48) 294977669) 48) 52914011309456) 48) 20890720927832) 48) 141974438959440) 48) 18223546236928) 48) 6291456) 48) 23399283949568) 48) 2165317632) 48) 221080427103232) 48) 14302584848) 48) 626000387)
def certWord197 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 5100273745 48) 79242163388416) 48) 8860467200) 48) 458752) 48) 32768) 48) 275147522560) 48) 96) 48) 1085696) 48) 18704) 48) 2572160083) 48) 0) 48) 481036353860) 48) 19791209299968) 48) 141906793201664) 48) 141784252416) 48) 863556861952) 48) 393216) 48) 4760973357056) 48) 206360937728) 48) 12956278800) 48) 383595090689) 48) 53989392688) 48) 70368744177664) 48) 6597069984833) 48) 35390530519044) 48) 18691697672192) 48) 1610612736) 48) 17665234042880) 48) 8388608) 48) 17918905614336) 48) 303038464) 48) 1536) 48) 32) 48) 2)
def certWord198 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 24 48) 2337804386304) 48) 100663298) 48) 92368103538688) 48) 76158393843736) 48) 4485039525888) 48) 512) 48) 13176880) 48) 1052928) 48) 54820896) 48) 87960930222080) 48) 6597069853888) 48) 35390530531912) 48) 19799799235840) 48) 146373290754048) 48) 691489734657) 48) 75317088616448) 48) 34645147665) 48) 163829467062272) 48) 1536) 48) 96) 48) 3) 48) 0) 48) 105553119495186) 48) 3298534883521) 48) 17729624997888) 48) 0) 48) 71536975282209) 48) 79242180165632) 48) 6291456) 48) 553844736) 48) 3661461733376) 48) 68224000) 48) 8458352) 48) 1161830913)
def certWord199 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 596 48) 2336462281040) 48) 5304301387776) 48) 275151585280) 48) 3775004672) 48) 61440) 48) 69928617216) 48) 5716844576) 48) 625213952) 48) 16793888) 48) 17592190583826) 48) 128) 48) 17935783449164) 48) 19808389169152) 48) 211176294187008) 48) 691506511874) 48) 93459025231872) 48) 393216) 48) 5653269594112) 48) 284811198464) 48) 14298390528) 48) 383595369217) 48) 22315040) 48) 17592186044416) 48) 3298674410625) 48) 52914022269520) 48) 20890720927744) 48) 140807550009377) 48) 84190016045056) 48) 554326556672) 48) 1179648) 48) 2201189625856) 48) 139526912) 48) 21491949616) 48) 266499)
def certWord200 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1108 48) 140875195813168) 48) 79246458355712) 48) 554321313792) 48) 1627586560) 48) 12288) 48) 14745600) 48) 96) 48) 1342722560) 48) 103149781296) 48) 17592187112466) 48) 1099511627776) 48) 481036337152) 48) 64424509512) 48) 6734508720133) 48) 149885802250240) 48) 554321313792) 48) 58583387734016) 48) 5515964841985) 48) 27831599039232) 48) 14933610016816) 48) 1343263235) 48) 0) 48) 105553116266657) 48) 3298534883330) 48) 17592186056772) 48) 19808389170260) 48) 211243671536912) 48) 83644504866820) 48) 40137008349184) 48) 17609667903488) 48) 3373277184) 48) 353329349376) 48) 9932251136) 48) 823552)
def certWord201 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1610711073 48) 79246491910144) 48) 571499085824) 48) 76192753385477) 48) 163831681650688) 48) 349176988672) 48) 26401776414768) 48) 6) 48) 72646944) 48) 35190818951187) 48) 4398046533833) 48) 35184372089728) 48) 178120883699712) 48) 71537243717712) 48) 13546377183232) 48) 0) 48) 34644951040) 48) 2563023831040) 48) 256) 48) 939925504) 48) 545026) 48) 34898208) 48) 4341858) 48) 1099659674753) 48) 53051436040192) 48) 25769804373) 48) 137438953525) 48) 79173460688900) 48) 93184149422281) 48) 35511108698112) 48) 3661461721088) 48) 343736975360) 48) 14302912544) 48) 1649590670081)
def certWord202 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 804 48) 212343451549696) 48) 8869157804036) 48) 58004339687424) 48) 36593423482880) 48) 24576) 48) 5120) 48) 17371136) 48) 528642) 48) 3671584) 48) 0) 48) 6597070050306) 48) 35184372088832) 48) 30065578244) 48) 212412171060496) 48) 79246491910144) 48) 26038239616) 48) 72911683846144) 48) 53248) 48) 69995725056) 48) 13224714240) 48) 268702213) 48) 5783840) 48) 52776559525922) 48) 133) 48) 17729643414924) 48) 20899310862336) 48) 71537780690001) 48) 79246508687363) 48) 4952635211776) 48) 196608) 48) 0) 48) 68224000) 48) 112) 48) 3)
def certWord203 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 512 48) 141974707372032) 48) 234881027) 48) 92909273612377) 48) 88014936145920) 48) 5499791613952) 48) 0) 48) 26397749882896) 48) 18) 48) 1) 48) 70368744177664) 48) 21990232839232) 48) 35459249995792) 48) 159437775962112) 48) 4831861072) 48) 18223613345792) 48) 22029426229248) 48) 4848615424) 48) 8192) 48) 228841358336) 48) 16) 48) 306713090) 48) 0) 48) 35184372090961) 48) 16492768067853) 48) 52845277609984) 48) 177038551941208) 48) 141974975807569) 48) 79242180165632) 48) 96779034951680) 48) 553844760) 48) 2287090016256) 48) 168569150308352) 48) 4263936) 48) 1650094510848)
def certWord204 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2268548038656 48) 33554435) 48) 829470801920) 48) 40974289993728) 48) 4554831691776) 48) 228846600704) 48) 13224714288) 48) 8451) 48) 103148716336) 48) 0) 48) 6597069766666) 48) 17729650172232) 48) 20899310863636) 48) 221139544670273) 48) 74848428621824) 48) 97328792862720) 48) 38792446869504) 48) 2201189629952) 48) 139526144) 48) 240) 48) 3) 48) 85229856) 48) 3641020435) 48) 0) 48) 17728) 48) 37387690312276) 48) 70506720002048) 48) 1241245548544) 48) 4194304) 48) 2749349494784) 48) 3239059457) 48) 141017803325440) 48) 18601746448) 48) 8)
def certWord205 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 256 48) 71606231629829) 48) 149610924343296) 48) 8388608) 48) 72895560744960) 48) 2165338112) 48) 4352) 48) 14933606084624) 48) 357040640) 48) 41154561328) 48) 17592189535234) 48) 3298534883456) 48) 17935783445824) 48) 37400575213568) 48) 1073741824) 48) 100663296) 48) 44041135718400) 48) 51556515840) 48) 1255223074816) 48) 68787765248) 48) 32) 48) 1162367490) 48) 0) 48) 105559563127827) 48) 1099511824577) 48) 35321811051844) 48) 2211908981028) 48) 216810217537557) 48) 70514806620160) 48) 6291456) 48) 4848812032) 48) 73728) 48) 69995725824) 48) 921632) 48) 266498)
def certWord206 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4026531921 48) 8873452765188) 48) 23128935759872) 48) 35718823936) 48) 4402360360960) 48) 78451441664) 48) 8458240) 48) 625213954) 48) 33040) 48) 52776563380370) 48) 3298534883401) 48) 17592204480524) 48) 161632504250368) 48) 5368709120) 48) 141767475200) 48) 97036736135168) 48) 553779200) 48) 40960) 48) 23757718528) 48) 8720688) 48) 823552) 48) 49168) 48) 35184372453394) 48) 2199023255617) 48) 17729625011528) 48) 2207613191444) 48) 141975512678400) 48) 4471077732353) 48) 92909273612288) 48) 6064796073984) 48) 240553836544) 48) 139527168) 48) 1480663040) 48) 9)
def certWord207 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 40 48) 15530870211856) 48) 79246508687361) 48) 40137006252032) 48) 69004886016) 48) 3373273088) 48) 3840) 48) 1489313792) 48) 13) 48) 0) 48) 105553118381074) 48) 3298534883328) 48) 412316860424) 48) 18726057411092) 48) 71605694758917) 48) 149610890788864) 48) 97036732989440) 48) 34645082112) 48) 2148532224) 48) 138580984320) 48) 13817526693904) 48) 7) 48) 39125024) 48) 2376706) 48) 5497558138882) 48) 17729624997888) 48) 36296768618496) 48) 5368731984) 48) 18223563014144) 48) 6291840) 48) 54202806108184) 48) 2287090024448) 48) 1792) 48) 96) 48) 1085698)
def certWord208 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4831838208 48) 8869141020672) 48) 8388608) 48) 17196974080) 48) 3301774995456) 48) 1792) 48) 12897558544) 48) 352850432) 48) 16400) 48) 3490818) 48) 4398046511237) 48) 17729625018380) 48) 90159953478740) 48) 140874927308801) 48) 141708167747588) 48) 40137277833216) 48) 196608) 48) 4762047090688) 48) 2162295808) 48) 22083084288) 48) 323228164) 48) 0) 48) 35184372090881) 48) 0) 48) 137438974464) 48) 90168543413524) 48) 212343451549696) 48) 117440512) 48) 824903204864) 48) 40974290124800) 48) 3661545603072) 48) 202441472) 48) 32) 48) 306450944)
def certWord209 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 268435456 48) 416645382148) 48) 40686762065920) 48) 24) 48) 3387675389952) 48) 1792) 48) 10003488768) 48) 92803588) 48) 1) 48) 87960930222080) 48) 6597069903049) 48) 35459249996416) 48) 107752139522048) 48) 4831838229) 48) 83571523977217) 48) 93184147324928) 48) 51824820224) 48) 380190593024) 48) 206635776) 48) 240) 48) 1374947906309) 48) 0) 48) 105553116266496) 48) 8796093022409) 48) 17660905533452) 48) 19812684136472) 48) 2336462209024) 48) 335544325) 48) 1121523335168) 48) 17609668100096) 48) 24576) 48) 228975575040) 48) 128) 48) 18)
def certWord210 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 5368709138 48) 70720981827584) 48) 7340032) 48) 58583656103936) 48) 101711872) 48) 68223488) 48) 208) 48) 528642) 48) 0) 48) 1041) 48) 0) 48) 1305670071624) 48) 90168543412224) 48) 0) 48) 13816976900096) 48) 571502231552) 48) 1310720) 48) 86016) 48) 146304975175680) 48) 18601746496) 48) 1095766528) 48) 0) 48) 123145302310912) 48) 8796093022208) 48) 274896343052) 48) 161628209284180) 48) 211243671486469) 48) 149610941126660) 48) 23094845505536) 48) 3848861122560) 48) 2217295753216) 48) 4263680) 48) 320) 48) 306450944)
def certWord211 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 805306368 48) 141784252416) 48) 1048576) 48) 983040) 48) 5516971474944) 48) 349101491200) 48) 135168) 48) 1650363208448) 48) 22315040) 48) 3645900883) 48) 3298535166978) 48) 35184372088832) 48) 8589935700) 48) 2336730644480) 48) 141733923985) 48) 40429333512192) 48) 41008381493248) 48) 4762047090688) 48) 297627943424) 48) 8929746944) 48) 6) 48) 50381088) 48) 52776558133248) 48) 6597069903049) 48) 35253091565568) 48) 8589934592) 48) 4563402752) 48) 100663296) 48) 863557910528) 48) 1179648) 48) 1091600384) 48) 1536) 48) 26393182285856) 48) 1)
def certWord212 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2269084981584 48) 13550638596096) 48) 0) 48) 58566207733760) 48) 24576) 48) 23761912832) 48) 6117518290944) 48) 8451) 48) 0) 48) 123145302310912) 48) 3298534906113) 48) 35253091571008) 48) 37391985280084) 48) 146372753883136) 48) 416645382144) 48) 6291456) 48) 196608) 48) 45056) 48) 228842405888) 48) 18589294656) 48) 786690) 48) 41154577712) 48) 17592186046545) 48) 3298535216257) 48) 35321829459340) 48) 20899310862336) 48) 268435477) 48) 79173427134465) 48) 57454318583808) 48) 553844736) 48) 4760990130176) 48) 297428714496) 48) 96) 48) 541331968)
def certWord213 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1108 48) 211243671486496) 48) 74844100100096) 48) 61581777960960) 48) 262144) 48) 381197225984) 48) 238937894486016) 48) 1485119504) 48) 92574208) 48) 18704) 48) 33) 48) 6) 48) 17798344478724) 48) 19791210452224) 48) 216811022843985) 48) 79242196942848) 48) 43989591916544) 48) 6064796073984) 48) 24576) 48) 23757718272) 48) 48) 48) 366146786053) 48) 0) 48) 17592186044416) 48) 4398046794816) 48) 35459250012176) 48) 19804094202624) 48) 212344256856085) 48) 79173460688896) 48) 3145728) 48) 17465081856) 48) 380123480064) 48) 160256098304) 48) 9999360000) 48) 15)
def certWord214 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1108 48) 2337535950929) 48) 84189965713408) 48) 846378041344) 48) 76192753385472) 48) 24576) 48) 512) 48) 671227968) 48) 571503809283) 48) 1) 48) 35184372187298) 48) 5497558138880) 48) 137438953472) 48) 25769803776) 48) 146304571277312) 48) 8869141020672) 48) 6291456) 48) 17196646400) 48) 24576) 48) 142943060480) 48) 18601746480) 48) 93065732) 48) 0) 48) 2181138) 48) 0) 48) 1030792159300) 48) 19799799235668) 48) 70507256971282) 48) 74848395067397) 48) 22544822304768) 48) 393216) 48) 28672) 48) 10551808) 48) 18593357888) 48) 299267)
def certWord215 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 141905719459840 48) 318767104) 48) 19922944) 48) 1310720) 48) 4402360352768) 48) 67174400) 48) 0) 48) 6) 48) 0) 48) 263882795205634) 48) 3298534883461) 48) 17592196091916) 48) 91276644974592) 48) 1610612741) 48) 158406983811072) 48) 2097152) 48) 983053) 48) 158711946412032) 48) 269550592) 48) 21483560960) 48) 8) 48) 34064) 48) 52779931552851) 48) 5497558145026) 48) 35184372109892) 48) 19808389170260) 48) 2336730644560) 48) 13546326851584) 48) 43218108416) 48) 393216) 48) 61440) 48) 353329349120) 48) 4198480) 48) 266499)
def certWord216 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1300 48) 141974438936576) 48) 100663296) 48) 6291456) 48) 89337769426944) 48) 5655417077760) 48) 139526656) 48) 21818843136) 48) 1343263232) 48) 2621984) 48) 35184372088865) 48) 2) 48) 17592186044420) 48) 18691697673492) 48) 141975244242944) 48) 416611827716) 48) 92368107732992) 48) 983040) 48) 34611200) 48) 139526144) 48) 5712650240) 48) 843846148) 48) 0) 48) 35184372088832) 48) 19791209452609) 48) 35321811042304) 48) 0) 48) 1610612817) 48) 79242146611200) 48) 19922944) 48) 52828399861760) 48) 24576) 48) 768) 48) 8458240) 48) 545027)
def certWord217 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 146303765970944 48) 100663296) 48) 8860467200) 48) 35718692864) 48) 4758859431936) 48) 160054772224) 48) 21483560992) 48) 2)
def certWord218 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1879048192 48) 18214956302340) 48) 92930746351616) 48) 51824820224) 48) 20480) 48) 76611584) 48) 135248) 48) 545025) 48) 83952928) 48) 0) 48) 1099511627778) 48) 17592186045836) 48) 19799799234560) 48) 0) 48) 13542098993152) 48) 279446552576) 48) 3775004672) 48) 20480) 48) 4352) 48) 8392704) 48) 545027) 48) 1552) 48) 87960930222113) 48) 4398046511237) 48) 17729624997896) 48) 1112396529664) 48) 211174952009781) 48) 70514773065732) 48) 92368104587264) 48) 0) 48) 3373281280) 48) 10739647232) 48) 128) 48) 528644)
def certWord219 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2268279603200 48) 13267170754560) 48) 554319216640) 48) 17901725941760) 48) 3239067648) 48) 4608) 48) 135184) 48) 1052930) 48) 4624) 48) 289) 48) 267266) 48) 35253091565568) 48) 247394411216896) 48) 268435456) 48) 234881024) 48) 60402171904) 48) 553713664) 48) 2232426496) 48) 210829312) 48) 135200) 48) 807168) 48) 34064) 48) 52776558133473) 48) 271617) 48) 35390530519040) 48) 25769803800) 48) 2336462209024) 48) 8869107466240) 48) 279443406848) 48) 3775004672) 48) 171834359808) 48) 2163712) 48) 128) 48) 266496)
def certWord220 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1879048192 48) 416611827713) 48) 4952634163200) 48) 51825147904) 48) 61440) 48) 1536) 48) 112) 48) 4) 48) 2576) 48) 35184372091921) 48) 2199023255617) 48) 17867063951360) 48) 247394411216897) 48) 9964860997632) 48) 13542031884288) 48) 1121256996864) 48) 196608) 48) 3306180608) 48) 10552320) 48) 16846896) 48) 8450) 48) 528) 48) 5247122) 48) 1099511627776) 48) 412316860420) 48) 18704582574080) 48) 2147483648) 48) 141767475200) 48) 6291456) 48) 553975808) 48) 20480) 48) 277938176) 48) 4264000) 48) 75506176)
def certWord221 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2147483648 48) 966401196032) 48) 3145728) 48) 17465344000) 48) 1091584000) 48) 18940672) 48) 8720416) 48) 18) 48) 16400) 48) 70368744177664) 48) 8796093022208) 48) 412316861056) 48) 37387690311768) 48) 71606500065333) 48) 79242196942848) 48) 829199220736) 48) 3848861122560) 48) 3306164224) 48) 6357248) 48) 13176848) 48) 8448) 48) 33040) 48) 87960930222080) 48) 18691697672192) 48) 68719476736) 48) 64424509440) 48) 216672510148608) 48) 18214989856768) 48) 7340032) 48) 88031025561600) 48) 2165321728) 48) 284811199488) 48) 18602074128) 48) 17)
def certWord222 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 532 48) 141974975807488) 48) 8869174575104) 48) 0) 48) 1627652096) 48) 3373289472) 48) 0) 48) 18052685840) 48) 24834) 48) 0) 48) 70368746489874) 48) 1099511627778) 48) 17729624999040) 48) 37396280246272) 48) 15463224442880) 48) 141801029632) 48) 8861515776) 48) 52898758656) 48) 168837120) 48) 69995726080) 48) 1208098816) 48) 18) 48) 50448) 48) 364690) 48) 3298534883529) 48) 17660905538128) 48) 230914621702145) 48) 68719476736) 48) 13198451277824) 48) 1104077127680) 48) 51824885760) 48) 0) 48) 68222976) 48) 397344) 48) 6)
def certWord223 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 5637144576 48) 1241295880196) 48) 22269942300672) 48) 69004951552) 48) 57344) 48) 202440960) 48) 921632) 48) 790791) 48) 1) 48) 17592186208482) 48) 5497558139009) 48) 17798344474636) 48) 89069031784448) 48) 1610612816) 48) 5025128513536) 48) 571499085824) 48) 69004886016) 48) 45056) 48) 2163456) 48) 96) 48) 528643) 48) 1296) 48) 52776558133248) 48) 0) 48) 1168231104512) 48) 25769803776) 48) 71538049024000) 48) 1241245548544) 48) 17825792) 48) 393216) 48) 3316807385088) 48) 6356992) 48) 4198448) 48) 790792)
def certWord224 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2268011167744 48) 17596481011712) 48) 8388608) 48) 553975808) 48) 12288) 48) 14745856) 48) 13497344000) 48) 8450) 48) 20201760) 48) 17592186408018) 48) 2199023255552) 48) 16) 48) 18691697672192) 48) 71536975282176) 48) 50331648) 48) 1048576) 48) 68736385024) 48) 1225785344) 48) 91270283776) 48) 272) 48) 0) 48) 1552) 48) 35184377333842) 48) 1099511646210) 48) 35253091565568) 48) 17179869184) 48) 805306368) 48) 691540066304) 48) 829200269312) 48) 34645213184) 48) 4488393928704) 48) 6457262336) 48) 1493770304) 48) 545024)
def certWord225 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 80333068304384 48) 13816909791232) 48) 43221254144) 48) 3775070208) 48) 32768) 48) 349101490688) 48) 12587024) 48) 19) 48) 50448) 48) 87960930222080) 48) 5497558138882) 48) 17798344474628) 48) 18691697672192) 48) 1610612737) 48) 140883550797827) 48) 92638686478336) 48) 3775004672) 48) 1091584000) 48) 23896129536) 48) 17532788800) 48) 24837) 48) 4624) 48) 0) 48) 19791209299978) 48) 17592186044416) 48) 8589934592) 48) 221070556659781) 48) 83915087806464) 48) 550025297920) 48) 17196974080) 48) 81920) 48) 4608) 48) 18597879808) 48) 1085696)
def certWord226 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2268279603200 48) 285212672) 48) 863557910528) 48) 51824885760) 48) 1074806784) 48) 68224000) 48) 4263968) 48) 6) 48) 0) 48) 105553116268561) 48) 2199023583497) 48) 35253091565568) 48) 55834574848) 48) 4831838208) 48) 17665200488448) 48) 97878546579456) 48) 553648128) 48) 20480) 48) 134283776) 48) 112) 48) 18) 48) 0) 48) 123145306588178) 48) 4398046511106) 48) 17729624997896) 48) 1103806595072) 48) 1610612736) 48) 13542065438720) 48) 26040336384) 48) 1179648) 48) 24576) 48) 68223744) 48) 16) 48) 893915650)
def certWord227 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 11064104189952 48) 1241312657408) 48) 2097152) 48) 553713664) 48) 34603008) 48) 6358272) 48) 4198464) 48) 7) 48) 1552) 48) 52776558135377) 48) 14) 48) 17798344474640) 48) 18691697672192) 48) 805306368) 48) 691523289088) 48) 1121258045440) 48) 917504) 48) 2165329920) 48) 512) 48) 240) 48) 624960002) 48) 0) 48) 35184375580754) 48) 136393) 48) 35459250000452) 48) 19804094201856) 48) 805306368) 48) 100663296) 48) 61598959927296) 48) 88014919434240) 48) 2148532224) 48) 202441984) 48) 921632) 48) 1343279620)
def certWord228 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1 48) 9965129433089) 48) 140883534020608) 48) 5242880) 48) 17465081856) 48) 24576) 48) 202441472) 48) 22355976208) 48) 790785) 48) 3600) 48) 2065) 48) 2199023278209) 48) 35390530519040) 48) 177021372071936) 48) 5368709120) 48) 141767475200) 48) 2097152) 48) 58583656038400) 48) 168837120) 48) 23824826880) 48) 135248) 48) 528644) 48) 33040) 48) 52776561625170) 48) 3298534883328) 48) 0) 48) 73014444032) 48) 1073741824) 48) 301989888) 48) 279443406848) 48) 6099155615744) 48) 4312793088) 48) 273744384) 48) 272) 48) 790785)
def certWord229 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1280 48) 146372485447680) 48) 141750697984) 48) 829199220736) 48) 6064795942912) 48) 16384) 48) 1536) 48) 17800699968) 48) 3) 48) 528) 48) 52776558133248) 48) 8796093022208) 48) 274877906944) 48) 247398706184193) 48) 9965129433088) 48) 416645382144) 48) 279441309696) 48) 553713664) 48) 2559836168192) 48) 768) 48) 135200) 48) 528640) 48) 49424) 48) 35184376630290) 48) 1099511627786) 48) 17798344474636) 48) 159437775962112) 48) 6666057678848) 48) 0) 48) 571501182976) 48) 553844736) 48) 168824832) 48) 68224000) 48) 32) 48) 24833)
def certWord230 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 88 48) 71606231629824) 48) 4471060955136) 48) 8388608) 48) 3775070208) 48) 8192) 48) 349176987904) 48) 8458272) 48) 0) 48) 34064) 48) 3073) 48) 4398046511104) 48) 893353198988) 48) 160537287589888) 48) 2269084909568) 48) 691523289088) 48) 829199220736) 48) 327680) 48) 2165317632) 48) 14745856) 48) 14294327312) 48) 790789) 48) 4624) 48) 33) 48) 1099511955653) 48) 35184372109328) 48) 160532992622592) 48) 1342177280) 48) 4471111286784) 48) 1138434768896) 48) 76193022083072) 48) 5585623851008) 48) 297561883136) 48) 403578944) 48) 266496)
def certWord231 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 72 48) 2336999079936) 48) 966384418816) 48) 8859418624) 48) 1376256) 48) 4762063880192) 48) 210829568) 48) 1489051664) 48) 1069314) 48) 16656) 48) 35184372090961) 48) 2199023255749) 48) 17729624997888) 48) 64424509440) 48) 221070556659716) 48) 141433289834499) 48) 40137006252032) 48) 983040) 48) 4761057230848) 48) 143018558720) 48) 1208098832) 48) 1095799296) 48) 69501216) 48) 52776558133409) 48) 257) 48) 17798344474624) 48) 12884902964) 48) 146372753883136) 48) 13267153977344) 48) 0) 48) 2701197312) 48) 4762198097920) 48) 6444679168) 48) 659472) 48) 41951745)
def certWord232 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 221071630401536 48) 285212672) 48) 6291456) 48) 17465147392) 48) 382270967808) 48) 2048) 48) 8458320) 48) 1162351105) 48) 72663328) 48) 17592186044416) 48) 192) 48) 17867063951364) 48) 18704582574080) 48) 141905719459840) 48) 966401196032) 48) 19922944) 48) 327680) 48) 5655417077760) 48) 2163200) 48) 48) 48) 528640) 48) 0) 48) 70368744472610) 48) 1099511627841) 48) 17935783428096) 48) 247394411216896) 48) 1342177280) 48) 4471144841216) 48) 554320265216) 48) 76195169370112) 48) 4096) 48) 14746368) 48) 135184) 48) 1112543744)
def certWord233 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 292 48) 71606231629824) 48) 13267237863424) 48) 8863612928) 48) 1114112) 48) 61440) 48) 4608) 48) 64) 48) 93327873) 48) 0) 48) 52776558133248) 48) 4398046511104) 48) 137438953472) 48) 36283883716608) 48) 2268011167744) 48) 4471144841216) 48) 43221254144) 48) 58584729649152) 48) 28672) 48) 80806144) 48) 659488) 48) 524544) 48) 55837216) 48) 17592186046545) 48) 0) 48) 1305670057996) 48) 159442070929408) 48) 1610612736) 48) 9143985373184) 48) 4194304) 48) 553648128) 48) 24576) 48) 2163200) 48) 12914736) 48) 299267)
def certWord234 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 11064372625408 48) 285212672) 48) 1104077127680) 48) 51825082368) 48) 3239055360) 48) 0) 48) 921632) 48) 266499) 48) 0) 48) 263882795205650) 48) 3298534883393) 48) 17729624997888) 48) 25769803776) 48) 1342177280) 48) 18214973079552) 48) 26039287808) 48) 71152238592) 48) 34619392) 48) 10551552) 48) 17371136) 48) 92803588) 48) 1) 48) 52776558133281) 48) 5497558139008) 48) 17867063951372) 48) 18695992639488) 48) 221070825095235) 48) 88038306742277) 48) 1155887267840) 48) 54202789265408) 48) 382472294400) 48) 349101491200) 48) 272) 48) 6)
def certWord235 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2268548038656 48) 141817806848) 48) 550029492224) 48) 553975808) 48) 235937792) 48) 202440960) 48) 12652544) 48) 3) 48) 528) 48) 70368744180753) 48) 1099511627778) 48) 17935783428108) 48) 18704582574080) 48) 141906793201717) 48) 70514773065728) 48) 8863612928) 48) 6101303099392) 48) 3222294528) 48) 1792) 48) 12652624) 48) 2) 48) 0) 48) 105553116266496) 48) 2199023539202) 48) 35184372088832) 48) 106652627894272) 48) 71536975282180) 48) 141433340166144) 48) 0) 48) 87996665954304) 48) 8192) 48) 2163712) 48) 8458352) 48) 786688)
def certWord236 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 24 48) 11132555231232) 48) 13542115770368) 48) 7340032) 48) 34644951040) 48) 3456393809920) 48) 2162944) 48) 96) 48) 92819972) 48) 0) 48) 17592186406994) 48) 0) 48) 137438953472) 48) 30064771072) 48) 0) 48) 134217733) 48) 1138705301504) 48) 53972631552) 48) 2559836176384) 48) 2163200) 48) 1493508112) 48) 3) 48) 33040) 48) 35184376369362) 48) 4398046511104) 48) 1374389534728) 48) 1103806595072) 48) 19859928776704) 48) 18489850986496) 48) 8861515776) 48) 3775070208) 48) 3239071744) 48) 4608) 48) 17532264448) 48) 1048832)
def certWord237 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 301989888 48) 8860467200) 48) 1649837867008) 48) 240688037888) 48) 256) 48) 304) 48) 266498) 48) 5834016) 48) 70368744177697) 48) 2199023255685) 48) 17798344484160) 48) 37383395345236) 48) 2337267515392) 48) 9143985373184) 48) 1104076079104) 48) 1114112) 48) 381331443712) 48) 269550336) 48) 8720384) 48) 545027) 48) 2576) 48) 52776558133281) 48) 3298534883334) 48) 17729624997888) 48) 36301063586837) 48) 1237219016704) 48) 50331648) 48) 8859418624) 48) 1651985416192) 48) 1091588096) 48) 1024) 48) 128) 48) 545028)
def certWord238 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2268816474112 48) 285212672) 48) 60399026176) 48) 65536) 48) 101711872) 48) 289039057920) 48) 135216) 48) 8450) 48) 16656) 48) 35184372089057) 48) 2) 48) 17867063951360) 48) 12884902484) 48) 2336462209024) 48) 17665200488448) 48) 846376992768) 48) 6100229554176) 48) 2165325824) 48) 5120) 48) 8458272) 48) 57602) 48) 51472) 48) 17592186048529) 48) 9) 48) 17729625002056) 48) 19795504267796) 48) 221139544571937) 48) 79242146611200) 48) 60401123328) 48) 553713664) 48) 2148548608) 48) 10552576) 48) 4263936) 48) 790786)
def certWord239 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 141905987895296 48) 13267204308992) 48) 1104075030528) 48) 196608) 48) 32768) 48) 269550336) 48) 135168) 48) 73984) 48) 85229856) 48) 17592189340690) 48) 2199023255680) 48) 17935783428104) 48) 18700287606784) 48) 70438000525312) 48) 285212672) 48) 846378041344) 48) 553713664) 48) 28672) 48) 282132736) 48) 135200) 48) 76042757) 48) 33040) 48) 33) 48) 3298535167105) 48) 35253091565568) 48) 36283883716608) 48) 1879048192) 48) 117440515) 48) 40411885207552) 48) 39857867259904) 48) 5500932456448) 48) 135333120) 48) 32) 48) 786688)
def certWord240 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2268816474112 48) 691523289088) 48) 1104077127680) 48) 553910272) 48) 2232430592) 48) 512) 48) 8720400) 48) 545029) 48) 51472) 48) 35184372089873) 48) 1099511627778) 48) 17660905521152) 48) 85899345920) 48) 6667131420672) 48) 8800421543936) 48) 60400074752) 48) 0) 48) 309273313280) 48) 1280) 48) 96) 48) 8450) 48) 1) 48) 52776558133248) 48) 7696581394434) 48) 17867063969088) 48) 37400575213568) 48) 2268816474112) 48) 8869191352320) 48) 8863612928) 48) 393216) 48) 2232426496) 48) 10551808) 48) 135248) 48) 41218)
def certWord241 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2268548038656 48) 8869141020672) 48) 571499085824) 48) 1179648) 48) 382270971904) 48) 1280) 48) 13233627136) 48) 807172) 48) 51691808) 48) 35184373155858) 48) 3298534883328) 48) 206158430208) 48) 36292473651200) 48) 268435456) 48) 141801029632) 48) 97071092727808) 48) 393216) 48) 34607104) 48) 68223232) 48) 8458240) 48) 266497) 48) 33040) 48) 3089) 48) 5497558139073) 48) 17935783428096) 48) 17179869184) 48) 146303765970944) 48) 691556843524) 48) 58004074397696) 48) 262144) 48) 2165325824) 48) 202440960) 48) 8720384) 48) 8448)
def certWord242 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 216673315454976 48) 141750697984) 48) 79994308001792) 48) 1179648) 48) 34619392) 48) 277938176) 48) 16) 48) 1162367488) 48) 528) 48) 52776558137345) 48) 133) 48) 17729624997896) 48) 18691697672192) 48) 1610612736) 48) 17665250820096) 48) 279441309696) 48) 55302300958720) 48) 34607104) 48) 10551296) 48) 8458320) 48) 790787) 48) 33040) 48) 17592186044641) 48) 4398046533697) 48) 35321811042312) 48) 1108101563444) 48) 212343451549696) 48) 9144002150400) 48) 554321313792) 48) 553713664) 48) 5518045233152) 48) 3328) 48) 921680) 48) 8453)
def certWord243 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2268011167744 48) 141733920768) 48) 0) 48) 52898562048) 48) 34611200) 48) 211675119872) 48) 135216) 48) 8450) 48) 528) 48) 70368744177664) 48) 2199023255562) 48) 17798344474624) 48) 106661217830144) 48) 146372753883136) 48) 416611827712) 48) 2097152) 48) 19612696576) 48) 303046656) 48) 10551296) 48) 1183744) 48) 1342722563) 48) 528) 48) 35184372089057) 48) 1099511627794) 48) 17798344474632) 48) 18713172508672) 48) 141907061637120) 48) 8869141020672) 48) 43223351296) 48) 17196777472) 48) 69632) 48) 1536) 48) 13176912) 48) 1102084)
def certWord244 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 71537243717632 48) 100663300) 48) 92913564385280) 48) 553713664) 48) 168837120) 48) 1280) 48) 16) 48) 8448) 48) 528) 48) 87960930222080) 48) 8796093022409) 48) 17592186044416) 48) 36305358553088) 48) 1073741824) 48) 416645382144) 48) 8860467200) 48) 35718889472) 48) 34623488) 48) 2163200) 48) 21818843152) 48) 8) 48) 16656) 48) 35184373285906) 48) 2199023255685) 48) 17729624997888) 48) 177042846908456) 48) 2337804386304) 48) 33554432) 48) 8863612928) 48) 3775201280) 48) 28672) 48) 14746112) 48) 4370538528) 48) 823557)
def certWord245 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1108 48) 2336462209027) 48) 141433323388928) 48) 0) 48) 6118483165184) 48) 101711872) 48) 14745856) 48) 5704392704) 48) 266501) 48) 528) 48) 17592186044449) 48) 1099511627778) 48) 17798344474636) 48) 18708877541377) 48) 1168231104512) 48) 201326592) 48) 554321313792) 48) 1310720) 48) 3385526857728) 48) 18940160) 48) 135168) 48) 8450) 48) 528) 48) 35184372089057) 48) 5497558340749) 48) 35253091565572) 48) 1099511627776) 48) 11064104189952) 48) 9144018927616) 48) 6291456) 48) 458752) 48) 34603008) 48) 5120) 48) 921632) 48) 1342722561)
def certWord246 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1610612736 48) 16777221) 48) 22854062047232) 48) 553779200) 48) 3239063552) 48) 353463566592) 48) 135184) 48) 2) 48) 33040) 48) 17592186044416) 48) 7696581394434) 48) 17660905521152) 48) 36296768618496) 48) 2267742732288) 48) 285212672) 48) 279444455424) 48) 34645147648) 48) 303038464) 48) 349101490176) 48) 12652608) 48) 41217) 48) 34064) 48) 35184372092929) 48) 3298534883330) 48) 17867063951360) 48) 30064771072) 48) 146303765970944) 48) 141733920768) 48) 863561056256) 48) 4950520299520) 48) 3373289472) 48) 67175680) 48) 659456) 48) 823556)
def certWord247 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 24 48) 11133360537600) 48) 4471060955136) 48) 846378041344) 48) 1627389952) 48) 5516971474944) 48) 2048) 48) 135200) 48) 37123) 48) 2576) 48) 87960930222113) 48) 3298534883529) 48) 17867063951372) 48) 89081916687381) 48) 10033312038912) 48) 416611827712) 48) 26038239232) 48) 6083049422848) 48) 5499791609856) 48) 134283776) 48) 135184) 48) 1052928) 48) 1552) 48) 35184372088865) 48) 3298534901770) 48) 35253091565580) 48) 159429186027520) 48) 2268548038656) 48) 141733920768) 48) 2097152) 48) 393216) 48) 382270967808) 48) 268501760) 48) 16) 48) 306450944)
def certWord248 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 8869124243456 48) 26431766659072) 48) 524288) 48) 1091579904) 48) 2048) 48) 96) 48) 8448) 48) 86294816) 48) 17592186046545) 48) 3298534883328) 48) 274877906944) 48) 36283883716608) 48) 2268011167744) 48) 416695713792) 48) 26397405872128) 48) 53972369408) 48) 69632) 48) 135331840) 48) 128) 48) 3) 48) 528) 48) 17592187111442) 48) 3298534883521) 48) 17729624997892) 48) 18700287606784) 48) 5368709120) 48) 4471144841216) 48) 60397977600) 48) 553844736) 48) 103249088512) 48) 2162944) 48) 135216) 48) 356524548)
def certWord249 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 5368709120 48) 8869141020672) 48) 3145728) 48) 553648128) 48) 4096) 48) 139526144) 48) 135200) 48) 823557) 48) 68436256) 48) 17592186044416) 48) 22593) 48) 35459249995792) 48) 18691697672192) 48) 216673852325888) 48) 691573620736) 48) 554323410944) 48) 89369981681664) 48) 34607104) 48) 343736976128) 48) 1493245968) 48) 843846149) 48) 4624) 48) 70368744180881) 48) 1099511627786) 48) 17935783429512) 48) 90168543412224) 48) 1610612736) 48) 141750697984) 48) 20971520) 48) 553844736) 48) 34611200) 48) 2163712) 48) 4370538512) 48) 826544642)
def certWord250 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2268011167744 48) 9144018927616) 48) 554321313792) 48) 553713664) 48) 34619392) 48) 1536) 48) 135232) 48) 545027) 48) 51472) 48) 87960930222080) 48) 2) 48) 17935783428096) 48) 36301063586816) 48) 146373827625029) 48) 70514840174592) 48) 97311611944960) 48) 553910272) 48) 34619392) 48) 2162944) 48) 135168) 48) 266496) 48) 528) 48) 17592186044449) 48) 1099511627778) 48) 17798344474624) 48) 25769803776) 48) 5) 48) 149610941120512) 48) 26038239232) 48) 553779200) 48) 34607104) 48) 2163968) 48) 4370538512) 48) 6)
def certWord251 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 141906524766208 48) 9144018927616) 48) 8859418624) 48) 553844736) 48) 34603008) 48) 5120) 48) 13176848) 48) 528642) 48) 0) 48) 105553116266529) 48) 2199023255749) 48) 17935783428104) 48) 18691697672192) 48) 5368709120) 48) 13816976900096) 48) 571501182976) 48) 553713664) 48) 382270963712) 48) 768) 48) 135216) 48) 823556) 48) 72647968) 48) 17592186044449) 48) 1099511627776) 48) 412316860416) 48) 36292473651200) 48) 2268816474178) 48) 83640277008384) 48) 97328792862720) 48) 553975808) 48) 34607104) 48) 256) 48) 135248) 48) 545026)
def certWord252 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 33 48) 4398046778569) 48) 35527969472512) 48) 36288178683904) 48) 2268011167744) 48) 141801029636) 48) 92368105635840) 48) 553975808) 48) 34611200) 48) 210830336) 48) 135200) 48) 8453) 48) 528) 48) 17592186044449) 48) 5497558138882) 48) 17867063951360) 48) 25769805076) 48) 221139544571904) 48) 9144035704832) 48) 0) 48) 553844736) 48) 34615296) 48) 2162944) 48) 21823561744) 48) 8450)
def certWord253 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1073741824 48) 0) 48) 2097152) 48) 196608) 48) 0) 48) 10551296) 48) 240) 48) 1085699) 48) 66832) 48) 97) 48) 1099511627776) 48) 68719476736) 48) 55834574848) 48) 71537243717632) 48) 117440512) 48) 279443406848) 48) 262144) 48) 0) 48) 18940928) 48) 8458304) 48) 4) 48) 0) 48) 52776558133248) 48) 2199023255749) 48) 17798344474624) 48) 12884901888) 48) 71537512153088) 48) 83886080) 48) 1048576) 48) 196608) 48) 16384) 48) 512) 48) 80) 48) 823552)
def certWord254 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1073741824 48) 33554432) 48) 0) 48) 65536) 48) 4312801280) 48) 512) 48) 64) 48) 8448) 48) 0) 48) 17592186044577) 48) 257) 48) 17729624997888) 48) 0) 48) 216672778584064) 48) 8869174575104) 48) 863560007680) 48) 0) 48) 4096) 48) 1024) 48) 32) 48) 7) 48) 49424) 48) 52776558133248) 48) 1099511627776) 48) 206158430208) 48) 36288178683904) 48) 805306368) 48) 33554432) 48) 863557910528) 48) 71152304128) 48) 1091571712) 48) 1280) 48) 16846864) 48) 1102084)
def certWord255 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 268435456 48) 83886080) 48) 77578895360) 48) 3775004672) 48) 168824832) 48) 10552064) 48) 0) 48) 1) 48) 0) 48) 70368744177889) 48) 18) 48) 17592186044424) 48) 89069031784449) 48) 1168231104512) 48) 134217728) 48) 5242880) 48) 553975808) 48) 8192) 48) 512) 48) 272) 48) 0) 48) 0) 48) 52776558133248) 48) 1099511627776) 48) 16) 48) 89064736817152) 48) 1342177280) 48) 0) 48) 1048576) 48) 51824951296) 48) 34619392) 48) 135333120) 48) 0) 48) 4)
def certWord256 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 146303765970944 48) 318767104) 48) 2097152) 48) 553713664) 48) 4096) 48) 210829568) 48) 135200) 48) 41217) 48) 0) 48) 35184372088865) 48) 0) 48) 412316860416) 48) 25769803776) 48) 0) 48) 141767475200) 48) 5242880) 48) 71152238592) 48) 0) 48) 68222976) 48) 16) 48) 266498) 48) 4624) 48) 17592186048593) 48) 1099511627909) 48) 17867063951360) 48) 12884901888) 48) 221070556659712) 48) 33554432) 48) 77580992512) 48) 4848615424) 48) 8192) 48) 10551552) 48) 16) 48) 1069313)
def certWord257 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 11065177931776 48) 17665217265664) 48) 2097152) 48) 65536) 48) 16384) 48) 202441216) 48) 112) 48) 5) 48) 0) 48) 0) 48) 4398046511104) 48) 68719476736) 48) 0) 48) 2267742732288) 48) 141750697984) 48) 313801048064) 48) 53972369408) 48) 16384) 48) 1280) 48) 16) 48) 1052932) 48) 0) 48) 35184372088832) 48) 2199023255552) 48) 343597383680) 48) 21474836480) 48) 2267742732288) 48) 117440512) 48) 8859418624) 48) 553648128) 48) 3373273088) 48) 1024) 48) 80) 48) 8452)
def certWord258 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 36288178683904 48) 2268816474112) 48) 141767475200) 48) 4194304) 48) 0) 48) 12288) 48) 2162688) 48) 8720384) 48) 4) 48) 0) 48) 87960930224145) 48) 2) 48) 17935783428108) 48) 159450660864000) 48) 805306368) 48) 141801029632) 48) 1048576) 48) 1179648) 48) 0) 48) 0) 48) 80) 48) 1)
def certWord259 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 83886080 48) 0) 48) 65536) 48) 4096) 48) 256) 48) 32) 48) 2)

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def mask256 : Nat := 2 ^ 256 - 1

def negD (d w : Nat) : Nat := (w ^^^ mask256) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then orD d a b else andD d a b

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      negD d a ≠ 0 → negD d a ≠ d → negD d a ∉ (a :: r) →
      P s (negD d a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (if c then andD d a b else orD d a b) ≠ 0 →
      (if c then andD d a b else orD d a b) ≠ d →
      (if c then andD d a b else orD d a b) ∉ (a :: b :: r) →
      P s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {d y : Nat}

theorem Run.done : RunD d y 0 [y] := fun _ dn _ _ _ => dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD d y s xs) :
    RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
theorem Run.one {s a r} (save : Bool)
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
    (h : RunD d y s (negD d a :: kept save a r)) :
    RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
theorem Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then andD d a b else orD d a b) ≠ 0)
    (hd : (if c then andD d a b else orD d a b) ≠ d)
    (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
    (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))) :
    RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

theorem Run.fold {P : ∀ t ws, RunD d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
      (h : RunD d y s (negD d a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h0 hd hm h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h0 : (if c then andD d a b else orD d a b) ≠ 0)
      (hd : (if c then andD d a b else orD d a b) ≠ d)
      (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
      (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h0 hd hm h))
    {t ws} (h : RunD d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunD d y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k h0 hd hm ⟨h', ih⟩ => ⟨Run.one k h0 hd hm h', one k h0 hd hm h' ih⟩)
    (fun c a b h0 hd hm ⟨h', ih⟩ => ⟨Run.two c a b h0 hd hm h', two c a b h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem run_len {d y s xs} (h : RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem zero_done {d y t ws} (h : RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def isConstB (d w : Nat) : Bool := (w &&& d == 0) || (w &&& d == d)

theorem isConstB_iff (d w : Nat) : isConstB d w = true ↔ IsConst d w := by
  simp [isConstB, IsConst]

def Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def availB (d : Nat) (bank : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || bank.any (fun v => (v &&& d) == m)

theorem availB_iff (d : Nat) (bank : List Nat) (w : Nat) :
    availB d bank w = true ↔ Avail d bank w := by
  simp [availB, Avail, IsConst, or_assoc]

def NatReach (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    (∃ b a, bank = negD d a :: b ∧ NatReach d roots p b ∧ Avail d b a) ∨
    (∃ b a c op, bank = binD d op a c :: b ∧ NatReach d roots p b ∧ Avail d b a ∧ Avail d b c)

def Lower (d : Nat) (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, NatReach d roots p bank → Avail d bank T → L ≤ p

theorem mask256_bit (i : Nat) : mask256.testBit i = decide (i < 256) := by
  rw [mask256, Nat.testBit_two_pow_sub_one]

theorem negD_and_sub {d d1 : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d) (a : Nat) :
    negD d1 a &&& d = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [negD, Nat.testBit_and, Nat.testBit_xor] at *
  cases hi : d.testBit i <;> simp_all

theorem andD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    andD d1 a b &&& d = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [andD, Nat.testBit_and] at *
  cases hi : d.testBit i <;> simp_all

theorem orD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    orD d1 a b &&& d = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [orD, Nat.testBit_and, Nat.testBit_or] at *
  cases hi : d.testBit i <;> simp_all

theorem negD_const {d : Nat} (hd : d &&& mask256 = d) {a : Nat} (hc : IsConst d a) :
    IsConst d (negD d a) := by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i := congrArg (fun v => v.testBit i) h0
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i := congrArg (fun v => v.testBit i) h1
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : IsConst d a) :
    (binD d op a b &&& d = 0) ∨ (binD d op a b &&& d = d) ∨ (binD d op a b &&& d = b &&& d) := by
  rcases hc with h0 | h1
  · cases op
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, andD, Nat.testBit_and, Nat.zero_testBit, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, andD, Nat.testBit_and, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_comm (d : Nat) (op : Bool) (a b : Nat) : binD d op a b = binD d op b a := by
  cases op <;> simp [binD, andD, orD, Nat.and_comm, Nat.or_comm]

theorem avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail d bank w) :
    Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail d bank v) : Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩

theorem countP_kept_ge {α : Type} (p : α → Bool) (b : Bool) (a : α) (xs : List α) :
    xs.countP p ≤ (kept b a xs).countP p := by
  cases b <;> simp [kept, List.countP_cons] <;> split <;> omega

theorem contraction {d d1 T : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD d1 T s ws) {roots p bank}
    (hp : NatReach d roots p bank) (hs : ∀ w ∈ ws, Avail d bank w) :
    ∃ q next, NatReach d roots q next ∧ Avail d next T ∧
      q + ws.countP (isConstB d) ≤ p + s := by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false := by
      cases hc : isConstB d T with
      | false => rfl
      | true => exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p, bank, hp, hs T (by simp), by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q, next, hq, ht, hle⟩ := ih hp (fun w hw => hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q, next, hq, ht, hle⟩
  | @one s a r save _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    by_cases hca : IsConst d a
    · have hc_neg : IsConst d (negD d1 a) := by
        have e := negD_and_sub hd hsub a
        rcases negD_const hd hca with h0 | h1
        · exact Or.inl (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h0))
        · exact Or.inr (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h1))
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact Or.inl hc_neg
        · exact hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw])
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have h1 : isConstB d (negD d1 a) = true := (isConstB_iff _ _).2 hc_neg
      have h2 : isConstB d a = true := (isConstB_iff _ _).2 hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h1, h2, ite_true] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hreach' : NatReach d roots (p + 1) (negD d a :: bank) := Or.inl ⟨bank, a, rfl, hp, ha⟩
      have hneg_av : Avail d (negD d a :: bank) (negD d1 a) :=
        Or.inr ⟨negD d a, List.mem_cons_self, by rw [negD_and_sub hd hsub a]; simp [negD, Nat.and_assoc, Nat.and_self]⟩
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d (negD d a :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hneg_av
        · exact avail_cons _ _ (hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw]))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have h2 : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd ((isConstB_iff _ _).1 h) hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h2, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
  | @two s a b r conj ka kb _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    have hb := hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1 := if conj then andD d1 a b else orD d1 a b
    set z0 := binD d (!conj) a b
    have hz_eq : z1 &&& d = z0 &&& d := by
      cases conj
      · simp only [z1, z0, Bool.false_eq_true, ite_false, Bool.not_false, binD, ite_true]
        rw [orD_and_sub hsub]; simp [orD, Nat.and_assoc, Nat.and_self]
      · simp only [z1, z0, ite_true, Bool.not_true, Bool.false_eq_true, binD, ite_false]
        rw [andD_and_sub hsub]; simp [andD, Nat.and_assoc, Nat.and_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail d bank z1 := by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases binD_const_left (!conj) hca with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
        · dsimp only [z0]; rw [binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0) := by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true := (isConstB_iff _ _).2 hca
          rcases binD_const_left (!conj) hca with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1, hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b := by
              simp only [isConstB, hz_eq.trans he]
            simp [ha1, hzb]
        · have hb1 : isConstB d b = true := (isConstB_iff _ _).2 hcb
          have hz_eq' : z1 &&& d = binD d (!conj) b a &&& d := by rw [hz_eq, binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1, hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a := by
              simp only [isConstB, hz_eq'.trans he]
            simp [hb1, hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hna : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false := by
        cases h : isConstB d b with | false => rfl | true => exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach' : NatReach d roots (p + 1) (z0 :: bank) := Or.inr ⟨bank, a, b, !conj, rfl, hp, ha, hb⟩
      have hz_av : Avail d (z0 :: bank) z1 := Or.inr ⟨z0, List.mem_cons_self, hz_eq.symm⟩
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d (z0 :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons, hna, hnb, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩

theorem mask_idemp (d w : Nat) : (w &&& d) &&& d = w &&& d := by
  simp [Nat.and_assoc, Nat.and_self]

theorem negD_mask (d a : Nat) : negD d (a &&& d) = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

theorem andD_mask (d a b : Nat) : andD d (a &&& d) (b &&& d) = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD, Nat.testBit_and]
  cases d.testBit i <;> simp

theorem orD_mask (d a b : Nat) : orD d (a &&& d) (b &&& d) = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

theorem pull_one {d Y k ws} (hd : d &&& mask256 = d) (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a : Nat} (ha : Avail d b a) (hsub : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := negD d a
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hc
        rcases negD_const hd hc with h0 | h1
        · exact hzp.1 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h0)
        · exact hzp.2 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h1)
      obtain ⟨v, hv, hve⟩ := ha.resolve_left ha_nc
      set a' := a &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨v, hv, hve⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : negD d a' = z := negD_mask d a
      have h1 : RunD d Y k (negD d a' :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      have hne0 : negD d a' ≠ 0 := ez.symm ▸ hzp.1
      have hned : negD d a' ≠ d := ez.symm ▸ hzp.2
      by_cases ham : a' ∈ rest
      · have hp2 : rest.Perm (a' :: rest.erase a') := List.perm_cons_erase ham
        have h2 : RunD d Y k (negD d a' :: kept true a' (rest.erase a')) :=
          Run.perm (hp2.cons _) h1
        have hnm : negD d a' ∉ (a' :: rest.erase a') := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase (List.mem_of_mem_erase hm)
        refine ⟨k + 1, rest, le_rfl, hrest_nd, hrest_prop, hrest_sub, ?_⟩
        exact Run.perm hp2.symm (Run.one true hne0 hned hnm h2)
      · have h2 : RunD d Y k (negD d a' :: kept false a' rest) := h1
        have hnm : negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, Run.one false hne0 hned hnm h2⟩
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_prop
          · exact hrest_prop w hw
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_mem
          · exact hrest_sub w hw
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem pull_two {d Y k ws} (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a c : Nat} (op : Bool) (ha : Avail d b a) (hc : Avail d b c)
    (hsub : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := binD d op a c
  have hz_mask : z &&& d = z := by cases op <;> simp [z, binD, andD, orD, Nat.and_assoc, Nat.and_self]
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hca
        rcases binD_const_left op hca with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans h0)
        · exact hzp.2 (hz_mask.symm.trans h1)
        · rcases hc with hcc | ⟨v, hv, hve⟩
          · rcases hcc with h0 | h1
            · exact hzp.1 (hz_mask.symm.trans (he.trans h0))
            · exact hzp.2 (hz_mask.symm.trans (he.trans h1))
          · exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he.symm.trans hz_mask)⟩)
      have hc_nc : ¬ IsConst d c := by
        intro hcc
        have hz' : z = binD d op c a := binD_comm d op a c
        rcases binD_const_left op hcc with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans (by rw [hz']; exact h0))
        · exact hzp.2 (hz_mask.symm.trans (by rw [hz']; exact h1))
        · rcases ha with hca | ⟨v, hv, hve⟩
          · exact absurd hca ha_nc
          · have he' : z &&& d = a &&& d := hz'.symm ▸ he
            exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he'.symm.trans hz_mask)⟩)
      obtain ⟨va, hva, hvae⟩ := ha.resolve_left ha_nc
      obtain ⟨vc, hvc, hvce⟩ := hc.resolve_left hc_nc
      set a' := a &&& d
      set c' := c &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨va, hva, hvae⟩
      have hc'_mem : c' ∈ b.map (· &&& d) := List.mem_map.2 ⟨vc, hvc, hvce⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d := ⟨fun e => hc_nc (Or.inl e), fun e => hc_nc (Or.inr e)⟩
      have hne_ac : a' ≠ c' := by
        intro heq
        dsimp only [a', c'] at heq
        have hz_eq : z = a' := by
          cases op
          · simp only [z, binD, Bool.false_eq_true, ite_false]; rw [← andD_mask, ← heq]; simp [andD, a', Nat.and_assoc, Nat.and_self]
          · simp only [z, binD, ite_true]; rw [← orD_mask, ← heq]; simp [orD, a', Nat.and_assoc, Nat.and_self]
        exact hzb (hz_eq ▸ ha'_mem)
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : (if !op then andD d a' c' else orD d a' c') = z := by
        cases op
        · simp [z, binD, a', c', andD_mask]
        · simp [z, binD, a', c', orD_mask]
      have h1 : RunD d Y k ((if !op then andD d a' c' else orD d a' c') :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      set ka := decide (a' ∈ rest)
      set kb := decide (c' ∈ rest)
      set tail := (rest.erase a').erase c'
      have htail_nd : tail.Nodup := (hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail := by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail := (hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail := by
        rw [mem_kept]; rintro (⟨_, h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) := by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept, mem_kept, (hrest_nd.erase a').mem_erase_iff, hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka, kb]
      have h2 := Run.perm (hrest_perm.cons _) h1
      have hne0 : (if !op then andD d a' c' else orD d a' c') ≠ 0 := ez.symm ▸ hzp.1
      have hned : (if !op then andD d a' c' else orD d a' c') ≠ d := ez.symm ▸ hzp.2
      have hnm : (if !op then andD d a' c' else orD d a' c') ∉ (a' :: c' :: tail) := by
        rw [ez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (e ▸ ha'_mem)
        · exact hzb (e ▸ hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD d Y (k + 1) (a' :: c' :: tail) := Run.two (!op) ka kb hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac, hna_tail], List.nodup_cons.2 ⟨hnc_tail, htail_nd⟩⟩
      refine ⟨k + 1, a' :: c' :: tail, le_rfl, hnd3, ?_, ?_, h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem reach_to_run_aux {d : Nat} {roots : List Nat} {p bank} (hd : d &&& mask256 = d)
    (hr : NatReach d roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (· &&& d)) → RunD d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ roots.map (· &&& d)) ∧ RunD d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_one hd hnd hprop hrun ha hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩
    · have hsub' : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw
        have ez : binD d op a c &&& d = binD d op a c := by cases op <;> simp [binD, andD, orD, Nat.and_assoc, Nat.and_self]
        simpa [List.map_cons, ez] using this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_two hnd hprop hrun op ha hc hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem reach_to_run {d : Nat} {roots : List Nat} {T : Nat} {p bank} (hd : d &&& mask256 = d)
    (hnc : ¬ IsConst d T) (hr : NatReach d roots p bank) (ha : Avail d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ roots.map (· &&& d)) ∧ RunD d (T &&& d) s ws := by
  obtain ⟨v, hv, hve⟩ := ha.resolve_left hnc
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (· &&& d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsub Run.done
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

theorem runD_bits {d y s ws} (hd : d &&& mask256 = d) (h : RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : mask256.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self
    intro w hm; cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
    · rcases hm with rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hm with rfl | rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; cases conj <;> cases ka <;> cases kb <;>
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm <;>
      rcases hm with rfl | hr <;>
      first | simp [andD, orD, ha, hb, hi, hj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem runD_bits_le {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (hp.length_eq.trans hl) (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at hm
    rcases hm with rfl | hr
    · cases conj <;> simp only [andD, orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · exact hw _ (by simp [hr])

theorem lower_base {d : Nat} {roots : List Nat} {T : Nat} (h : availB d roots T = false) :
    Lower d roots T 1 := by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht := (availB_iff d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p => omega

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_zero (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) : moveBits tag d 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK256 (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) && (moveBits p.1 p.2 mask256 == mask256)

theorem applyMoves_hom (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b, applyMoves ms (a &&& b) = applyMoves ms a &&& applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ||| b) = applyMoves ms a ||| applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ^^^ b) = applyMoves ms a ^^^ applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256 := by
  induction ms with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    obtain ⟨⟨hz, hm⟩, hps⟩ := hok
    obtain ⟨hand, hor, hxor, h0, h256⟩ := ih hps
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves, List.foldl_cons, move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves, List.foldl_cons, hm]; exact h256

theorem move_invol (tag d w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1, ite_true, moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false := by
      have htd := congrArg (fun v : Nat => v.testBit (d + i)) h
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at htd
      have hge : d ≤ d + i := Nat.le_add_right d i
      have hsub : d + i - d = i := Nat.add_sub_cancel_left d i
      simp [hge, hsub, h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true := by
      simp [Nat.testBit_shiftLeft, Nat.le_add_right, Nat.add_sub_cancel_left, h1]
    simp [h2, h3, Nat.add_sub_cancel_left]
  · simp only [h1, ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2, ite_true, moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      simp [h2.2, Nat.add_sub_of_le h2.1]
    · simp [h1, h2, moved tag d i w h]

theorem applyMoves_inj (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms) := by
  induction ms with
  | nil => intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves, List.foldl_cons] at h
    have h1 := ih hok.2 h
    have := congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1, move_invol p.1 p.2 b hok.1.1] at this

theorem applyMoves_runD {d Y s} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD d Y s ws) :
    RunD d Y s (ws.map (applyMoves ms)) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hinj := applyMoves_inj ms hok
  have hneg : ∀ a, applyMoves ms (negD d a) = negD d (applyMoves ms a) := fun a => by
    simp only [negD, hand, hxor, h256, hd]
  have hand' : ∀ a b, applyMoves ms (andD d a b) = andD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [andD, hand, hd]
  have hor' : ∀ a b, applyMoves ms (orD d a b) = orD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [orD, hand, hor, hd]
  rw [← hY]
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map _) ih
  | @one s a r save hne0 hned hnm _ ih =>
    have e1 : (negD d a :: kept save a r).map (applyMoves ms) =
        negD d (applyMoves ms a) :: kept save (applyMoves ms a) (r.map (applyMoves ms)) := by
      simp [kept_map, hneg]
    rw [e1] at ih
    refine Run.one save ?_ ?_ ?_ ih
    · intro e; rw [← hneg] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← hneg] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← hneg, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)
  | @two s a b r conj ka kb hne0 hned hnm _ ih =>
    have eop : applyMoves ms (if conj then andD d a b else orD d a b) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) := by
      cases conj <;> simp [hand', hor']
    have e1 : ((if conj then andD d a b else orD d a b) :: kept ka a (kept kb b r)).map (applyMoves ms) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))) := by
      simp [kept_map, eop]
    rw [e1] at ih
    refine Run.two conj ka kb ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop, ← List.map_cons, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)

theorem reach_map_moves (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd : applyMoves ms d2 = d1)
    {roots1 roots2 : List Nat} (hroots : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r)) :
    ∀ {p bank}, NatReach d2 roots2 p bank →
      ∃ bank', NatReach d1 roots1 p bank' ∧ ∀ v ∈ bank, Avail d1 bank' (applyMoves ms v) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hav : ∀ {b b' w}, (∀ v ∈ b, Avail d1 b' (applyMoves ms v)) →
      Avail d2 b w → Avail d1 b' (applyMoves ms w) := by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v, hv, he⟩
    · exact Or.inl (Or.inl (by rw [← hd, ← hand, hz, h0]))
    · exact Or.inl (Or.inr (by rw [← hd, ← hand, h1]))
    · have hve : applyMoves ms v &&& d1 = applyMoves ms w &&& d1 := by rw [← hd, ← hand, ← hand, he]
      exact avail_of_eq hve (hbb v hv)
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1, rfl, hroots⟩
  | succ p ih =>
    intro bank hr
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha
      refine ⟨negD d1 (applyMoves ms a) :: b', Or.inl ⟨b', applyMoves ms a, rfl, hrb', ha'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨negD d1 (applyMoves ms a), List.mem_cons_self, by simp only [negD, hand, hxor, h256, hd]⟩
      · exact avail_cons _ _ (hbb v hv)
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha; have hc' := hav hbb hc
      refine ⟨binD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
        Or.inr ⟨b', applyMoves ms a, applyMoves ms c, op, rfl, hrb', ha', hc'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨binD d1 op (applyMoves ms a) (applyMoves ms c), List.mem_cons_self, by
          cases op <;> simp only [binD, andD, orD, hand, hor, hd, ite_true, ite_false, Bool.false_eq_true]⟩
      · exact avail_cons _ _ (hbb v hv)

theorem lower_iso {d1 d2 T1 T2 L : Nat} {roots1 roots2 : List Nat}
    (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r => availB d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower d1 roots1 T1 L) : Lower d2 roots2 T2 L := by
  obtain ⟨hand, _, _, h0, _⟩ := applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r) := fun r hr =>
    (availB_iff _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank', hrb', hbb⟩ := reach_map_moves ms hok hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v, hv, he⟩
  · exact Or.inl (Or.inl (by rw [← hT, ← hd, ← hand, hz, h0]))
  · exact Or.inl (Or.inr (by rw [← hT, ← hd, ← hand, ho]))
  · have hve : applyMoves ms v &&& d1 = T1 &&& d1 := by rw [← hT, ← hd, ← hand, ← hand, he]
    exact avail_of_eq hve (hbb v hv)

def pairOK (d T : Nat) (p : Nat × Nat) : Bool :=
  d.testBit p.1 && d.testBit p.2 && (T.testBit p.1 != T.testBit p.2)

def essOK (d T : Nat) (roots : List Nat) (a : Nat) (p : Nat × Nat) : Bool :=
  pairOK d T p && roots.all (fun v => (v == a) || (v.testBit p.1 == v.testBit p.2))

theorem countP_ge_sublist (p : Nat → Bool) {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs, a ∈ ys) (hall : ∀ a ∈ xs, p a = true) :
    xs.length ≤ ys.countP p := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.1 hnd
    have ham : a ∈ ys := hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a) := List.perm_cons_erase ham
    rw [hperm.countP_eq, List.countP_cons, hall a List.mem_cons_self]
    have ih' := ih hnd' (fun x hx => by
      have hne : x ≠ a := fun e => hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true, List.length_cons]
    omega

theorem lower_slice {d dSub T TSub L : Nat} {roots rootsSub : List Nat}
    (hd : d &&& mask256 = d) (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB dSub rootsSub) = true)
    (singles : List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e => isConstB dSub e.1 && essOK d (T &&& d) (roots.map (· &&& d)) e.1 e.2) = true)
    (hprior : Lower dSub rootsSub TSub L) :
    Lower d roots T (L + singles.length) := by
  have hnc' : ¬ IsConst d T := fun h => by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T &&& d) := by
    intro h
    have e : (T &&& d) &&& dSub = TSub &&& dSub := by
      rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run hd hnc' hr ha
  have hws_av : ∀ w ∈ ws, Avail dSub rootsSub w := by
    intro w hw
    obtain ⟨r, hr_m, rfl⟩ := List.mem_map.1 (hws_sub w hw)
    have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub]) hav
  obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hncSub' hrun (p := 0) (bank := rootsSub) rfl hws_av
  have hTSub_av : Avail dSub next TSub := avail_of_eq (by
    rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht
  have hL : L ≤ q := hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst, a ∈ ws := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok (a', r1, r2) hm
    simp only [Bool.and_eq_true, essOK, pairOK, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
    obtain ⟨_, ⟨⟨hr1, hr2⟩, hdiff⟩, hiso⟩ := hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst, isConstB dSub a = true := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt := countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega

def runChoices (d : Nat) (pool : List Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some pool
  | p + 1, bits =>
    let code := bits &&& 1023
    let op := code &&& 3
    let ia := (code >>> 2) &&& 15
    let ib := (code >>> 6) &&& 15
    if ia < pool.length && (op == 2 || ib < pool.length) then
      let a := pool.getD ia 0
      let b := pool.getD ib 0
      let w := if op == 2 then negD d a else binD d (op == 1) a b
      runChoices d (pool ++ [w]) p (bits >>> 10)
    else none

theorem getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem runChoices_sound {d : Nat} {roots : List Nat} :
    ∀ (p bits q : Nat) (bank pool result : List Nat),
      NatReach d roots q bank →
      (∀ v ∈ pool, Avail d bank v) →
      runChoices d pool p bits = some result →
      ∃ bank', NatReach d roots (q + p) bank' ∧ ∀ v ∈ result, Avail d bank' v
  | 0, _, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices, Option.some.injEq] at hok; subst hok; exact ⟨bank, hr, hsup⟩
  | p + 1, bits, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices] at hok
    split at hok
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hcond
      obtain ⟨hia, hopb⟩ := hcond
      set code := bits &&& 1023
      set op := code &&& 3
      set ia := (code >>> 2) &&& 15
      set ib := (code >>> 6) &&& 15
      set a := pool.getD ia 0
      set b := pool.getD ib 0
      set w := if op == 2 then negD d a else binD d (op == 1) a b
      have ha : Avail d bank a := hsup a (getD_mem hia)
      have hr1 : NatReach d roots (q + 1) (w :: bank) := by
        by_cases h2 : op = 2
        · simp only [w, h2, beq_self_eq_true, ite_true]
          exact Or.inl ⟨bank, a, rfl, hr, ha⟩
        · have hib : ib < pool.length := hopb.resolve_left h2
          have hb : Avail d bank b := hsup b (getD_mem hib)
          simp only [w, h2, beq_iff_eq, ite_false]
          exact Or.inr ⟨bank, a, b, (op == 1), rfl, hr, ha, hb⟩
      have hsup1 : ∀ v ∈ pool ++ [w], Avail d (w :: bank) v := by
        intro v hv; rcases List.mem_append.1 hv with hv | hv
        · exact avail_cons _ _ (hsup v hv)
        · rw [List.mem_singleton.1 hv]; exact Or.inr ⟨w, List.mem_cons_self, rfl⟩
      obtain ⟨bank', hrb', hsb'⟩ := runChoices_sound p (bits >>> 10) (q + 1) (w :: bank) (pool ++ [w]) result hr1 hsup1 hok
      exact ⟨bank', by simpa [Nat.add_assoc, Nat.add_comm 1] using hrb', hsb'⟩
    · contradiction

def checkCutEntry (dSub : Nat) (rootsSub : List Nat) (LSub s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  let p := (hint >>> 8) &&& 15
  decide (s + p < LSub + ws.countP (isConstB dSub)) &&
  match runChoices dSub rootsSub p (hint >>> 12) with
  | none => false
  | some pool => ws.all (availB dSub pool)

theorem checkCutEntry_sound {d dSub T TSub LSub s : Nat} {rootsSub ws : List Nat}
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower dSub rootsSub TSub LSub) (hint : Nat)
    (hchk : checkCutEntry dSub rootsSub LSub s ws hint = true) :
    ¬ RunD d (T &&& d) s ws := by
  intro hrun
  simp only [checkCutEntry, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hineq, hmatch⟩ := hchk
  cases hrc : runChoices dSub rootsSub ((hint >>> 8) &&& 15) (hint >>> 12) with
  | none => rw [hrc] at hmatch; contradiction
  | some pool =>
    rw [hrc] at hmatch
    have hsup0 : ∀ v ∈ rootsSub, Avail dSub rootsSub v := fun v hv => Or.inr ⟨v, hv, rfl⟩
    obtain ⟨bank, hrb, hsb⟩ := runChoices_sound _ _ 0 rootsSub rootsSub pool rfl hsup0 hrc
    simp only [Nat.zero_add] at hrb
    have hws_av : ∀ w ∈ ws, Avail dSub bank w := by
      intro w hw
      have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hmatch w hw)
      rcases hav with hc | ⟨v, hv, he⟩
      · exact Or.inl hc
      · exact avail_of_eq he (hsb v hv)
    have hnc' : ¬ IsConst dSub (T &&& d) := by
      intro h; have e : (T &&& d) &&& dSub = TSub &&& dSub := by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
      rcases h with h0 | h1
      · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
      · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
    obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hnc' hrun hrb hws_av
    have hL := hprior q next hq (avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht)
    omega

def coversP (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then
    pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem coversP_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : coversP pairs s ws = true := by
  unfold coversP
  by_cases hl : ws.length = s + 1
  · simp only [hl, beq_self_eq_true, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := runD_bits_le h hl v u hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u <;> cases hv : w.testBit v <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  · simp only [hl, beq_iff_eq, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def unorientedCov (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem unorientedCov_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : unorientedCov pairs ws = true := by
  simp only [unorientedCov, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro ⟨u, v⟩ hm
  have hp := List.all_eq_true.1 hpairs (u, v) hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  by_contra! hall
  have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2, hp.2] at heq; contradiction

def maskP (m : Nat) : Nat := 2 ^ m - 1

def projBit (rs : List Nat) (w : Nat) : Nat :=
  rs.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0

theorem projBit_testBit (rs : List Nat) (w : Nat) (i : Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false := by
  induction rs generalizing i with
  | nil => simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one, decide_false, Bool.false_and, Bool.false_or,
        List.length_cons, Nat.zero_lt_succ, dite_true, List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i), decide_true, Bool.true_and, Nat.add_sub_cancel,
        List.length_cons, Nat.succ_lt_succ_iff, List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false := by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1, Bool.or_false]; exact ih i

theorem projBit_negD {dm : Nat} (hd : dm &&& mask256 = dm) {rs : List Nat}
    (hrs : ∀ r ∈ rs, dm.testBit r = true) (w : Nat) :
    projBit rs (negD dm w) = projBit rs w ^^^ maskP rs.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_xor, projBit_testBit, maskP, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < rs.length
  · have hdr := hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true := by
      have := congrArg (fun v => v.testBit rs[i]) hd; simp [Nat.testBit_and, hdr] at this; exact this
    simp [hi, negD, hdr, hmr]
  · simp [hi]

theorem projBit_andD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (andD dm a b) = projBit rs a &&& projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_and, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, andD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem projBit_orD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (orD dm a b) = projBit rs a ||| projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_or, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, orD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs : List α) (acc i : Nat) :
    (xs.foldl (fun a x => a ||| g x) acc).testBit i = (acc.testBit i || xs.any (fun x => (g x).testBit i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons, Bool.or_assoc]

def coversD (mp s : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  if dws.length == s + 1 then
    dws.foldl (fun acc d => acc ||| ((d.2.1 ^^^ mp) &&& d.2.2)) 0 == mp
  else
    dws.foldl (fun acc d => acc ||| (d.2.1 ^^^ d.2.2)) 0 == mp

theorem coversD_eq (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) :
    coversD (maskP pairs.length) s (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) =
      coversP pairs s ws := by
  set r1s := pairs.map Prod.fst
  set r2s := pairs.map Prod.snd
  set mp := maskP pairs.length
  have hr1 : r1s.length = pairs.length := List.length_map _
  have hr2 : r2s.length = pairs.length := List.length_map _
  unfold coversD coversP
  simp only [List.length_map]
  split
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
        Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
            Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true, r1s, r2s, List.getElem_map]
          exact hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Nat.testBit_two_pow_sub_one, decide_false, Bool.xor_false, Bool.and_false, not_false_eq_true, Bool.false_eq_true]
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s, bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true, r1s, r2s, List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Bool.xor_false, Bool.false_eq_true, not_false_eq_true]

theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs : List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x == f a) = false := beq_false_of_ne (fun e => h (hinj e))
      have hx : (x == a) = false := beq_false_of_ne h
      simp [hf, hx, ih]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b, v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {dm y s ws} (h : RunD dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, andD, Nat.testBit_and, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, orD, Nat.testBit_and, Nat.testBit_or, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil => simp [sumBelow]
  | cons w ws ih => rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]; omega

def scoreCheck (dm y s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  let a := code &&& 255
  let b := (code >>> 8) &&& 255
  let c := (code >>> 16) &&& 255
  let d := (code >>> 24) &&& 255
  let e := (code >>> 32) &&& 255
  let f := (code >>> 40) &&& 255
  dm.testBit a && dm.testBit b && dm.testBit c && dm.testBit d && dm.testBit e && dm.testBit f &&
    ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)

theorem scoreCheck_no {dm y s ws} (h : RunD dm y s ws) (code : Nat) :
    scoreCheck dm y s ws code = false := by
  unfold scoreCheck
  by_cases hok : dm.testBit (code &&& 255) = true ∧ dm.testBit ((code >>> 8) &&& 255) = true ∧
      dm.testBit ((code >>> 16) &&& 255) = true ∧ dm.testBit ((code >>> 24) &&& 255) = true ∧
      dm.testBit ((code >>> 32) &&& 255) = true ∧ dm.testBit ((code >>> 40) &&& 255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha, hb, hc, hd, he, hf, hl⟩ := hok
    simp only [ha, hb, hc, hd, he, hf, hl, beq_self_eq_true, Bool.true_and]
    by_contra hbad
    have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht := Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1, ht.1.1.1.1.1.1.2, ht.1.1.1.1.1.2, ht.1.1.1.1.2, ht.1.1.1.2, ht.1.1.2, ht.1.2⟩

def scr (dm y s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck dm y s zs)

theorem scr_no {dm y s : Nat} (pool : List Nat) {zs : List Nat}
    (h : RunD dm y s zs) : scr dm y s pool zs = false := by
  unfold scr; rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
  intro x _; rw [scoreCheck_no h x]; simp

def nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(ws.contains w) &&
         (f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem nextD_one {dm y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h0 : negD dm a ≠ 0) (hd : negD dm a ≠ dm) (hnm : negD dm a ∉ (a :: rest))
    (h : RunD dm y s (negD dm a :: kept save a rest))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  have hnc : ws.contains (negD dm a) = false := by
    cases h : ws.contains (negD dm a) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (negD dm a != 0) = true := bne_iff_ne.2 h0
  have hdb : (negD dm a != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true => simp [kept] at ht hh; simp [ht, show 2 ≤ s + 2 - ws.length by omega]

theorem nextD_two_sorted {dm y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (if conj then andD dm a b else orD dm a b) = false := by
    cases h : ws.contains (if conj then andD dm a b else orD dm a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : ((if conj then andD dm a b else orD dm a b) != 0) = true := bne_iff_ne.2 h0
  have hdb : ((if conj then andD dm a b else orD dm a b) != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right; apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem nextD_two {dm y a b rest} {conj ka kb : Bool} {s ws} (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hab p h0 hd hnm h f hf
  · have he : (if conj then andD dm a b else orD dm a b) = (if conj then andD dm b a else orD dm b a) := by
      cases conj <;> simp [andD, orD, Nat.and_comm, Nat.or_comm]
    have hnm' : (if conj then andD dm b a else orD dm b a) ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _

theorem nextD_complete {dm y t ws} (h : RunD dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, RunD dm y s ys → f ys = true) →
      nextD dm (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_one p h0 hd hnm h f hf
  | two conj ka kb h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_two p h0 hd hnm h f hf

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi

def fld (T w i : Nat) : Nat :=
  (T >>> (w * i)) &&& (if w == 32 then 4294967295 else if w == 52 then 4503599627370495 else if w == 256 then mask256 else 2 ^ w - 1)

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw256 (seed w : Nat) : Nat :=
  let x := (((w % PEqualNP.Outside.L_meta_29324_aux.certWord0) ^^^ seed) * PEqualNP.Outside.L_meta_29324_aux.certWord1) &&& PEqualNP.Outside.L_meta_29324_aux.certWord2
  let y := ((x ^^^ (x >>> 61)) * PEqualNP.Outside.L_meta_29324_aux.certWord3) &&& PEqualNP.Outside.L_meta_29324_aux.certWord2
  y >>> 96

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw256 seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def foundH (S : Nat → Nat → List Nat) (N : Nat → Nat) (htAt : Nat → Nat → Nat)
    (idxH : Nat → Nat → Nat) (s h : Nat) (zs : List Nat) : Bool :=
  let i := idxH s h
  decide (i < N s) && (htAt s i == h) && zs.isPerm (S s i)

def nextD_decor (dm mp : Nat) (slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  dws.any fun da =>
    let a := da.1
    let ra := dws.erase da
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
         let dw := (w, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
         (f (dw :: ra) || (slack ≥ 2 && f (dw :: da :: ra))))) ||
    ra.any fun db =>
      let b := db.1
      a ≤ b && (let r := ra.erase db
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
            let dw := if conj then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                      else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
            (f (dw :: r) || (slack ≥ 1 && (f (dw :: da :: r) || f (dw :: db :: r))) ||
              (slack ≥ 2 && f (dw :: da :: db :: r))))

theorem nextD_decor_gen (dm mp : Nat) (dec : Nat → Nat × Nat × Nat)
    (hfst : ∀ w, (dec w).1 = w)
    (hneg : ∀ a, (negD dm a, (dec a).2.1 ^^^ mp, (dec a).2.2 ^^^ mp) = dec (negD dm a))
    (hbin : ∀ (c : Bool) a b,
      (if c then (if c then andD dm a b else orD dm a b, (dec a).2.1 &&& (dec b).2.1, (dec a).2.2 &&& (dec b).2.2)
       else (if c then andD dm a b else orD dm a b, (dec a).2.1 ||| (dec b).2.1, (dec a).2.2 ||| (dec b).2.2)) =
      dec (if c then andD dm a b else orD dm a b))
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    nextD_decor dm mp slack (ws.map dec) g = nextD dm slack ws (fun zs => g (zs.map dec)) := by
  have hinj : Function.Injective dec := fun x y h => by rw [← hfst x, ← hfst y, h]
  have herase : ∀ (l : List Nat) x, (l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x => erase_map_inj dec hinj l x
  have hcont : ∀ (l : List Nat) w, (l.map dec).any (fun x => x.1 == w) = l.contains w := by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map, Function.comp_def, hfst, herase, hcont, hneg, hbin, List.map_cons]

theorem nextD_decor_eq {dm : Nat} (hd : dm &&& mask256 = dm)
    (pairs : List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true)
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    let dec := fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)
    nextD_decor dm (maskP pairs.length) slack (ws.map dec) g =
      nextD dm slack ws (fun zs => g (zs.map dec)) := by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro a
    simp only [dec, projBit_negD hd hr1, projBit_negD hd hr2, List.length_map]
  · intro c a b
    cases c <;> simp only [dec, ↓reduceIte, Bool.false_eq_true, projBit_andD hr1, projBit_andD hr2,
      projBit_orD hr1, projBit_orD hr2]

def colB (mp : Nat) (d : Bool) (p : Nat × Nat) : Nat :=
  if d then (p.1 ^^^ mp) &&& p.2 else p.1 ^^^ p.2

def addC (x : Nat) (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (c.1 ||| x, c.2.1 ||| (c.1 &&& x), c.2.2 ||| (c.2.1 &&& x))

def cov3 (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) : Nat × Nat × Nat :=
  dws.foldl (fun c dw => addC (colB mp d dw.2) c) (0, 0, 0)

def takeOne (c : Nat × Nat × Nat) (x : Nat) : Nat := (c.1 ^^^ x) ||| c.2.1
def takeTwo (c : Nat × Nat × Nat) (x y : Nat) : Nat :=
  (c.1 ^^^ (x ||| y)) ||| (c.2.1 &&& (x ^^^ y)) ||| c.2.2

theorem cov3_bit (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) (i : Nat) :
    let k := dws.countP (fun dw => (colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k) := by
  have hgen : ∀ (xs : List (Nat × Nat × Nat)) (c : Nat × Nat × Nat) (k0 : Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k := k0 + xs.countP (fun dw => (colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k) := by
    intro xs
    induction xs with
    | nil => intro c k0 ⟨h1, h2, h3⟩; simp [h1, h2, h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1, h2, h3⟩
      simp only [List.foldl_cons, List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) := by
        simp only [addC, Nat.testBit_or, Nat.testBit_and, h1, h2, h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb, Nat.le_add_left]
      have ih' := ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc, Nat.add_comm 1] using ih'
  simpa only [cov3, Nat.zero_testBit, Nat.zero_add] using hgen dws (0, 0, 0) 0 (by simp)

theorem cov3_perm (mp : Nat) (d : Bool) {xs ys : List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys := by
  have heq : ∀ i, (cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i := by
    intro i
    obtain ⟨a1, a2, a3⟩ := cov3_bit mp d xs i
    obtain ⟨b1, b2, b3⟩ := cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i => (heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.2)

theorem takeOne_eq (mp : Nat) (d : Bool) (a : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, _⟩ := cov3_bit mp d (a :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeOne, Nat.testBit_or, Nat.testBit_xor, h1, h2, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, decide_true, Bool.xor_false, Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 1 ≤ k + 3 by omega,
      decide_true, Bool.xor_true, Bool.or_true, Bool.or_false]

theorem takeTwo_eq (mp : Nat) (d : Bool) (a b : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, h3⟩ := cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeTwo, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, h1, h2, h3, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega, show 2 ≤ k + 3 + 1 + 1 by omega, show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true, Bool.xor_true, Bool.xor_false, Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false])

theorem cov3_coversD (mp s : Nat) (dw : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    let d := (dw :: rest).length == s + 1
    ((cov3 mp d rest).1 ||| colB mp d dw.2 == mp) = coversD mp s (dw :: rest) := by
  intro d
  have e : ∀ b : Bool, ((cov3 mp b rest).1 ||| colB mp b dw.2) =
      (dw :: rest).foldl (fun acc x => acc ||| colB mp b x.2) 0 := by
    intro b; apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1, _, _⟩ := cov3_bit mp b rest i
    rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, Nat.testBit_or, h1, List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw => (colB mp b dw.2).testBit i)) =
        rest.any (fun x => (colB mp b x.2).testBit i) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.succ_le_iff, List.countP_pos_iff, List.any_eq_true]
    rw [hp, Bool.or_comm]
  have hf : ∀ b : Bool, (cov3 mp b rest).1 ||| colB mp b dw.2 =
      (dw :: rest).foldl (fun acc x => acc ||| (if b then (x.2.1 ^^^ mp) &&& x.2.2 else x.2.1 ^^^ x.2.2)) 0 := by
    intro b; simpa only [colB] using e b
  unfold coversD
  dsimp only [d]
  cases (dw :: rest).length == s + 1
  · simpa only [Bool.false_eq_true, ↓reduceIte] using congrArg (· == mp) (hf false)
  · simpa only [↓reduceIte] using congrArg (· == mp) (hf true)

def nextD_cov (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  let len := dws.length
  let covF := cov3 mp false dws
  let covT := cov3 mp true dws
  let du0 := len == s + 1
  let du1 := len + 1 == s + 1
  let db0 := len - 1 == s + 1
  let db1 := len == s + 1
  let db2 := len + 1 == s + 1
  dws.any fun da =>
    let a := da.1
    (slack ≥ 1 &&
      (let pneg := (da.2.1 ^^^ mp, da.2.2 ^^^ mp)
       let uok0 := (takeOne (if du0 then covT else covF) (colB mp du0 da.2) ||| colB mp du0 pneg) == mp
       let uok1 := slack ≥ 2 && (((if du1 then covT.1 else covF.1) ||| colB mp du1 pneg) == mp)
       (uok0 || uok1) &&
       (let w := negD dm a
        w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
          let dw := (w, pneg)
          let ra := dws.erase da
          ((uok0 && f (dw :: ra)) || (uok1 && f (dw :: da :: ra)))))) ||
    (dws.erase da).any fun db =>
      let b := db.1
      a ≤ b &&
        [false, true].any fun conj =>
          let pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                    else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
          let ok0 := (takeTwo (if db0 then covT else covF) (colB mp db0 da.2) (colB mp db0 db.2) ||| colB mp db0 pz) == mp
          let ok1a := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 db.2) ||| colB mp db1 pz) == mp)
          let ok1b := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 da.2) ||| colB mp db1 pz) == mp)
          let ok2 := slack ≥ 2 && (((if db2 then covT.1 else covF.1) ||| colB mp db2 pz) == mp)
          (ok0 || ok1a || ok1b || ok2) &&
          (let w := if conj then andD dm a b else orD dm a b
           w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
             let dw := (w, pz)
             let r := (dws.erase da).erase db
             ((ok0 && f (dw :: r)) || (ok1a && f (dw :: da :: r)) || (ok1b && f (dw :: db :: r)) || (ok2 && f (dw :: da :: db :: r))))

theorem nextD_cov_eq (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (g : List (Nat × Nat × Nat) → Bool) :
    nextD_cov dm mp s slack dws g =
      nextD_decor dm mp slack dws (fun dzs => coversD mp s dzs && g dzs) := by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      refine ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra
        rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 :
          (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra)
        rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hu0, hf0⟩ | ⟨⟨hsl2, hu1⟩, hf1⟩
      · left; exact ⟨hcov0 ▸ hu0, hf0⟩
      · right; exact ⟨hsl2, hcov1 ▸ hu1, hf1⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw]
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r
      rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r)
      rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r)
      rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r)
      rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with ((⟨hu0, hf0⟩ | ⟨⟨hsl1, hu1a⟩, hf1a⟩) | ⟨⟨hsl1, hu1b⟩, hf1b⟩) | ⟨⟨hsl2, hu2⟩, hf2⟩
      · left; left; exact ⟨hcov0' ▸ hu0, hf0⟩
      · left; right; exact ⟨hsl1, Or.inl ⟨hcov1a' ▸ hu1a, hf1a⟩⟩
      · left; right; exact ⟨hsl1, Or.inr ⟨hcov1b' ▸ hu1b, hf1b⟩⟩
      · right; exact ⟨hsl2, hcov2' ▸ hu2, hf2⟩
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra; rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra); rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hc0, hg0⟩ | ⟨hsl2, hc1, hg1⟩
      · have hu0 : ((takeOne _ _ ||| _) == mp) = true := hcov0.symm ▸ hc0
        exact ⟨hsl, Or.inl hu0, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl ⟨hu0, hg0⟩⟩
      · have hu1 : ((_ ||| _) == mp) = true := hcov1.symm ▸ hc1
        exact ⟨hsl, Or.inr ⟨hsl2, hu1⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, hu1⟩, hg1⟩⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw] at hfx
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r; rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r); rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r); rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r); rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with (⟨hc0, hg0⟩ | ⟨hsl1, ⟨hc1a, hg1a⟩ | ⟨hc1b, hg1b⟩⟩) | ⟨hsl2, hc2', hg2⟩
      · have u0 : ((takeTwo _ _ _ ||| _) == mp) = true := hcov0'.symm ▸ hc0
        exact ⟨Or.inl (Or.inl (Or.inl u0)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inl ⟨u0, hg0⟩))⟩
      · have u1a : ((takeOne _ _ ||| _) == mp) = true := hcov1a'.symm ▸ hc1a
        exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1, u1a⟩)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inr ⟨⟨hsl1, u1a⟩, hg1a⟩))⟩
      · have u1b : ((takeOne _ _ ||| _) == mp) = true := hcov1b'.symm ▸ hc1b
        exact ⟨Or.inl (Or.inr ⟨hsl1, u1b⟩), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inr ⟨⟨hsl1, u1b⟩, hg1b⟩)⟩
      · have u2 : ((_ ||| _) == mp) = true := hcov2'.symm ▸ hc2'
        exact ⟨Or.inr ⟨hsl2, u2⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, u2⟩, hg2⟩⟩

def bar (dm Y : Nat) (pairs : List (Nat × Nat)) (r1s r2s : List Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov dm mp s (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(scr dm Y s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

theorem bar_all {dm T : Nat} {pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {u ys}, RunD dm (T &&& dm) u ys → RunD dm (T &&& dm) u (ori ys))
    (hcut : ∀ {u ys}, cutHitH u (hk seed ys) ys = true → ¬ RunD dm (T &&& dm) u ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, bar dm (T &&& dm) pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD dm (T &&& dm) s (S s i) := by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb := hc s hs i hi
    cases s with
    | zero => simp [bar, zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (zs : List Nat) :=
        coversP pairs s zs && !(scr dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, foundH]
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        rintro ⟨hj, _⟩
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN := nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr dm (T &&& dm) s pool zs') &&
           (let cz := ori zs'
            let h := hk seed cz
            !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

def pickMin (seed : Nat) (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH

theorem pickMin_runD {dm Y u} (seed : Nat) (orig : List Nat) (h0 : RunD dm Y u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all moveOK256 && (applyMoves ms dm == dm) && (applyMoves ms Y == Y)) = true →
      RunD dm Y u best →
      RunD dm Y u (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb

def gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => andD mask256 (w.getD i 0) acc) mask256
  | .or  => g.inputs.foldr (fun i acc => orD mask256 (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => mask256 | i :: _ => negD mask256 (w.getD i 0)
  | _ => 0

def execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [gvN l g]) w

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
  have hm : mask256.testBit r = true := by simp [mask256_bit, hr]
  have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? with | none => simp | some v => rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.all_cons, id_eq, andD, Nat.testBit_and, Nat.testBit_and, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.any_cons, id_eq, orD, Nat.testBit_and, Nat.testBit_or, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    cases g.inputs with
    | nil => simp [hm]
    | cons i l => simp only [List.map_cons, List.headD_cons, negD, Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Bool.xor_true, hgd]

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]

theorem execN_reach (gs : List Gate) (roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (p : Nat) (w bank : List Nat), NatReach mask256 roots p bank →
      (∀ v ∈ w, Avail mask256 bank v) →
      ∃ p' bank', p' ≤ p + gs.length ∧ NatReach mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w, Avail mask256 bank' v := by
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by omega, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Avail mask256 bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))

    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ NatReach mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail mask256 bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD mask256 a mask256 &&& mask256 = a &&& mask256 := fun a => by
        simp [andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, orD mask256 a 0 &&& mask256 = a &&& mask256 := fun a => by
        simp [orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Avail mask256 (z :: bank) v) := fun z v hv => avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 false (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, false, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by simp [binD, andD, Nat.and_assoc, Nat.and_self]⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 true (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, true, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [binD, orD]; cases mask256.testBit r <;> simp⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, l⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · refine ⟨p + 1, negD mask256 (w.getD i 0) :: bank, le_rfl,
            Or.inl ⟨bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def xs256 : List Nat :=
  [PEqualNP.Outside.L_meta_29324_aux.certWord4,
   PEqualNP.Outside.L_meta_29324_aux.certWord5,
   PEqualNP.Outside.L_meta_29324_aux.certWord6,
   PEqualNP.Outside.L_meta_29324_aux.certWord7,
   PEqualNP.Outside.L_meta_29324_aux.certWord8,
   PEqualNP.Outside.L_meta_29324_aux.certWord9,
   PEqualNP.Outside.L_meta_29324_aux.certWord10,
   PEqualNP.Outside.L_meta_29324_aux.certWord11]

def pt8 (r : Nat) : Fin 8 → Bool := fun i => r.testBit i.val

theorem xs256_bits : ∀ r : Fin 256, xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val) := by
  decide +kernel

theorem lower_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 256, T.testBit r.val = f (pt8 r.val))
    (hlow : Lower mask256 xs256 T lb) :
    ∀ t : ℕ, HasCircuitSize 8 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ xs256, Avail mask256 xs256 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates xs256 hfan 0 xs256 xs256 rfl hsup0
  have hout : (execN C.gates xs256).getD C.output 0 &&& mask256 = T &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit C.gates xs256 r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r) := hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hav_out : Avail mask256 bank ((execN C.gates xs256).getD C.output 0) := by
    by_cases hi : C.output < (execN C.gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := hlow p bank hr (avail_of_eq hout hav_out)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def dom_0 : Nat := 0x3000300030003
def goal_0 : Nat := 0x3000200020000
def roots_0 : List Nat := [0x2000200020002, 0x3000000030000, 0x3000300000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (16, 17), (16, 48), (32, 33), (32, 48)]
def r1sG : List Nat := [1, 1, 16, 16, 32, 32]
def r2sG : List Nat := [17, 33, 17, 48, 33, 48]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x6c50c4bd
  | 3, 0 => 0x6c50c4bd
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord12
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x243
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 10
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x30303
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ab57
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 6 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 6 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 3 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_0 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_0 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord18, 31), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_0 == dom_0) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_0 goalM u ys) : RunD dom_0 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_0 roots_0 goal_0 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_0 goal_0 := by
    have h0 : isConstB dom_0 goal_0 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_0

theorem low_0 : Lower dom_0 roots_0 goal_0 4 := S_0.noCircuit

def dom_1 : Nat := 0x303030303030303
def goal_1 : Nat := 0x303020202020200
def roots_1 : List Nat := [0x202020202020202, 0x300030003000300, 0x303000003030000, 0x303030300000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x300030003000300, 1, 9)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0x33003300330033
def goal_2 : Nat := 0x33002200220020
def roots_2 : List Nat := [0x22002200220022, 0x30003000300030, 0x33000000330000, 0x33003300000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0x333300003333
def goal_3 : Nat := 0x322200003220
def roots_3 : List Nat := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord19, 12), (PEqualNP.Outside.L_meta_29324_aux.certWord20, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_4 : Nat := 0x33333333
def goal_4 : Nat := 0x32223220
def roots_4 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0x3333
def goal_5 : Nat := 0x3220
def roots_5 : List Nat := [0x2222, 0x3030, 0x3300]

theorem low_5 : Lower dom_5 roots_5 goal_5 4 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord19, 12), (PEqualNP.Outside.L_meta_29324_aux.certWord20, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_6 : Nat := 0x3333333333333333
def goal_6 : Nat := 0x3333322232223220
def roots_6 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

namespace S_6
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (1, 17), (1, 33), (4, 5), (4, 12), (8, 9), (8, 12), (16, 17), (16, 48), (20, 21), (20, 28), (20, 52), (24, 25), (24, 28), (24, 56), (32, 33), (32, 48), (36, 37), (36, 44), (36, 52), (40, 41), (40, 44), (40, 56)]
def r1sG : List Nat := [1, 1, 1, 1, 4, 4, 8, 8, 16, 16, 20, 20, 20, 24, 24, 24, 32, 32, 36, 36, 36, 40, 40, 40]
def r2sG : List Nat := [5, 9, 17, 33, 5, 12, 9, 12, 17, 48, 21, 28, 52, 25, 28, 56, 33, 48, 37, 44, 52, 41, 44, 56]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_6.map (· &&& dom_6)
def goalM : Nat := goal_6 &&& dom_6
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 10
  | 6 => 6
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x3715501e
  | 4, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord21
  | 5, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord22
  | 6, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord23
  | 7, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord24
  | 0, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord25
  | 0, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord26
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xac1cb4
  | 4, 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord27
  | 5, 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord28
  | 6, 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord29
  | 7, 0, 0 => 0x15831285
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 24
  | 4 => 29
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord30
  | 0, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord31
  | 0, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord32
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord33
  | 0, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord34
  | 0, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord35
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 24 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 24 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 23 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 23 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 23 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 23 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 5 0) :: stateWiresD n (ids >>> 5)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 5 0) :: stateWiresS n (ids >>> 5)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 5
  | 5 => 27
  | 6 => 5
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord36
  | 5, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord37
  | 6, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord38
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord39
  | 5, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord40
  | 6, 0 => 0x80000000001000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 3 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 4 => checkCutEntry dom_0 roots_0 4 s ws hint
  | 5 => checkCutEntry dom_5 roots_5 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_6 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_6 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord19, 12), (PEqualNP.Outside.L_meta_29324_aux.certWord20, 24)], [(PEqualNP.Outside.L_meta_29324_aux.certWord41, 28), (PEqualNP.Outside.L_meta_29324_aux.certWord42, 8), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord19, 12), (PEqualNP.Outside.L_meta_29324_aux.certWord20, 24), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord41, 28), (PEqualNP.Outside.L_meta_29324_aux.certWord42, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_6 == dom_6) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_6 goalM u ys) : RunD dom_6 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_6 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := range_split z5_0 (z5_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := z6_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := z7_0
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_6 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_6 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_6 roots_6 goal_6 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_6 goal_6 := by
    have h0 : isConstB dom_6 goal_6 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_6

theorem low_6 : Lower dom_6 roots_6 goal_6 8 := S_6.noCircuit

def dom_7 : Nat := 0x5555
def goal_7 : Nat := 0x5440
def roots_7 : List Nat := [0x4444, 0x5050, 0x5500]

theorem low_7 : Lower dom_7 roots_7 goal_7 4 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_8 : Nat := 0xf0f
def goal_8 : Nat := 0xe08
def roots_8 : List Nat := [0xa0a, 0xc0c, 0xf00]

theorem low_8 : Lower dom_8 roots_8 goal_8 4 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_9 : Nat := 0xff
def goal_9 : Nat := 0xe8
def roots_9 : List Nat := [0xaa, 0xcc, 0xf0]

theorem low_9 : Lower dom_9 roots_9 goal_9 4 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0xffff
def goal_10 : Nat := 0xfee8
def roots_10 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

namespace S_10
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (2, 6), (2, 10), (4, 5), (4, 6), (4, 12), (8, 9), (8, 10), (8, 12)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 8]
def r2sG : List Nat := [3, 5, 9, 3, 6, 10, 5, 6, 12, 9, 10, 12]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_10.map (· &&& dom_10)
def goalM : Nat := goal_10 &&& dom_10
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x5b7720d1
  | 4, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord44
  | 5, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord45
  | 6, 0 => 0xa8d11512
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord46
  | 0, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord47
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa9864
  | 4, 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord48
  | 5, 0, 0 => 0xa75440a7534da7545
  | 6, 0, 0 => 0xa7544
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord49
  | 0, 1 => 0xfc0e3fe07e001f81c7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord50
  | 0, 1 => 0xff6ffff6ff24dfbbdf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 14 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 14 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 14 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 14 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 4 0) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 4 0) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 2 => 1
  | 3 => 4
  | 4 => 8
  | 5 => 2
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0x5770d39
  | 3, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord51
  | 4, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord52
  | 5, 0 => 0x1a46e13f02e67005
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x0
  | 3, 0 => 0x400002
  | 4, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord53
  | 5, 0 => 0x400003
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 1 => checkCutEntry dom_5 roots_5 4 s ws hint
  | 2 => checkCutEntry dom_8 roots_8 4 s ws hint
  | 3 => checkCutEntry dom_9 roots_9 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_10 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_10 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6)], [(PEqualNP.Outside.L_meta_29324_aux.certWord43, 1), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord54, 3), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)], [(PEqualNP.Outside.L_meta_29324_aux.certWord55, 7), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_10 == dom_10) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_10 goalM u ys) : RunD dom_10 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_10 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_10 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_10 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_10 roots_10 goal_10 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_10 goal_10 := by
    have h0 : isConstB dom_10 goal_10 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_10

theorem low_10 : Lower dom_10 roots_10 goal_10 7 := S_10.noCircuit

def dom_11 : Nat := 0xffffffff
def goal_11 : Nat := 0xfeeafee8
def roots_11 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_11 : Lower dom_11 roots_11 goal_11 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffff0000, 1, 17)] (by decide +kernel) (by decide +kernel) low_10

def dom_12 : Nat := 0xf0f0f0f0f0f0f0f
def goal_12 : Nat := 0xf0f0e0a0e0a0e08
def roots_12 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 8 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_13 : Nat := 0xff00ff00ff00ff
def goal_13 : Nat := 0xff00ea00ea00e8
def roots_13 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 8 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0xffff0000ffff
def goal_14 : Nat := 0xfeea0000fee8
def roots_14 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 8 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_15 : Nat := 0x5555555555555555
def goal_15 : Nat := 0x5555544054405440
def roots_15 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000055550000, 32, 48), (0x5555555500000000, 16, 48)] (by decide +kernel) (by decide +kernel) low_7

def dom_16 : Nat := 0x555500000000
def goal_16 : Nat := 0x544000000000
def roots_16 : List Nat := [0x444400000000, 0x505000000000, 0x550000000000]

namespace S_16
def pairsG : List (Nat × Nat) := [(34, 38), (34, 42), (36, 38), (36, 44), (40, 42), (40, 44)]
def r1sG : List Nat := [34, 34, 36, 36, 40, 40]
def r2sG : List Nat := [38, 42, 38, 44, 42, 44]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_16.map (· &&& dom_16)
def goalM : Nat := goal_16 &&& dom_16
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x95ad01e5
  | 3, 0 => 0x95ad01e5
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord56
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x243
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 10
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x30303
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ab57
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 6 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 6 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 3 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15), (PEqualNP.Outside.L_meta_29324_aux.certWord16, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_16 == dom_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_16 goalM u ys) : RunD dom_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_16 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_16 roots_16 goal_16 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_16 goal_16 := by
    have h0 : isConstB dom_16 goal_16 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_16

theorem low_16 : Lower dom_16 roots_16 goal_16 4 := S_16.noCircuit

def dom_17 : Nat := 0x5555555500000000
def goal_17 : Nat := 0x5555544000000000
def roots_17 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 32, 48)] (by decide +kernel) (by decide +kernel) low_16

def dom_18 : Nat := 0xffffffff00000000
def goal_18 : Nat := 0xfffffeea00000000
def roots_18 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_17

def dom_19 : Nat := 0xffff0000ffff0000
def goal_19 : Nat := 0xffff0000feea0000
def roots_19 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 6 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18

def dom_20 : Nat := 0xffff00000000
def goal_20 : Nat := 0xfeea00000000
def roots_20 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord17, 15)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17

def dom_21 : Nat := 0xffff0000
def goal_21 : Nat := 0xfeea0000
def roots_21 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20

def dom_22 : Nat := 0xff00ff
def goal_22 : Nat := 0xea00e8
def roots_22 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

theorem low_22 : Lower dom_22 roots_22 goal_22 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_23 : Nat := 0xff000000ff
def goal_23 : Nat := 0xea000000e8
def roots_23 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

theorem low_23 : Lower dom_23 roots_23 goal_23 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_22

def dom_24 : Nat := 0xf0f0f0f
def goal_24 : Nat := 0xe0a0e08
def roots_24 : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]

theorem low_24 : Lower dom_24 roots_24 goal_24 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_22

def dom_25 : Nat := 0xf0f00000f0f
def goal_25 : Nat := 0xe0a00000e08
def roots_25 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]

theorem low_25 : Lower dom_25 roots_25 goal_25 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24

def dom_26 : Nat := 0xf000f000f000f
def goal_26 : Nat := 0xf000a000a0008
def roots_26 : List Nat := [0xa000a000a000a, 0xc000c000c000c, 0xf0000000f0000, 0xf000f00000000]

theorem low_26 : Lower dom_26 roots_26 goal_26 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_27 : Nat := 0x5555000055550000
def goal_27 : Nat := 0x5555000054400000
def roots_27 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]

theorem low_27 : Lower dom_27 roots_27 goal_27 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17

def dom_28 : Nat := 0xffffffffffffffff
def goal_28 : Nat := 0xfffffeeafeeafee8
def roots_28 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_28
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (1, 33), (2, 3), (2, 6), (2, 10), (4, 5), (4, 6), (4, 12), (8, 9), (8, 10), (8, 12), (16, 17), (16, 48), (18, 19), (18, 22), (18, 26), (18, 50), (20, 21), (20, 22), (20, 28), (20, 52), (24, 25), (24, 26), (24, 28), (24, 56), (32, 33), (32, 48), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (36, 44), (36, 52), (40, 41), (40, 42), (40, 44), (40, 56)]
def r1sG : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 8, 16, 16, 18, 18, 18, 18, 20, 20, 20, 20, 24, 24, 24, 24, 32, 32, 34, 34, 34, 34, 36, 36, 36, 36, 40, 40, 40, 40]
def r2sG : List Nat := [3, 5, 9, 17, 33, 3, 6, 10, 5, 6, 12, 9, 10, 12, 17, 48, 19, 22, 26, 50, 21, 22, 28, 52, 25, 26, 28, 56, 33, 48, 35, 38, 42, 50, 37, 38, 44, 52, 41, 42, 44, 56]
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_28.map (· &&& dom_28)
def goalM : Nat := goal_28 &&& dom_28
def NN : Nat → Nat
  | 4 => 2
  | 5 => 30
  | 6 => 104
  | 7 => 162
  | 8 => 52
  | 9 => 9
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x15e86903110c7cbc
  | 5, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord57
  | 6, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord58
  | 6, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord59
  | 7, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord60
  | 7, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord61
  | 7, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord62
  | 8, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord63
  | 9, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord64
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord65
  | 0, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord66
  | 0, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord67
  | 0, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord68
  | 0, 4 => PEqualNP.Outside.L_meta_29324_aux.certWord69
  | 0, 5 => PEqualNP.Outside.L_meta_29324_aux.certWord70
  | 0, 6 => PEqualNP.Outside.L_meta_29324_aux.certWord71
  | 0, 7 => PEqualNP.Outside.L_meta_29324_aux.certWord72
  | 0, 8 => PEqualNP.Outside.L_meta_29324_aux.certWord73
  | 0, 9 => PEqualNP.Outside.L_meta_29324_aux.certWord74
  | 0, 10 => PEqualNP.Outside.L_meta_29324_aux.certWord75
  | 0, 11 => PEqualNP.Outside.L_meta_29324_aux.certWord76
  | 0, 12 => PEqualNP.Outside.L_meta_29324_aux.certWord77
  | 0, 13 => PEqualNP.Outside.L_meta_29324_aux.certWord78
  | 0, 14 => PEqualNP.Outside.L_meta_29324_aux.certWord79
  | 0, 15 => PEqualNP.Outside.L_meta_29324_aux.certWord80
  | 1, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord81
  | 1, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord82
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord83
  | 5, 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord84
  | 5, 0, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord85
  | 6, 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord86
  | 6, 0, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord87
  | 6, 0, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord88
  | 6, 0, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord89
  | 6, 0, 4 => PEqualNP.Outside.L_meta_29324_aux.certWord90
  | 6, 0, 5 => PEqualNP.Outside.L_meta_29324_aux.certWord91
  | 6, 0, 6 => PEqualNP.Outside.L_meta_29324_aux.certWord92
  | 7, 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord93
  | 7, 0, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord94
  | 7, 0, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord95
  | 7, 0, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord96
  | 7, 0, 4 => PEqualNP.Outside.L_meta_29324_aux.certWord97
  | 7, 0, 5 => PEqualNP.Outside.L_meta_29324_aux.certWord98
  | 7, 0, 6 => PEqualNP.Outside.L_meta_29324_aux.certWord99
  | 7, 0, 7 => PEqualNP.Outside.L_meta_29324_aux.certWord100
  | 7, 0, 8 => PEqualNP.Outside.L_meta_29324_aux.certWord101
  | 7, 0, 9 => PEqualNP.Outside.L_meta_29324_aux.certWord102
  | 7, 0, 10 => PEqualNP.Outside.L_meta_29324_aux.certWord103
  | 8, 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord104
  | 8, 0, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord105
  | 8, 0, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord106
  | 8, 0, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord107
  | 9, 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord108
  | 10, 0, 0 => 0x7868543f302c6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 44
  | 5 => 52
  | 6 => 60
  | 7 => 68
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord109
  | 0, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord110
  | 0, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord111
  | 0, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord112
  | 0, 4 => PEqualNP.Outside.L_meta_29324_aux.certWord113
  | 0, 5 => PEqualNP.Outside.L_meta_29324_aux.certWord114
  | 0, 6 => PEqualNP.Outside.L_meta_29324_aux.certWord115
  | 0, 7 => PEqualNP.Outside.L_meta_29324_aux.certWord116
  | 0, 8 => PEqualNP.Outside.L_meta_29324_aux.certWord117
  | 0, 9 => PEqualNP.Outside.L_meta_29324_aux.certWord118
  | 0, 10 => PEqualNP.Outside.L_meta_29324_aux.certWord119
  | 0, 11 => PEqualNP.Outside.L_meta_29324_aux.certWord120
  | 0, 12 => PEqualNP.Outside.L_meta_29324_aux.certWord121
  | 0, 13 => PEqualNP.Outside.L_meta_29324_aux.certWord122
  | 0, 14 => PEqualNP.Outside.L_meta_29324_aux.certWord123
  | 0, 15 => PEqualNP.Outside.L_meta_29324_aux.certWord124
  | 1, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord125
  | 1, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord126
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord127
  | 0, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord128
  | 0, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord129
  | 0, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord130
  | 0, 4 => PEqualNP.Outside.L_meta_29324_aux.certWord131
  | 0, 5 => PEqualNP.Outside.L_meta_29324_aux.certWord132
  | 0, 6 => PEqualNP.Outside.L_meta_29324_aux.certWord133
  | 0, 7 => PEqualNP.Outside.L_meta_29324_aux.certWord134
  | 0, 8 => PEqualNP.Outside.L_meta_29324_aux.certWord135
  | 0, 9 => PEqualNP.Outside.L_meta_29324_aux.certWord136
  | 0, 10 => PEqualNP.Outside.L_meta_29324_aux.certWord137
  | 0, 11 => PEqualNP.Outside.L_meta_29324_aux.certWord138
  | 0, 12 => PEqualNP.Outside.L_meta_29324_aux.certWord139
  | 0, 13 => PEqualNP.Outside.L_meta_29324_aux.certWord140
  | 0, 14 => PEqualNP.Outside.L_meta_29324_aux.certWord141
  | 0, 15 => PEqualNP.Outside.L_meta_29324_aux.certWord142
  | 1, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord143
  | 1, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord144
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 42 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 42 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 138 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 138 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 138 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 138 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 8 0) :: stateWiresD n (ids >>> 8)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 8 0) :: stateWiresS n (ids >>> 8)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 3 => 2
  | 4 => 22
  | 5 => 230
  | 6 => 744
  | 7 => 1111
  | 8 => 181
  | 9 => 8
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0x419c7c502d93c148
  | 4, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord145
  | 5, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord146
  | 5, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord147
  | 5, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord148
  | 5, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord149
  | 6, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord150
  | 6, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord151
  | 6, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord152
  | 6, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord153
  | 6, 4 => PEqualNP.Outside.L_meta_29324_aux.certWord154
  | 6, 5 => PEqualNP.Outside.L_meta_29324_aux.certWord155
  | 6, 6 => PEqualNP.Outside.L_meta_29324_aux.certWord156
  | 6, 7 => PEqualNP.Outside.L_meta_29324_aux.certWord157
  | 6, 8 => PEqualNP.Outside.L_meta_29324_aux.certWord158
  | 6, 9 => PEqualNP.Outside.L_meta_29324_aux.certWord159
  | 6, 10 => PEqualNP.Outside.L_meta_29324_aux.certWord160
  | 6, 11 => PEqualNP.Outside.L_meta_29324_aux.certWord161
  | 7, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord162
  | 7, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord163
  | 7, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord164
  | 7, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord165
  | 7, 4 => PEqualNP.Outside.L_meta_29324_aux.certWord166
  | 7, 5 => PEqualNP.Outside.L_meta_29324_aux.certWord167
  | 7, 6 => PEqualNP.Outside.L_meta_29324_aux.certWord168
  | 7, 7 => PEqualNP.Outside.L_meta_29324_aux.certWord169
  | 7, 8 => PEqualNP.Outside.L_meta_29324_aux.certWord170
  | 7, 9 => PEqualNP.Outside.L_meta_29324_aux.certWord171
  | 7, 10 => PEqualNP.Outside.L_meta_29324_aux.certWord172
  | 7, 11 => PEqualNP.Outside.L_meta_29324_aux.certWord173
  | 7, 12 => PEqualNP.Outside.L_meta_29324_aux.certWord174
  | 7, 13 => PEqualNP.Outside.L_meta_29324_aux.certWord175
  | 7, 14 => PEqualNP.Outside.L_meta_29324_aux.certWord176
  | 7, 15 => PEqualNP.Outside.L_meta_29324_aux.certWord177
  | 7, 16 => PEqualNP.Outside.L_meta_29324_aux.certWord178
  | 7, 17 => PEqualNP.Outside.L_meta_29324_aux.certWord179
  | 8, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord180
  | 8, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord181
  | 8, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord182
  | 9, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord183
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord184
  | 4, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord185
  | 5, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord186
  | 5, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord187
  | 5, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord188
  | 5, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord189
  | 5, 4 => PEqualNP.Outside.L_meta_29324_aux.certWord190
  | 5, 5 => PEqualNP.Outside.L_meta_29324_aux.certWord191
  | 5, 6 => PEqualNP.Outside.L_meta_29324_aux.certWord192
  | 5, 7 => PEqualNP.Outside.L_meta_29324_aux.certWord193
  | 6, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord194
  | 6, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord195
  | 6, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord196
  | 6, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord197
  | 6, 4 => PEqualNP.Outside.L_meta_29324_aux.certWord198
  | 6, 5 => PEqualNP.Outside.L_meta_29324_aux.certWord199
  | 6, 6 => PEqualNP.Outside.L_meta_29324_aux.certWord200
  | 6, 7 => PEqualNP.Outside.L_meta_29324_aux.certWord201
  | 6, 8 => PEqualNP.Outside.L_meta_29324_aux.certWord202
  | 6, 9 => PEqualNP.Outside.L_meta_29324_aux.certWord203
  | 6, 10 => PEqualNP.Outside.L_meta_29324_aux.certWord204
  | 6, 11 => PEqualNP.Outside.L_meta_29324_aux.certWord205
  | 6, 12 => PEqualNP.Outside.L_meta_29324_aux.certWord206
  | 6, 13 => PEqualNP.Outside.L_meta_29324_aux.certWord207
  | 6, 14 => PEqualNP.Outside.L_meta_29324_aux.certWord208
  | 6, 15 => PEqualNP.Outside.L_meta_29324_aux.certWord209
  | 6, 16 => PEqualNP.Outside.L_meta_29324_aux.certWord210
  | 6, 17 => PEqualNP.Outside.L_meta_29324_aux.certWord211
  | 6, 18 => PEqualNP.Outside.L_meta_29324_aux.certWord212
  | 6, 19 => PEqualNP.Outside.L_meta_29324_aux.certWord213
  | 6, 20 => PEqualNP.Outside.L_meta_29324_aux.certWord214
  | 6, 21 => PEqualNP.Outside.L_meta_29324_aux.certWord215
  | 6, 22 => PEqualNP.Outside.L_meta_29324_aux.certWord216
  | 6, 23 => PEqualNP.Outside.L_meta_29324_aux.certWord217
  | 7, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord218
  | 7, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord219
  | 7, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord220
  | 7, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord221
  | 7, 4 => PEqualNP.Outside.L_meta_29324_aux.certWord222
  | 7, 5 => PEqualNP.Outside.L_meta_29324_aux.certWord223
  | 7, 6 => PEqualNP.Outside.L_meta_29324_aux.certWord224
  | 7, 7 => PEqualNP.Outside.L_meta_29324_aux.certWord225
  | 7, 8 => PEqualNP.Outside.L_meta_29324_aux.certWord226
  | 7, 9 => PEqualNP.Outside.L_meta_29324_aux.certWord227
  | 7, 10 => PEqualNP.Outside.L_meta_29324_aux.certWord228
  | 7, 11 => PEqualNP.Outside.L_meta_29324_aux.certWord229
  | 7, 12 => PEqualNP.Outside.L_meta_29324_aux.certWord230
  | 7, 13 => PEqualNP.Outside.L_meta_29324_aux.certWord231
  | 7, 14 => PEqualNP.Outside.L_meta_29324_aux.certWord232
  | 7, 15 => PEqualNP.Outside.L_meta_29324_aux.certWord233
  | 7, 16 => PEqualNP.Outside.L_meta_29324_aux.certWord234
  | 7, 17 => PEqualNP.Outside.L_meta_29324_aux.certWord235
  | 7, 18 => PEqualNP.Outside.L_meta_29324_aux.certWord236
  | 7, 19 => PEqualNP.Outside.L_meta_29324_aux.certWord237
  | 7, 20 => PEqualNP.Outside.L_meta_29324_aux.certWord238
  | 7, 21 => PEqualNP.Outside.L_meta_29324_aux.certWord239
  | 7, 22 => PEqualNP.Outside.L_meta_29324_aux.certWord240
  | 7, 23 => PEqualNP.Outside.L_meta_29324_aux.certWord241
  | 7, 24 => PEqualNP.Outside.L_meta_29324_aux.certWord242
  | 7, 25 => PEqualNP.Outside.L_meta_29324_aux.certWord243
  | 7, 26 => PEqualNP.Outside.L_meta_29324_aux.certWord244
  | 7, 27 => PEqualNP.Outside.L_meta_29324_aux.certWord245
  | 7, 28 => PEqualNP.Outside.L_meta_29324_aux.certWord246
  | 7, 29 => PEqualNP.Outside.L_meta_29324_aux.certWord247
  | 7, 30 => PEqualNP.Outside.L_meta_29324_aux.certWord248
  | 7, 31 => PEqualNP.Outside.L_meta_29324_aux.certWord249
  | 7, 32 => PEqualNP.Outside.L_meta_29324_aux.certWord250
  | 7, 33 => PEqualNP.Outside.L_meta_29324_aux.certWord251
  | 7, 34 => PEqualNP.Outside.L_meta_29324_aux.certWord252
  | 8, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord253
  | 8, 1 => PEqualNP.Outside.L_meta_29324_aux.certWord254
  | 8, 2 => PEqualNP.Outside.L_meta_29324_aux.certWord255
  | 8, 3 => PEqualNP.Outside.L_meta_29324_aux.certWord256
  | 8, 4 => PEqualNP.Outside.L_meta_29324_aux.certWord257
  | 8, 5 => PEqualNP.Outside.L_meta_29324_aux.certWord258
  | 9, 0 => PEqualNP.Outside.L_meta_29324_aux.certWord259
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_6 roots_6 8 s ws hint
  | 1 => checkCutEntry dom_11 roots_11 8 s ws hint
  | 2 => checkCutEntry dom_12 roots_12 8 s ws hint
  | 3 => checkCutEntry dom_13 roots_13 8 s ws hint
  | 4 => checkCutEntry dom_14 roots_14 8 s ws hint
  | 5 => checkCutEntry dom_10 roots_10 7 s ws hint
  | 6 => checkCutEntry dom_15 roots_15 6 s ws hint
  | 7 => checkCutEntry dom_18 roots_18 6 s ws hint
  | 8 => checkCutEntry dom_19 roots_19 6 s ws hint
  | 9 => checkCutEntry dom_20 roots_20 5 s ws hint
  | 10 => checkCutEntry dom_21 roots_21 5 s ws hint
  | 11 => checkCutEntry dom_22 roots_22 5 s ws hint
  | 12 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 13 => checkCutEntry dom_24 roots_24 5 s ws hint
  | 14 => checkCutEntry dom_25 roots_25 5 s ws hint
  | 15 => checkCutEntry dom_26 roots_26 5 s ws hint
  | 16 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 17 => checkCutEntry dom_27 roots_27 5 s ws hint
  | 18 => checkCutEntry dom_17 roots_17 5 s ws hint
  | 19 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 20 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 21 => checkCutEntry dom_7 roots_7 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_28 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_22 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_26 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_28 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4)], [(PEqualNP.Outside.L_meta_29324_aux.certWord15, 2), (PEqualNP.Outside.L_meta_29324_aux.certWord14, 4), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6)], [(PEqualNP.Outside.L_meta_29324_aux.certWord16, 6), (PEqualNP.Outside.L_meta_29324_aux.certWord13, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_28 == dom_28) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_28 goalM u ys) : RunD dom_28 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_28 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_16 : ∀ i, 16 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_24 : ∀ i, 24 ≤ i → i < 30 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 24 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 30 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (z5_24)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_8 : ∀ i, 8 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_16 : ∀ i, 16 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_24 : ∀ i, 24 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_32 : ∀ i, 32 ≤ i → i < 40 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_40 : ∀ i, 40 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_48 : ∀ i, 48 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_56 : ∀ i, 56 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_64 : ∀ i, 64 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_72 : ∀ i, 72 ≤ i → i < 80 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_80 : ∀ i, 80 ≤ i → i < 88 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_88 : ∀ i, 88 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_96 : ∀ i, 96 ≤ i → i < 104 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 96 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 104 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (z6_96))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_8 : ∀ i, 8 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_16 : ∀ i, 16 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_24 : ∀ i, 24 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_32 : ∀ i, 32 ≤ i → i < 40 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_40 : ∀ i, 40 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_48 : ∀ i, 48 ≤ i → i < 56 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_56 : ∀ i, 56 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_64 : ∀ i, 64 ≤ i → i < 72 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_72 : ∀ i, 72 ≤ i → i < 80 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_80 : ∀ i, 80 ≤ i → i < 88 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_88 : ∀ i, 88 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_96 : ∀ i, 96 ≤ i → i < 104 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_104 : ∀ i, 104 ≤ i → i < 112 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_112 : ∀ i, 112 ≤ i → i < 120 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_120 : ∀ i, 120 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_128 : ∀ i, 128 ≤ i → i < 136 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_136 : ∀ i, 136 ≤ i → i < 144 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_144 : ∀ i, 144 ≤ i → i < 152 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_152 : ∀ i, 152 ≤ i → i < 160 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_160 : ∀ i, 160 ≤ i → i < 162 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 160 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 162 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (z7_160))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_24 : ∀ i, 24 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_32 : ∀ i, 32 ≤ i → i < 40 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_40 : ∀ i, 40 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_48 : ∀ i, 48 ≤ i → i < 52 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 48 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 52 → Z 8 i = true := range_split z8_0 (range_split z8_8 (range_split z8_16 (range_split z8_24 (range_split z8_32 (range_split z8_40 (z8_48))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_0 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_8 : ∀ i, 8 ≤ i → i < 9 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 8 = true)
theorem z9 : ∀ i, 0 ≤ i → i < 9 → Z 9 i = true := range_split z9_0 (z9_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z10_0 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := z10_0
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
  · exact fun i hi => z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_28 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD dom_28 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_28 roots_28 goal_28 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_28 goal_28 := by
    have h0 : isConstB dom_28 goal_28 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_28

theorem low_28 : Lower dom_28 roots_28 goal_28 11 := S_28.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_28_bits : ∀ r : Fin 64, roots_28.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_28_lt : ∀ r : Fin 64, dom_28.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_28 T)
    (hlow : Lower dom_28 roots_28 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_28, Avail mask256 roots_28 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_28 hfan 0 roots_28 roots_28 rfl hsup0
  set out := (execN C.gates roots_28).getD C.output 0
  have hout : out &&& dom_28 = T &&& dom_28 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_28_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_28 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_28_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_28).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_28)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_28.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_28 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_28).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_28 &&& mask256 = dom_28 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_28 = T &&& dom_28 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_28, hd63, hout]
  have hnc_m : ¬ IsConst dom_28 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_28 roots_28 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_28, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_28 roots_28 0 roots_28 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3) || (x 4 && x 5)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_28.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem rootBound : ∀ t : ℕ, HasCircuitSize 6 fG t → 11 ≤ t :=
  lower_to_circuit6 fG goal_28 11 hT6 (by unfold IsConst; decide) low_28

end PEqualNP.Outside.L_meta_29324_aux

namespace PEqualNP.Outside.L_meta_29324
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

def g0 : (Fin 8 → Bool) → Bool := fun x => (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 7) || (x 2 && x 6) || (x 2 && x 7) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def g1 : (Fin 8 → Bool) → Bool := fun x => g0 (Function.update x 0 false)
theorem dep0 : ∃ x : Fin 8 → Bool, g0 (Function.update x 0 (!x 0)) ≠ g0 x :=
  ⟨fun i => decide (i = 4), by decide +kernel⟩
theorem keep0 : ∃ x y : Fin 8 → Bool, g0 (Function.update x 0 false) ≠ g0 (Function.update y 0 false) :=
  ⟨fun _ => false, fun i => decide (i = 1 ∨ i = 4), by decide +kernel⟩
def g2 : (Fin 8 → Bool) → Bool := fun x => g1 (Function.update x 3 false)
theorem dep1 : ∃ x : Fin 8 → Bool, g1 (Function.update x 3 (!x 3)) ≠ g1 x :=
  ⟨fun i => decide (i = 6), by decide +kernel⟩
theorem keep1 : ∃ x y : Fin 8 → Bool, g1 (Function.update x 3 false) ≠ g1 (Function.update y 3 false) :=
  ⟨fun _ => false, fun i => decide (i = 1 ∨ i = 4), by decide +kernel⟩
def identify (i : Fin 8) : Fin 6 := match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 0
  | 4 => 2
  | 5 => 3
  | 6 => 5
  | _ => 0
theorem image : (fun x : Fin 6 → Bool => g2 (x ∘ identify)) = PEqualNP.Outside.L_meta_29324_aux.fG := by decide +kernel

theorem lower (t : ℕ) (h0 : HasCircuitSize 8 g0 t) : 13 ≤ t := by
  obtain ⟨s1, c1, h1⟩ := one_gate_at 7 g0 0 false t dep0 keep0 h0
  change HasCircuitSize 8 g1 s1 at h1
  obtain ⟨s2, c2, h2⟩ := one_gate_at 7 g1 3 false s1 dep1 keep1 h1
  change HasCircuitSize 8 g2 s2 at h2
  have r := relabel_size identify g2 s2 h2
  rw [image] at r
  have hl := PEqualNP.Outside.L_meta_29324_aux.rootBound s2 r
  omega

def wg : List Gate := [⟨GateOp.or, [7, 0]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [8, 1]⟩, ⟨GateOp.or, [9, 2]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [7, 15]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.and, [13, 17]⟩, ⟨GateOp.and, [11, 6]⟩, ⟨GateOp.or, [18, 19]⟩]

theorem wfits : ∀ g ∈ wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wg, 20⟩ (List.ofFn x) = g0 x := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem bridge : ∀ x : Fin 8 → Bool, g0 x = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel

end PEqualNP.Outside.L_meta_29324

theorem PEqualNP.Outside.L_meta_29324 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  have h := PEqualNP.Outside.L_meta_29324.lower gates.length ⟨⟨gates, o⟩, legal, le_rfl, fun x => (computes x).trans (PEqualNP.Outside.L_meta_29324.bridge x).symm⟩
  have hw : PEqualNP.Outside.L_meta_29324.wg.length = 13 := rfl
  exact ⟨PEqualNP.Outside.L_meta_29324.wg, 20, PEqualNP.Outside.L_meta_29324.wfits, by omega, fun x => (PEqualNP.Outside.L_meta_29324.weval x).trans (PEqualNP.Outside.L_meta_29324.bridge x)⟩

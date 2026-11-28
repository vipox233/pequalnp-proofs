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

namespace PEqualNP.Outside.L_meta_28352_aux
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
def certWord12 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1103823437824 48) 16842752) 48) 1103806595328) 48) 1099528405248)
def certWord13 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294901760 48) 65535) 48) 0) 48) 281470681743360) 48) 4294901760)
def certWord14 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 280375465148160 48) 4278190080) 48) 280375465148160) 48) 4278190080) 48) 280375465148160)
def certWord15 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4278255360 48) 65280) 48) 280375465082880) 48) 280379743272960) 48) 4278255360)
def certWord16 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3084 48) 13245881256972) 48) 13245881256972) 48) 13245881256972) 48) 13245881256972) 48) 13245881256972)
def certWord17 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 8738 48) 37529996894754) 48) 37529996894754) 48) 37529996894754) 48) 37529996894754) 48) 37529996894754)
def certWord18 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2570 48) 11038234380810) 48) 11038234380810) 48) 11038234380810) 48) 11038234380810) 48) 11038234380810)
def certWord19 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 240 48) 1030807879920) 48) 1030807879920) 48) 1030807879920) 48) 1030807879920) 48) 1030807879920)
def certWord20 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 858980352 48) 13056) 48) 56075093016576) 48) 52983525015552) 48) 572662306)
def certWord21 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3435973836 48) 52428) 48) 225176545394688) 48) 225179981316096) 48) 3435973836)
def certWord22 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 56294995329024 48) 858980352) 48) 56294136361728) 48) 56075948667648) 48) 52983525027888) 48) 52983289225762) 48) 37529996886016) 48) 858993459)
def certWord23 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4123168636416 48) 16911548447) 48) 61094756351)
def certWord24 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4280242437778 48) 22316423954751) 48) 5077616258485)
def certWord25 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3320437960 48) 217561583893201) 48) 45233308990846) 48) 184533233539410) 48) 168025876070269) 48) 118872211876181) 48) 217313833592821) 48) 71251456638524) 48) 181665172341211) 48) 60374985419460) 48) 271463908018409) 48) 20819707627625) 48) 72516232480355)
def certWord26 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 274878038016 48) 8796093022208) 48) 16777232) 48) 536871104) 48) 4294967296) 48) 206158430208) 48) 3298534883328) 48) 17592186044418)
def certWord27 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4415293751296 48) 67371008) 48) 4415226381312) 48) 4398113620992)
def certWord28 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 264913582878960 48) 4042260480) 48) 264913582878960) 48) 4042260480) 48) 264913582878960)
def certWord29 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 170 48) 730155581610) 48) 730155581610) 48) 730155581610) 48) 730155581610) 48) 730155581610)
def certWord30 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3855 48) 16557351567360) 48) 16557351567360) 48) 252641280) 48) 16557098929920) 48) 16492926078720) 48) 13245881256972) 48) 13245847570954) 48) 11038234378240) 48) 16557098929935)
def certWord31 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 16773120 48) 277076930457600) 48) 68465954312) 48) 7650152447)
def certWord32 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 16776630 48) 279590099743890) 48) 80470253735497) 48) 40217258756973)
def certWord33 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3280106625 48) 93010789344318) 48) 35489417491800)
def certWord34 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 246393126440215 48) 128242470812592) 48) 214965067821024) 48) 171264581187265) 48) 177516483613437) 48) 73072734329960) 48) 148469721494136) 48) 65414262052209) 48) 121613932195325) 48) 155226228475295) 48) 99216331790456) 48) 215355241543005) 48) 76523491836301) 48) 203891397968628) 48) 44402087892180) 48) 190000770299809)
def certWord35 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 134217760 48) 0) 48) 34359738368) 48) 824633720832) 48) 3145728) 48) 16777216) 48) 0) 48) 21474836480) 48) 343597416448) 48) 2199024566272) 48) 87960946999298)
def certWord36 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 225176545447116 48) 3435921408) 48) 225176545447116) 48) 3435921408) 48) 225176545447116)
def certWord37 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2886017630 48) 64233605769067) 48) 257574027232746)
def certWord38 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281473545011200 48) 4294901760) 48) 65280) 48) 280375465082880) 48) 275955859456000) 48) 4042322160) 48) 52428) 48) 225176545394688) 48) 187649984430080) 48) 1431655765)
def certWord39 : Nat := (Nat.lor (Nat.shiftLeft 114694580944 48) 105189213572374)
def certWord40 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 255 48) 31756979798016) 48) 70094336270142) 48) 66587131952) 48) 496202925628)
def certWord41 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 255 48) 209886458232996) 48) 210917752029182) 48) 145821704593780) 48) 163773809002040)
def certWord42 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2886017630 48) 90633557255735) 48) 54069833301183)
def certWord43 : Nat := (Nat.lor (Nat.shiftLeft 40889115679626 48) 139573590086625)
def certWord44 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 187647121205930 48) 2863267840) 48) 187647121205930) 48) 2863267840) 48) 187647121205930)
def certWord45 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 204 48) 876186697932) 48) 876186697932) 48) 876186697932) 48) 876186697932) 48) 876186697932)
def certWord46 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2863311530 48) 43690) 48) 187647121162240) 48) 187649984430080) 48) 2863311530)
def certWord47 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4042322160 48) 61680) 48) 264913582817280) 48) 264917625077760) 48) 4042322160)
def certWord48 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3735797812 48) 243106884796833) 48) 32060579928349) 48) 188396211577964) 48) 188796384968847) 48) 155329116471902) 48) 187520276202691) 48) 127051156838863) 48) 195469713728162) 48) 93375378903246) 48) 147877078191627) 48) 76939620269842) 48) 264085607539242) 48) 55948672052066) 48) 126981164240686) 48) 25161012872239) 48) 151595167242038)
def certWord49 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2096046604 48) 134742970757904) 48) 78032822136097) 48) 118810593618185) 48) 114754661238697) 48) 112594076198119) 48) 132514273584695) 48) 103192019948402) 48) 82713870155676) 48) 87945988886517) 48) 276090413453264) 48) 86462601645411) 48) 15110974624862) 48) 81973743995193) 48) 248280397991106) 48) 78555756447162) 48) 166899302790552) 48) 73548004671807) 48) 53232885413743) 48) 67261271718833) 48) 271584645333510) 48) 60731077571855) 48) 129103266195486) 48) 55104500346709) 48) 202194966733011) 48) 50547543059091) 48) 147013134920548) 48) 45427815950603) 48) 275320962033353) 48) 38413706142444) 48) 107220108362785) 48) 31434501331386) 48) 52888633724656) 48) 26453625804693) 48) 112726097292534) 48) 22093373837967) 48) 220010006481014) 48) 17502364437807) 48) 269612489541743) 48) 11436725963033) 48) 168740733175503) 48) 1804900368796) 48) 155795669416407)
def certWord50 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 65416 48) 270471158398977) 48) 268587835387635) 48) 6931612713142) 48) 245958357606051) 48) 196202087280415) 48) 237986175962244) 48) 83952859109647) 48) 207291880945454) 48) 59973594714226) 48) 194001393198981) 48) 68327110437305) 48) 175208411930304) 48) 236986041160854) 48) 171460561705956) 48) 32274858045923) 48) 156688291564690) 48) 158662744793485) 48) 152437687028174) 48) 249990879873246) 48) 148879924627012) 48) 135723203150948) 48) 144986510296026) 48) 245858924233194)
def certWord51 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1461819679 48) 91322836800242) 48) 279981683464063) 48) 87348848970837) 48) 79801763850649) 48) 72657874796863) 48) 53232880177217) 48) 66992086268961) 48) 273843801693337) 48) 60424152102357) 48) 266366180293651) 48) 58678544577289) 48) 107366421971453) 48) 54117041385769) 48) 190486896277238) 48) 52185291829042) 48) 46622659797509) 48) 50199752092840) 48) 36709815378541) 48) 46114820860393) 48) 73410271901857) 48) 44687662392860) 48) 53451456280123) 48) 38238984282649) 48) 259528254393109) 48) 36143287246889) 48) 51518647827147) 48) 33247578955049) 48) 279319384849182) 48) 27642057922689) 48) 271055693162037) 48) 19344822374462) 48) 190396160841785) 48) 16108501405309) 48) 228806020426690) 48) 14714339527851) 48) 244134702773778) 48) 10918267127768) 48) 50835330934590) 48) 6241379418687) 48) 17849910194366) 48) 1104867098758) 48) 181470960759929)
def certWord52 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 267436336148931 48) 24841804777037) 48) 262364598164006) 48) 196579940651949) 48) 230708301320489) 48) 66094422083456) 48) 217054815241049) 48) 151860205487325) 48) 198893223325745) 48) 222533774030489) 48) 187740046730799) 48) 185987734622054) 48) 180260907623177) 48) 53930231389731) 48) 170552475031267) 48) 277307008322834) 48) 157703213452638) 48) 187988635663148) 48) 137668427610917) 48) 269030211189853) 48) 134055821277665) 48) 99129868048245) 48) 131740434724720) 48) 60745721125439) 48) 128917882565722) 48) 114471388052770) 48) 125775137370652) 48) 237715434369315) 48) 121764326239179) 48) 109931472912811) 48) 115435164886788) 48) 83890997102244) 48) 106332853460922) 48) 218791519121863) 48) 102504870468419) 48) 150600262798681)
def certWord53 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 62267 48) 105351026658015) 48) 183196242315960) 48) 82864788889441) 48) 123537715061194) 48) 70404709992189) 48) 89864306380889) 48) 109114901295993) 48) 73355787189799) 48) 140734066216812) 48) 24215366143614) 48) 23171433930416)
def certWord54 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 93824992215040 48) 858993459) 48) 1285) 48) 5519032975360) 48) 1099511562240) 48) 16711935) 48) 15) 48) 64424509440) 48) 252641280) 48) 255)
def certWord55 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 5570645 48) 365077790720) 48) 281470681808895) 48) 4278190080) 48) 280375465086735) 48) 252641280) 48) 5519032976645) 48) 16711680) 48) 1095216660565) 48) 5570560) 48) 4294967295)
def certWord56 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4042322160 48) 264917625138926) 48) 262709978263278) 48) 225179981368524) 48) 225179408706218) 48) 187649984451925) 48) 93824992236885) 48) 56294995342131) 48) 56294388993807) 48) 16557351567615) 48) 1095233372415)
def certWord57 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4278255360 48) 280379744321280) 48) 280379743338240) 48) 280379743338240) 48) 263887068856575) 48) 280375481859840) 48) 4278190080) 48) 278163506396412) 48) 278163472710394) 48) 275955859517680) 48) 264982049648895)
def certWord58 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294901760 48) 225176545460218) 48) 281453501546490) 48) 281410551218160) 48) 281410551214320) 48) 281410299559884) 48) 281255930036172) 48) 281255074398156) 48) 225180834791338) 48) 281109898919850) 48) 187651410537130)
def certWord59 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294967040 48) 281474959998975) 48) 280379760036864) 48) 281474892496895) 48) 275955943731440) 48) 281474724069375) 48) 225180840348876) 48) 281473545076735) 48) 187651416064000) 48) 281470681808895) 48) 4289331200)
def certWord60 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294967295 48) 225179981381631) 48) 281473545054890) 48) 281474976645120) 48) 1099511627775) 48) 65535) 48) 281453501874170) 48) 281474975727615) 48) 281410552201164) 48) 281474973368319) 48) 281109904490410)
def certWord61 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4294967295 48) 281410551218175) 48) 281474973368268) 48) 281474976710604) 48) 225180840361983) 48) 281109898919935) 48) 281474959998720) 48) 281474976710400) 48) 4294967295) 48) 275955859521535) 48) 281474724065520)
def certWord62 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281474976710655 48) 281109904490495) 48) 281474959998975) 48) 281474976706800) 48) 281474976710655) 48) 187651416129535) 48) 281470681808895) 48) 281474976382970)
def certWord63 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 28377 48) 108386827504566) 48) 76736375483798) 48) 186076733945438) 48) 145931555238265) 48) 126053427410411) 48) 16580294102935) 48) 46530017832532) 48) 176636684749411) 48) 217540284745612) 48) 164267664742186) 48) 89755074335913) 48) 77527807288037) 48) 98799385725588) 48) 113170646121565) 48) 140940129116229)
def certWord64 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 464867960 48) 203712056091155) 48) 41068673730890) 48) 163176789808938) 48) 89611177999545) 48) 76359642813381) 48) 26403896904202) 48) 88026918104657) 48) 70593028073797)
def certWord65 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2295423458 48) 252106992159702) 48) 25470529385554) 48) 168162778546667) 48) 181589264066285) 48) 24366362698689) 48) 115057500529949) 48) 178755562279958) 48) 262620780332217) 48) 96227958592453) 48) 222909195506327) 48) 46531075330692) 48) 265474311037266) 48) 145445014252820) 48) 173921825685614) 48) 238909477099523) 48) 130336345497806) 48) 100838625818951)
def certWord66 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 15317651 48) 217472236424020) 48) 173921846146142) 48) 181459995259323) 48) 111220519892845) 48) 22703974425531) 48) 123906751112476) 48) 4495934166826) 48) 211171012002928) 48) 147819108942789) 48) 81604494857377) 48) 66372716417668) 48) 221494397219573) 48) 43480444734228) 48) 182778048265320) 48) 176958870985731) 48) 73551466994880) 48) 28764071823622)
def certWord67 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1859209698 48) 251814926952331) 48) 163999129416530) 48) 132737349378490) 48) 181589264070282) 48) 86960912739252) 48) 90678458744988) 48) 31336404264) 48) 191156801264801) 48) 7700086870628) 48) 78286357763230) 48) 50929087364188) 48) 186097964262035) 48) 218023620249483) 48) 162883283661918) 48) 194654136245250) 48) 162474469953741) 48) 239909666863431)
def certWord68 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1926324883 48) 216922558238164) 48) 166199155340370) 48) 146000747352393) 48) 249614013069197) 48) 26015394210756) 48) 115160311309597) 48) 178967668529450) 48) 246411791865073) 48) 76969532388197) 48) 222325065387799) 48) 46531100562052) 48) 203764220934981) 48) 45144743087578) 48) 25461647409262) 48) 230112572479923) 48) 76460334852832) 48) 28704043737254)
def certWord69 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1755640178 48) 181420417256596) 48) 173904597362986) 48) 88549358305803) 48) 199998550859789) 48) 233775846931200) 48) 121879526540376) 48) 3807661462306) 48) 229100740172969) 48) 78068092859045) 48) 2422754497687) 48) 46530605366364) 48) 176887373085541) 48) 43480444759318) 48) 45399828316524) 48) 181357458578435) 48) 183119346215120) 48) 99137550334295)
def certWord70 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 13678930 48) 145166473546703) 48) 25470529317180) 48) 101882012829154) 48) 162477716567789) 48) 22704209830784) 48) 90678188188184) 48) 2835878745104) 48) 211225255508169) 48) 130295639171813) 48) 81618715430679) 48) 46530605037148) 48) 186096856965780) 48) 184213637696783) 48) 22145999779688) 48) 181356915235842) 48) 163309866455232) 48) 12735253344390)
def certWord71 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 13406 48) 119543209040899) 48) 165933093431502) 48) 239901075089735)
def certWord72 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4050822407 48) 9243526146364) 48) 101882127241545) 48) 179105673801742) 48) 169501897042247) 48) 899704669514) 48) 19172735360554) 48) 88547293978018) 48) 216773636157454) 48) 239870641219895) 48) 132876130829770) 48) 163277709126226) 48) 132737155507441) 48) 126053113165549) 48) 26015629617480) 48) 934735521675) 48) 164308270591798) 48) 101882101420361) 48) 249751452024842) 48) 233775847219335)
def certWord73 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 709372339530 48) 9307413621052) 48) 101882127241545) 48) 249474417913869) 48) 16600825897191) 48) 899302074250) 48) 163208976902460) 48) 101847213801801) 48) 249473326933901) 48) 22682734995784) 48) 119646143571274) 48) 18142216431932) 48) 101882110411170) 48) 163035005345806) 48) 239870741883207) 48) 1123720349130) 48) 163236873019708) 48) 101882127230217) 48) 249474417455117) 48) 25968149569767)
def certWord74 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1158073796042 48) 163208976340778) 48) 88514570146121) 48) 249474417983503) 48) 239870641219911) 48) 899033523530) 48) 18101338152500) 48) 101882134974793) 48) 249475500376064) 48) 28764477634902) 48) 708428621130) 48) 9277378537802) 48) 101882118729122) 48) 162477716570112) 48) 28716928637158) 48) 1123982493130) 48) 163209031592252) 48) 101881848833265) 48) 126053130338304) 48) 28764408158486)
def certWord75 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 951921747851 48) 163208993843502) 48) 93050591437218) 48) 162477716572272) 48) 99133152864584) 48) 143835399382410) 48) 163277709125966) 48) 132737163252058) 48) 162477716570125) 48) 22699914864951) 48) 898887771466) 48) 11476389210442) 48) 132668436042114) 48) 162477716566016) 48) 28764408682790) 48) 708429669706) 48) 9305257814332) 48) 101882127188411) 48) 76028606177293) 48) 24366126768391)
def certWord76 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 7438935947 48) 163140039586898) 48) 132736870306146) 48) 162477716500493) 48) 22669547309287) 48) 951903774026) 48) 15874448304444) 48) 101847213801890) 48) 162477707255821) 48) 239870641748295) 48) 898887771466) 48) 8177845938492) 48) 93050852397434) 48) 215254274699264) 48) 28716928639206) 48) 146070270363082) 48) 163309371564348) 48) 101882136154490) 48) 162477716570126) 48) 239823161172199)
def certWord77 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 115058719049162 48) 163312592790844) 48) 101882127241546) 48) 21740219691008) 48) 28716928372966) 48) 115214554219978) 48) 163312592789820) 48) 101882127254945) 48) 249474417850318) 48) 239870641219912) 48) 951915365834) 48) 18073224093226) 48) 88548904589730) 48) 162477708046349) 48) 22704209832263) 48) 898887771466) 48) 3779790313258) 48) 88445580519753) 48) 249474417985293) 48) 26015629617480)
def certWord78 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 986275104202 48) 163208759159100) 48) 101882100499834) 48) 162477716571787) 48) 22682734995784) 48) 899290424650) 48) 15902314896946) 48) 101882127230193) 48) 161513487233037) 48) 24366362700103) 48) 119646557816266) 48) 163277763651900) 48) 101882119384482) 48) 162477716570125) 48) 169501897570647) 48) 898895168970) 48) 20272444120622) 48) 93048436478193) 48) 179105673670669) 48) 19371079803111)
def certWord79 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 53626 48) 162477716567691) 48) 233775847219368) 48) 7003612424) 48) 15805712050492) 48) 119543015987618) 48) 161513487758986) 48) 163437403220296)
def certWord80 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 10809714 48) 181437404212500) 48) 173921774741820) 48) 119543209840970) 48) 92108972388365) 48) 22669614420788) 48) 90730939983132) 48) 3589616079900) 48) 226336878386345) 48) 78514909471461) 48) 81618983866135) 48) 46530605372024) 48) 203764202840723) 48) 217473864862287) 48) 25479166014546) 48) 132737348672515) 48) 76036147848909) 48) 22669682321735)
def certWord81 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1099479924224 48) 66213363216384) 48) 281345060242431) 48) 281474959998944) 48) 4396973029376) 48) 2130303909824) 48) 136339441848319)
def certWord82 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281474439855679 48) 211140592267264) 48) 2197949774848) 48) 140669305683998) 48) 30813164929024) 48) 281474708275203) 48) 246307784491007)
def certWord83 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1030792411196 48) 4157409984256) 48) 265944381259776) 48) 8310895935486) 48) 31052680411263) 48) 279825457610688) 48) 140737479970815)
def certWord84 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 536610752 48) 34342961152) 48) 261120) 48) 68702699520) 48) 1010812800) 48) 280925472562751) 48) 175920786706431)
def certWord85 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 64424509440 48) 66005057302543) 48) 2199014867904) 48) 68198338335) 48) 277103706883968) 48) 1649267572732) 48) 30786326073095)
def certWord86 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1099511365632 48) 70366596694031) 48) 279405869663231) 48) 140805686755326) 48) 25773996152) 48) 264364095307776) 48) 0)
def certWord87 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 280440392910399 48) 211108261560304) 48) 1073740800) 48) 65535) 48) 281448137359359) 48) 279340646399936) 48) 105570296135431)
def certWord88 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281406794102847 48) 215263744200688) 48) 265944381520896) 48) 140733327540255) 48) 277077999747072) 48) 68702707263) 48) 175920786706400)
def certWord89 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4095 48) 281474911698943) 48) 281406274011104) 48) 4364760512632) 48) 264432546349056) 48) 4396981157863)
def certWord90 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 439362526208 48) 22094173970432) 48) 75318693986508) 48) 168875882722080) 48) 1437740320768) 48) 755914252800) 48) 39582418600249)
def certWord91 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 187649268657181 48) 211131427705920) 48) 1611837559808) 48) 84387739992080) 48) 17592399953920) 48) 171326782308354) 48) 211114247567227)
def certWord92 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 38422849256508 48) 87754653564674) 48) 265953046971460) 48) 157844610412252) 48) 31044089952375) 48) 259956399913856) 48) 69195924508095)
def certWord93 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 75060458852945 48) 18794762470468) 48) 76818862361873) 48) 37562659914824) 48) 149534600578969) 48) 281007885549183) 48) 277969344995325)
def certWord94 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 150287482355741 48) 279138514499183) 48) 112150181874649) 48) 56349718507359) 48) 278032495138730) 48) 21532102885373) 48) 66268487986959)
def certWord95 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 225399883534515 48) 70368446393279) 48) 280371170028543) 48) 197087240716286) 48) 186156339690234) 48) 264950358378640) 48) 11147447247874)
def certWord96 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281129755242367 48) 253355775033336) 48) 150706761236002) 48) 75078259703807) 48) 281474905407487) 48) 280580818206685) 48) 263298675113807)
def certWord97 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 281470144871743 48) 277042566258686) 48) 279257279889271) 48) 281474171391199) 48) 280037235570278) 48) 149877174271871) 48) 281474613207028)
def certWord98 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4095 48) 281474964127743) 48) 281469725442045) 48) 246280940945150) 48) 273778395290034) 48) 30786325577727)
def certWord99 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 61306 48) 14494977870702) 48) 229577197532346) 48) 192408799227682) 48) 167222645855911) 48) 183109770562387) 48) 155329116474566) 48) 258623805564564) 48) 147149715372394) 48) 193249691381253) 48) 118269666352998) 48) 57601347968446) 48) 96939759194582) 48) 186518916034133) 48) 85826816657450) 48) 70846684213237) 48) 75046908341502) 48) 167019145200276) 48) 45077451318703) 48) 179830880310450) 48) 33450643230284) 48) 220748653686962) 48) 13366381054040) 48) 203040363059765)
def certWord100 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 949903343 48) 61997180532416) 48) 451878583601) 48) 59322167539156) 48) 13534336630043) 48) 57173926753192) 48) 194438316846231) 48) 55172074254517) 48) 214083436685927) 48) 51884073496357) 48) 224262505385478) 48) 48422228798128) 48) 88876455010345) 48) 45498005792230) 48) 230640355904169) 48) 39825245872939) 48) 135025769768570) 48) 38223458148661) 48) 226912265444204) 48) 35405748379456) 48) 164282980793118) 48) 30667272428502) 48) 7237484341198) 48) 30271843015307) 48) 96181935692428) 48) 28063394436860) 48) 119804195108702) 48) 24673167414747) 48) 154584803810530) 48) 22076465943352) 48) 223634961202603) 48) 19499433398626) 48) 179744671744142) 48) 17291172515281) 48) 169788868967687) 48) 13073027762975) 48) 249705286335270) 48) 10794679011071) 48) 258067520359894) 48) 3102275797597) 48) 34063402483510) 48) 1100183306435) 48) 225030525063395)
def certWord101 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2096567640 48) 134875487303536) 48) 13174629078001) 48) 128118397432517) 48) 235434846977314) 48) 123966609911961) 48) 5215929888486) 48) 118393662433834) 48) 176391785600917) 48) 110753828135751) 48) 83512986703742) 48) 106565546041443) 48) 224143063400552) 48) 103721227738206) 48) 129267176059922) 48) 99371870280278) 48) 57768816687359) 48) 97809973336300) 48) 157210165161593) 48) 96284545144704) 48) 267887152957072) 48) 95064275637229) 48) 24250785352506) 48) 91061052985927) 48) 224572325883841) 48) 87969988497321) 48) 45953190076020) 48) 85749608435034) 48) 216763986030453) 48) 83738753714652) 48) 271980013108556) 48) 78555756447444) 48) 123215207164416) 48) 76026600702690) 48) 59722639571363) 48) 73192809513495) 48) 123541540865491) 48) 72106763829246) 48) 179685285086960) 48) 66871508221086) 48) 243989499278563) 48) 63485680630134) 48) 212700617573822)
def certWord102 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4267454971 48) 269044357133145) 48) 64866544920246) 48) 256954115024833) 48) 27397153450469) 48) 241417275561985) 48) 258668025805696) 48) 236529775269132) 48) 33375439254313) 48) 229975032385442) 48) 28599373091371) 48) 226466184284914) 48) 80632804675701) 48) 219655135085491) 48) 216924859830275) 48) 211611457404815) 48) 158839517751337) 48) 195180118060927) 48) 42411450969085) 48) 191005493800335) 48) 116916191694679) 48) 188391732979468) 48) 269572065457968) 48) 177558247153647) 48) 113746238648438) 48) 168044196698076) 48) 88758017114387) 48) 163940777170132) 48) 178900743458013) 48) 161332444237903) 48) 213140156097431) 48) 156790395342141) 48) 41049364584735) 48) 152509196896724) 48) 73347361273802) 48) 142544721641806) 48) 90033258222942)
def certWord103 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 230118210 48) 15011499281780) 48) 142271013855046) 48) 14225436052692) 48) 199351118004335) 48) 13809918217356) 48) 84452151807471) 48) 13610163637321) 48) 155632640540542) 48) 13150697425879) 48) 13172860830638) 48) 12766102293339) 48) 232710107882222) 48) 12354213055276) 48) 154919656652131) 48) 12057040390894) 48) 11755508158380) 48) 11751940295338) 48) 82283161730448) 48) 11503934966359) 48) 136288065638895) 48) 10589499033912) 48) 62723852761105) 48) 9813933164737) 48) 9573620007934) 48) 8921124046835) 48) 146784921897482) 48) 7679065458372) 48) 71730355590789) 48) 6840395892090) 48) 174560446161068) 48) 5594709755143) 48) 41163046265306) 48) 4721579983488) 48) 216672550144466) 48) 2509129384482) 48) 139315885886160) 48) 2045830365605) 48) 253385916973660) 48) 1639327007058) 48) 157616731836103) 48) 1104867098791) 48) 182291300817588)
def certWord104 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 445703273 48) 28950409321010) 48) 91152526269212) 48) 28155998378319) 48) 162418905451990) 48) 27635118905583) 48) 83215406009843) 48) 27171044137089) 48) 271055796600829) 48) 26553660086307) 48) 161370910576914) 48) 25775522060120) 48) 78280455442570) 48) 24945678882372) 48) 118318130466693) 48) 24286458091024) 48) 14014847784012) 48) 23192801055851) 48) 242614451546918) 48) 22205944304648) 48) 178112619679916) 48) 20993215763179) 48) 197899522638874) 48) 20613517152878) 48) 272919697265067) 48) 19262140256631) 48) 131838608399023) 48) 18832731541663) 48) 187200720362750) 48) 17783681847317) 48) 192307429437346) 48) 17370628165579) 48) 116380991649543) 48) 17079343845206) 48) 281363557544629) 48) 16271502347965) 48) 53399574141978) 48) 16075396746878) 48) 23171591521314) 48) 15727584546341) 48) 102761624429716) 48) 15285317930454) 48) 56564950845171)
def certWord105 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 720315038 48) 46595705809496) 48) 110742145781658) 48) 46315992590782) 48) 186320675042202) 48) 45205245798629) 48) 86999533594839) 48) 43261191661392) 48) 198969306213190) 48) 42446125409919) 48) 168543750719330) 48) 40835104122122) 48) 204883445352827) 48) 40602288006322) 48) 195756627065001) 48) 38952119182156) 48) 111429221021609) 48) 37888295772747) 48) 863862136734) 48) 37513574752725) 48) 108551567146926) 48) 36798544224631) 48) 161663126593003) 48) 36158841626808) 48) 31542788168835) 48) 35478028165180) 48) 178426366700210) 48) 35277492920340) 48) 6163811453846) 48) 34692332527338) 48) 265352177557364) 48) 33164539797000) 48) 247747102209574) 48) 32460554116467) 48) 269818925151719) 48) 31615282257004) 48) 119739869750463) 48) 31004208405514) 48) 260284070725293) 48) 30195937975144) 48) 188330479129902) 48) 29992892504873) 48) 210329299047009)
def certWord106 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 957208333 48) 62564213209153) 48) 223944830188542) 48) 61216883226508) 48) 250298739117410) 48) 60794065139445) 48) 174312168164937) 48) 59687651259958) 48) 146901675723739) 48) 59558799816221) 48) 118988680057476) 48) 59193008731578) 48) 52395205599510) 48) 58923732186462) 48) 45965633037254) 48) 58362519565557) 48) 40652752692036) 48) 58047056524488) 48) 264738374680380) 48) 57289148150790) 48) 87326143535481) 48) 56797211276116) 48) 243345106294730) 48) 54864210768239) 48) 5850569128830) 48) 53423983571077) 48) 26891602994417) 48) 52978175979486) 48) 104948328873844) 48) 52239901667122) 48) 46622657014114) 48) 51286794972730) 48) 249903445192698) 48) 50099283635515) 48) 226852334318325) 48) 49227436534842) 48) 263466918189899) 48) 48250621602754) 48) 201829835356432) 48) 47834702097214) 48) 120070829129204) 48) 47385129396984) 48) 256036605943355)
def certWord107 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1313473384 48) 86058004663831) 48) 25723864853832) 48) 85267292245257) 48) 187734309721758) 48) 83792526134184) 48) 88176940920580) 48) 82619913226990) 48) 126964781020392) 48) 82039648307744) 48) 256303409610516) 48) 80645486430552) 48) 97939368615069) 48) 80391063553622) 48) 100176989069041) 48) 76100315596080) 48) 62316839817100) 48) 75967679644895) 48) 145192510870887) 48) 74626535474129) 48) 73762898616696) 48) 73588503364296) 48) 232792641730979) 48) 73342232052336) 48) 199828761611964) 48) 72072477360428) 48) 29928422079936) 48) 70740206960454) 48) 3033305255310) 48) 69305444941365) 48) 240600815730687) 48) 68059648179606) 48) 218735127254620) 48) 67553288469741) 48) 228153975260133) 48) 66408023145479) 48) 9372621685123) 48) 65625078381370) 48) 270210270746304) 48) 64915288308456) 48) 42585587086827) 48) 63788127697337) 48) 220418681026596)
def certWord108 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1693008013 48) 110738431042606) 48) 93047842082428) 48) 109465988653959) 48) 120625826289348) 48) 108898531238612) 48) 207959662149640) 48) 106998346113205) 48) 153886004626261) 48) 106043795071073) 48) 135705392760573) 48) 105183246180248) 48) 127016667645993) 48) 104815564775126) 48) 180257071967903) 48) 102703506414928) 48) 95332644931734) 48) 101086723726249) 48) 23679688470495) 48) 100107357805275) 48) 96079941164424) 48) 98648437119392) 48) 214389089007284) 48) 98108570097913) 48) 47950506411334) 48) 97106091333505) 48) 252442459609375) 48) 95738359862856) 48) 154182181539426) 48) 94663983060462) 48) 203522760551306) 48) 94051888813273) 48) 279788474952713) 48) 93086260417696) 48) 13345862524060) 48) 90478177964616) 48) 75214838508047) 48) 89520043544815) 48) 245939765338941) 48) 88293267754938) 48) 138758836462852) 48) 86804757237446) 48) 6834612354718)
def certWord109 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2034752905 48) 133328461986078) 48) 175610345800130) 48) 131580418029429) 48) 228889390932769) 48) 130581552723645) 48) 128812349022049) 48) 129924333663751) 48) 105787016590117) 48) 128864900379925) 48) 55926726371021) 48) 127696035017722) 48) 45021785995181) 48) 126919798977118) 48) 108896509196269) 48) 124907918553482) 48) 179346853078289) 48) 123537715064665) 48) 116709014161549) 48) 122174290161353) 48) 150613473572714) 48) 121480500047420) 48) 141177421844929) 48) 120562275741046) 48) 70671227236749) 48) 120209103088891) 48) 134262494829656) 48) 118814464240582) 48) 3523680944525) 48) 117976040106746) 48) 220531184895005) 48) 117189174258222) 48) 270606195010421) 48) 116235213367599) 48) 192991816032069) 48) 114077641369517) 48) 37221925745260) 48) 113967441274670) 48) 241486266411979) 48) 113233412974186) 48) 227523312900463) 48) 111551743616338) 48) 87713521717110)
def certWord110 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2522983661 48) 163957496517747) 48) 127790648673369) 48) 162853176251272) 48) 106831185070586) 48) 160295217107359) 48) 169954294442701) 48) 159508643680457) 48) 139996887349167) 48) 158111699603315) 48) 1853521323932) 48) 155437734923437) 48) 70499933909852) 48) 153394982980280) 48) 82865130064685) 48) 152425860074041) 48) 172668585641093) 48) 150909729933539) 48) 117740229274237) 48) 149872375072737) 48) 90913848176876) 48) 147811303851585) 48) 2922827855822) 48) 147309227640211) 48) 247903451220705) 48) 146213759124710) 48) 11894988834222) 48) 144595054003014) 48) 56008574200039) 48) 144162392146664) 48) 126020815362722) 48) 142580604567898) 48) 51357082456010) 48) 141192401485786) 48) 170976187911517) 48) 139055351627339) 48) 8763842093457) 48) 137508866587543) 48) 21884931257630) 48) 135645049420345) 48) 174875935209110) 48) 134055821277665) 48) 99129882063383)
def certWord111 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3102148704 48) 203279122675936) 48) 69431226852593) 48) 201183986235120) 48) 61034552181162) 48) 200409958363907) 48) 89402730434740) 48) 195067688562769) 48) 55747338400215) 48) 193731799265185) 48) 237025005702994) 48) 191435154238954) 48) 267081162807166) 48) 190442359139422) 48) 115597614490315) 48) 187730699725312) 48) 187619907114805) 48) 186647526222232) 48) 55356381717009) 48) 186145571448868) 48) 158714744902622) 48) 183873503930156) 48) 176521656754610) 48) 183196242323017) 48) 199864771202320) 48) 180834611340398) 48) 271710952622480) 48) 178563378094559) 48) 277277214429989) 48) 177486412423299) 48) 192352795752472) 48) 175885777280914) 48) 167948758330146) 48) 173273877421295) 48) 236998927426418) 48) 172195298188263) 48) 185858730734907) 48) 170918709336244) 48) 266221807312596) 48) 166637666408328) 48) 105525592492204) 48) 165789663008418) 48) 247362577909074)
def certWord112 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 65229 48) 35291629024385) 48) 267436336149125) 48) 82325618016280) 48) 260727530056811) 48) 77923222504469) 48) 256841842550763) 48) 150130157956940) 48) 252037767619831) 48) 89854552947772) 48) 249191313301824) 48) 114894136208520) 48) 245945788653333) 48) 176110240442086) 48) 241810607299328) 48) 71132606798415) 48) 239381818365898) 48) 276530778578346) 48) 236130226394591) 48) 280181439830430) 48) 232063076324083) 48) 257224805530652) 48) 229297503064027) 48) 177613245018433) 48) 225650624154777) 48) 73086594469293) 48) 224144433466183) 48) 266312856144148) 48) 223108612737057) 48) 8610440440504) 48) 217941991998835) 48) 119205827376648) 48) 215496391115616) 48) 110242188082767) 48) 213416456470845) 48) 123771312902255) 48) 210711371825012) 48) 191683273530333) 48) 208218890353584) 48) 181482688781533) 48) 205149646666207) 48) 154166663816313)
def certWord113 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 312055787 48) 20313050452530) 48) 78714166412471) 48) 19703108931958) 48) 29309146430017) 48) 18918411604177) 48) 187561501446689) 48) 17583566163952) 48) 127084052923381) 48) 17326698532747) 48) 46587767971067) 48) 16342736965246) 48) 23171591323326) 48) 15326466018742) 48) 129012451166630) 48) 14626922564911) 48) 187754712015073) 48) 14051698871475) 48) 674520006246) 48) 13387341106210) 48) 88498003934992) 48) 13019449461682) 48) 281135868845380) 48) 12377146919631) 48) 10844971773883) 48) 11640044915223) 48) 48692186343256) 48) 8760594597716) 48) 257376037978365) 48) 7613814998704) 48) 134153410659365) 48) 6773658551750) 48) 32805054483223) 48) 6116856497542) 48) 174483131768496) 48) 4429281887203) 48) 110311994192508) 48) 3203312321237) 48) 188970014199818) 48) 2518797845052) 48) 164024826788683) 48) 950419456100) 48) 168315474427375)
def certWord114 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 584604826 48) 37745181073897) 48) 231228718840168) 48) 36804524580938) 48) 192608349891245) 48) 35452053561404) 48) 229033964318319) 48) 34994647277467) 48) 263355036109669) 48) 34347689909988) 48) 250530252919667) 48) 33599197290099) 48) 172915894213101) 48) 33023488892312) 48) 173792052212799) 48) 32443201428851) 48) 269818922617716) 48) 31145918798879) 48) 280019451131137) 48) 30641454390136) 48) 233904377361202) 48) 29756455393956) 48) 192977617893716) 48) 28886525876750) 48) 226980866853549) 48) 28464363674033) 48) 233406130156567) 48) 27927804713258) 48) 15213193655337) 48) 26905822435426) 48) 34566303548165) 48) 26502787831720) 48) 35347972657819) 48) 25467303171816) 48) 240896506662633) 48) 24614089135622) 48) 22317018671744) 48) 23647968826721) 48) 180569370049084) 48) 22103228945426) 48) 28639172614765) 48) 21359152075450) 48) 183030345402442)
def certWord115 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 864685682 48) 56339548353305) 48) 68831996969644) 48) 55614445203867) 48) 68454016099514) 48) 54022528446706) 48) 122085264118251) 48) 51659218890477) 48) 275449919879441) 48) 51248632639046) 48) 78731809971064) 48) 49989297974637) 48) 271966674176913) 48) 49425425575095) 48) 248941349054450) 48) 48012548975520) 48) 180569746990162) 48) 47344874695412) 48) 17927906297128) 48) 46647378782827) 48) 246016437518561) 48) 46529358604644) 48) 25749018558038) 48) 44571166713788) 48) 205875624363279) 48) 43382464325465) 48) 97797062226035) 48) 42904710883043) 48) 118902525937038) 48) 42600428938939) 48) 52704192385987) 48) 42139597350478) 48) 177163748282046) 48) 42028047279661) 48) 72546930733633) 48) 41363574891785) 48) 216295165765940) 48) 40041419514981) 48) 93072548995673) 48) 39760208143279) 48) 227127058759142) 48) 38587461149443) 48) 155942257357419)
def certWord116 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1180596693 48) 76925909615895) 48) 169940108633677) 48) 74465885242281) 48) 272989249562122) 48) 73710226129669) 48) 149766630069177) 48) 73355787190745) 48) 276493916190982) 48) 72175681159556) 48) 31633522240907) 48) 71172577575004) 48) 157493234064250) 48) 70531047636988) 48) 176502742791738) 48) 69161291955751) 48) 140734235446966) 48) 68167738080753) 48) 187953100041299) 48) 67646277172589) 48) 12739898047433) 48) 66897735466143) 48) 66929492345598) 48) 66646981098639) 48) 250822805552478) 48) 65918662097782) 48) 183924378317194) 48) 64371277511307) 48) 29022070266589) 48) 63627920816464) 48) 3574363685998) 48) 62233758939260) 48) 37478821887616) 48) 61078254204722) 48) 232246986732635) 48) 60229478659695) 48) 178611419895796) 48) 59204424054175) 48) 114242732412247) 48) 58380864533710) 48) 203208667720351) 48) 57367323030534) 48) 87326144937067)
def certWord117 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1537807753 48) 100061750188784) 48) 68927156168377) 48) 99245870766578) 48) 39467961707168) 48) 98486514112835) 48) 224280391906658) 48) 97377060083651) 48) 89714728036045) 48) 95019779118656) 48) 53224670412156) 48) 94057759003841) 48) 244161705388213) 48) 92031777723202) 48) 278963814995409) 48) 90796597793420) 48) 178405731320337) 48) 90090082685416) 48) 32235100776975) 48) 89512034128128) 48) 136589905016045) 48) 88344847274040) 48) 188936941538278) 48) 86928971681472) 48) 104167152400170) 48) 85861083729422) 48) 175686945915114) 48) 85635144502737) 48) 19135383894875) 48) 84847891270935) 48) 123601854794484) 48) 83891344133150) 48) 59155859580606) 48) 83499665017784) 48) 166362522332217) 48) 82474149169902) 48) 126964776503061) 48) 81420122081761) 48) 41533568776714) 48) 80352625314040) 48) 151699452239142) 48) 78263762372321) 48) 208826789185560)
def certWord118 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2035470964 48) 133349566413085) 48) 170705505249114) 48) 132328337274865) 48) 12792408877854) 48) 130768001005275) 48) 12294181248865) 48) 128786583745778) 48) 39983811509601) 48) 128211627701156) 48) 91446075997595) 48) 125062564638925) 48) 264382898771243) 48) 123782678343804) 48) 262291242835359) 48) 122510345662313) 48) 105688116174375) 48) 121510191328824) 48) 253946077120863) 48) 120512835185989) 48) 194864487572764) 48) 119009710074861) 48) 119998899327214) 48) 118028927855430) 48) 198811538154342) 48) 116888105937360) 48) 181077594532589) 48) 113924899497794) 48) 101573402052464) 48) 112535142032639) 48) 224637070803141) 48) 110738431042633) 48) 201611737651458) 48) 109374134968978) 48) 210154402668611) 48) 107521285579178) 48) 56523393947652) 48) 105368766013277) 48) 21618148923342) 48) 103383721991624) 48) 52370106209838) 48) 102677467127086) 48) 71864945860225)
def certWord119 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2544177804 48) 166734716180132) 48) 201750015277226) 48) 163862983578675) 48) 30123087899533) 48) 161904223359714) 48) 20562471826388) 48) 161287007801981) 48) 144605414818445) 48) 159529872298124) 48) 180614387803665) 48) 157670406852214) 48) 133528622953677) 48) 156275768003951) 48) 240700914632426) 48) 153853271575484) 48) 127476970805827) 48) 153100880743096) 48) 82865128471239) 48) 152118934604312) 48) 213891687452893) 48) 150775337224440) 48) 39571822457509) 48) 148968971405064) 48) 3652980536724) 48) 147938875835985) 48) 145326764216761) 48) 147238379881810) 48) 17375356274939) 48) 144187378926098) 48) 31943817387906) 48) 140046234255143) 48) 237535292630630) 48) 138685610687997) 48) 78312249869477) 48) 138202947091763) 48) 280588014194989) 48) 136370062785480) 48) 117379229422726) 48) 135425010268905) 48) 137505437930671) 48) 134833372625451) 48) 268514802283031)
def certWord120 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3369637149 48) 220412415756243) 48) 266338566392438) 48) 217437662397674) 48) 249485059973070) 48) 215059589415172) 48) 57538574758171) 48) 209044184612368) 48) 134925237148196) 48) 204816110762565) 48) 243540623634265) 48) 201627414148798) 48) 129968768344192) 48) 198185302406142) 48) 197683169276734) 48) 195912728097296) 48) 222374892992235) 48) 193846668930963) 48) 96248841783977) 48) 190952521968675) 48) 193435317836686) 48) 187159131564584) 48) 114098654876098) 48) 186428559894924) 48) 100457823834052) 48) 185639672457229) 48) 83552794161906) 48) 182939046356537) 48) 92731113225922) 48) 180507086791181) 48) 203747374398510) 48) 177303757234299) 48) 63297617201283) 48) 175451061984828) 48) 76307038335264) 48) 172817953561596) 48) 237024669118753) 48) 170338925910582) 48) 111658844027849) 48) 168689738750168) 48) 63125690397943) 48) 167437586372635) 48) 139168079186107)
def certWord121 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 65306 48) 257771028807058) 48) 272660878455429) 48) 82325694182550) 48) 265313544499261) 48) 162212024822872) 48) 257801858902585) 48) 269783688912207) 48) 251111071081564) 48) 138422017950427) 48) 248843489632464) 48) 81900204915923) 48) 246819763183525) 48) 216886712328370) 48) 244957732462039) 48) 274645349566674) 48) 239391673473231) 48) 131008706254371) 48) 234158241141519) 48) 111303277528987) 48) 227373804932770) 48) 133370784078679) 48) 224358283201532) 48) 205513300551160) 48) 222508123277784) 48) 152354450009743)
def certWord122 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 47828 48) 239851219613236) 48) 170650612366570) 48) 18885759457636) 48) 51599645154931) 48) 98874903024828) 48) 25467303171425) 48) 180569304660545)
def certWord123 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 72279425152 48) 37653) 48) 1379960356864) 48) 285212675) 48) 22274774139141) 48) 17935783428096) 48) 70368744706305) 48) 128) 48) 2165313536) 48) 524288) 48) 13542031884288) 48) 2147483648) 48) 412316860416) 48) 61572651155471) 48) 128) 48) 24576) 48) 138580117829) 48) 84125527722003) 48) 22814866276352) 48) 343597383680) 48) 92358976733199) 48) 384) 48) 8192) 48) 524288) 48) 268435456) 48) 17179869184) 48) 137456599816) 48) 8796093022222)
def certWord124 : Nat := (Nat.lor (Nat.shiftLeft 1236950581248 48) 74766790688789)
def certWord125 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1344 48) 69632) 48) 280313987072) 48) 13542185193810) 48) 53602265595904) 48) 68719493444) 48) 21990232555536) 48) 128) 48) 37893) 48) 5709287391232) 48) 33554432) 48) 8589934861) 48) 17729625014596) 48) 21991310758404) 48) 33833024) 48) 86016) 48) 280315035648) 48) 33557588) 48) 4951023550661) 48) 17798344474624) 48) 8796093022216) 48) 1088) 48) 4096) 48) 524288) 48) 16780435) 48) 35734127902729) 48) 17935800287560) 48) 13194140602629)
def certWord126 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 51659328 48) 28673) 48) 1306879066112) 48) 33554432) 48) 1073741824) 48) 0) 48) 83562883710978) 48) 72279425152) 48) 77824) 48) 211596607488) 48) 13267288200211) 48) 35734127902720) 48) 618475290624) 48) 4398047039750) 48) 67387584) 48) 24577) 48) 1311173771329) 48) 88038256410624) 48) 2147483845) 48) 18210661335040) 48) 70368744177670) 48) 896) 48) 28672) 48) 211594248256) 48) 79242217017683) 48) 36009005809857) 48) 18141941871108) 48) 1129366018)
def certWord127 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 128 48) 4379923237) 48) 23304693874688) 48) 13542031884292) 48) 22270479171713) 48) 18004502904832) 48) 35184372088853) 48) 70129057856) 48) 86016) 48) 276019281920) 48) 83886080) 48) 16106127360) 48) 1168231104512) 48) 21990233624837) 48) 64) 48) 3306172416) 48) 1310720) 48) 0) 48) 6442451209) 48) 17660905521152) 48) 35184373158144) 48) 33833024) 48) 20480) 48) 1572931) 48) 83915071029248) 48) 2147483777) 48) 17592186044416) 48) 8796093022215)
def certWord128 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 768 48) 5775676153856) 48) 9732358144) 48) 117440516) 48) 22266184204288) 48) 549755830340) 48) 2) 48) 52950237376) 48) 2165334016) 48) 4194304) 48) 33554432) 48) 18253611008) 48) 1099511627776) 48) 79164837199874) 48) 68436040) 48) 233459594301440) 48) 524353) 48) 79517091627011) 48) 4683661836549) 48) 18004502904832) 48) 8796093022214) 48) 33833344) 48) 4096) 48) 207301378048) 48) 33554432) 48) 5368709120) 48) 206158430208) 48) 17592186044423)
def certWord129 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 55324868395008 48) 4625883209728) 48) 1310720) 48) 13542186176851) 48) 36009005809664) 48) 0) 48) 1095766529) 48) 33833344) 48) 24576) 48) 3670016) 48) 17940182356307) 48) 36010079551488) 48) 137438953472) 48) 26388279066630) 48) 72279425152) 48) 86016) 48) 211595034624) 48) 13267288195072) 48) 2147483648) 48) 206167679048) 48) 2) 48) 72279425152) 48) 4312805941) 48) 23240269627392) 48) 83886084) 48) 22271763961032) 48) 52776558133248) 48) 74766790688787)
def certWord130 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 8192 48) 1048576) 48) 17940162281472) 48) 17180144908) 48) 35321828688648) 48) 8796093022214) 48) 384) 48) 2165313536) 48) 524352) 48) 88313167872000) 48) 2147483648) 48) 137457119752) 48) 1095766531) 48) 0) 48) 2219510333440) 48) 4456448) 48) 285212672) 48) 1073742021) 48) 17798344491332) 48) 21990232555520)
def certWord131 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 512 48) 4379906049) 48) 76154199867392) 48) 8869141020672) 48) 3221225737) 48) 17660926571016) 48) 1085699) 48) 33832960) 48) 4096) 48) 4456448) 48) 301989892) 48) 22266184488136) 48) 35390530519364) 48) 5) 48) 320) 48) 8192) 48) 1310720) 48) 33554432) 48) 8589934853) 48) 17660905537604) 48) 4399393702401) 48) 1024) 48) 4486112219136) 48) 524288) 48) 17940162281472) 48) 5368709120) 48) 343618691848) 48) 4398046511113)
def certWord132 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 448 48) 16384) 48) 5505024) 48) 318767108) 48) 22270479171598) 48) 17660905534020) 48) 8796093022214) 48) 320) 48) 8192) 48) 221216719765504) 48) 234881028) 48) 4676145643717) 48) 18210661335040) 48) 13194139533315) 48) 51658944) 48) 4762181304320) 48) 4980736) 48) 18214973079555) 48) 39857296507145) 48) 17660905521152) 48) 26389626536450) 48) 256) 48) 36865) 48) 5773644267520) 48) 966384418816) 48) 79439715107085) 48) 17729624998788) 48) 8796093059330)
def certWord133 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 68436224 48) 16384) 48) 524288) 48) 50331648) 48) 5368709120) 48) 687194767360) 48) 21990233608451) 48) 576) 48) 4096) 48) 211595034624) 48) 67108864) 48) 2147483648) 48) 481036337152) 48) 4398047580417) 48) 64) 48) 303046656) 48) 0) 48) 16777220) 48) 39858370248704) 48) 206158447428) 48) 8796093022213) 48) 540672) 48) 4514127872) 48) 4194304) 48) 83886083) 48) 22268331687936) 48) 274877906944) 48) 83562883748098)
def certWord134 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4735040 48) 2366640128) 48) 6510084131) 48) 79998077632512) 48) 12884901888) 48) 68719476736) 48) 21990232555526) 48) 256) 48) 4312805376) 48) 2621440) 48) 14366699159552) 48) 6442450944) 48) 343597396036) 48) 35184372088836) 48) 2375808) 48) 3306160128) 48) 207299805184) 48) 966384418816) 48) 8589934610) 48) 17729625014596) 48) 4398047301889) 48) 2637824) 48) 4514123777) 48) 23240202518528) 48) 33554433) 48) 4677219385344) 48) 137438966788) 48) 8796093030658)
def certWord135 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 960 48) 3373281280) 48) 786432) 48) 134217732) 48) 22271552913669) 48) 17660905521152) 48) 4398046519554) 48) 3686464) 48) 20480) 48) 19394986048) 48) 88313167872004) 48) 22266184204288) 48) 68719481604) 48) 8796093845760) 48) 64) 48) 4096) 48) 1310720) 48) 117440515) 48) 39857296506880) 48) 412316860416) 48) 35184372617474) 48) 4734976) 48) 20481) 48) 71683138388048) 48) 88794187431940) 48) 22269405430017) 48) 17798344491076) 48) 8796093022217)
def certWord136 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 320 48) 12288) 48) 1048576) 48) 33554436) 48) 22266184537228) 48) 35184390255112) 48) 4398046511106) 48) 768) 48) 4379901952) 48) 280314773504) 48) 416628604928) 48) 5368709120) 48) 412316876868) 48) 4398047301890) 48) 960) 48) 16384) 48) 19394985984) 48) 134217728) 48) 19327352832) 48) 0) 48) 807177) 48) 320) 48) 4447023104) 48) 211595034624) 48) 141767475200) 48) 44257490501632) 48) 274877906944) 48) 57174604685570)
def certWord137 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 51659328 48) 49152) 48) 1310720) 48) 134217728) 48) 44255343017984) 48) 206158434372) 48) 17592187113729) 48) 2376000) 48) 24576) 48) 524288) 48) 18214989856768) 48) 5368709381) 48) 17729624997888) 48) 30786325577728) 48) 51658944) 48) 20481) 48) 71683138650112) 48) 17940162281472) 48) 2147483648) 48) 137438966340) 48) 13194140635394) 48) 51658944) 48) 4312805376) 48) 15100280832) 48) 33554436) 48) 4675071901696) 48) 274877908100) 48) 1069317)
def certWord138 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 640 48) 40960) 48) 19394461696) 48) 18214973079552) 48) 2147483648) 48) 343597384516) 48) 8796093812996) 48) 68436288) 48) 36864) 48) 5505024) 48) 167772160) 48) 12884901888) 48) 824633737284) 48) 17592186044422) 48) 3686528) 48) 2165317632) 48) 0) 48) 141750697988) 48) 57450556499144) 48) 35390530531908) 48) 8796093047042) 48) 64) 48) 4312805376) 48) 262144) 48) 100663300) 48) 22266184204288) 48) 9028) 48) 4398046511108)
def certWord139 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 128 48) 0) 48) 211594772480) 48) 18489884540928) 48) 6442450944) 48) 687194767748) 48) 13195235299841) 48) 576) 48) 2165313536) 48) 138580066304) 48) 50331648) 48) 7516193033) 48) 17592186044416) 48) 8796093022214) 48) 448) 48) 4417392742400) 48) 215890001920) 48) 234881028) 48) 4676145972424) 48) 35184372088832) 48) 21990233362692) 48) 320) 48) 3456511246336) 48) 3670016) 48) 13816943345664) 48) 18253611026) 48) 17660905521152) 48) 26389441708544)
def certWord140 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 128 48) 20480) 48) 0) 48) 966401196032) 48) 5368709120) 48) 549755813888) 48) 8796093022214) 48) 67387584) 48) 24576) 48) 10804527104) 48) 17665200488448) 48) 13958643712) 48) 412316860740) 48) 17592186900738) 48) 576) 48) 20481) 48) 23304626765824) 48) 83886083) 48) 39859443990528) 48) 206158446660) 48) 17593348686339) 48) 384) 48) 20480) 48) 0) 48) 966417973249) 48) 39859443990789) 48) 17660905521152) 48) 4399209153027)
def certWord141 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 3686464 48) 3456511250432) 48) 1310720) 48) 17665250820099) 48) 4673998160137) 48) 17660905537860) 48) 21990233657602) 48) 69484672) 48) 86016) 48) 786432) 48) 18214956302336) 48) 5368709120) 48) 68719476736) 48) 26388279066637) 48) 540864) 48) 69632) 48) 4980736) 48) 285212672) 48) 0) 48) 618475290624) 48) 6) 48) 86220243136) 48) 0) 48) 1310720) 48) 67108864) 48) 2147483909) 48) 17660905521152) 48) 26388279066633)
def certWord142 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 256 48) 20480) 48) 1048657) 48) 79998111186944) 48) 6442451137) 48) 17729624997888) 48) 61572651155458) 48) 512) 48) 2165309441) 48) 76016761176064) 48) 9693757964288) 48) 1073742089) 48) 17660905521152) 48) 21990232613120) 48) 320) 48) 12289) 48) 1379893248000) 48) 100663300) 48) 39857296506880) 48) 274877906944) 48) 5) 48) 2376000) 48) 16384) 48) 262144) 48) 1241279102980) 48) 22271553189061) 48) 35184372088832) 48) 39582419128580)
def certWord143 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 34881792 48) 57344) 48) 2214592512) 48) 8869141020672) 48) 18253611276) 48) 17729624999044) 48) 8796094075137) 48) 74393354304) 48) 32768) 48) 1835008) 48) 17940095172608) 48) 2147483913) 48) 17729624997888) 48) 21990824526337) 48) 87311810688) 48) 3306172416) 48) 1572864) 48) 33554432) 48) 5368709385) 48) 17592207352584) 48) 2) 48) 4735168) 48) 4379922432) 48) 276019281920) 48) 33554432) 48) 5368709313) 48) 17729624997888) 48) 13194139533315)
def certWord144 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 68436032 48) 16384) 48) 221216719765504) 48) 67108864) 48) 61847529062593) 48) 18279380812932) 48) 8796093022222) 48) 36978752) 48) 2232418304) 48) 262144) 48) 1241262325760) 48) 12885234888) 48) 35253091565568) 48) 70368744177666) 48) 192) 48) 168828928) 48) 1835008) 48) 1241279102980) 48) 39858370248704) 48) 412316877380) 48) 4398046552320) 48) 70271104) 48) 0) 48) 288904183808) 48) 33554433) 48) 4683661836288) 48) 274895553288) 48) 8796093022210)
def certWord145 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 512 48) 20480) 48) 262144) 48) 13267288195072) 48) 19327352832) 48) 0) 48) 26388280119553) 48) 128) 48) 20480) 48) 138580066304) 48) 0) 48) 2147483648) 48) 274877906944) 48) 21990233624838) 48) 51658752) 48) 235929600) 48) 1572864) 48) 83886080) 48) 8589934793) 48) 17592186045316) 48) 8796094091525) 48) 68436032) 48) 12288) 48) 524288) 48) 150994944) 48) 6442450958) 48) 17729624998788) 48) 4398046535938)
def certWord146 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 19153024 48) 3373277184) 48) 212344391335936) 48) 18214989856768) 48) 5368709120) 48) 549755826756) 48) 5) 48) 576) 48) 20480) 48) 1048576) 48) 16782355) 48) 35737349128192) 48) 206158430208) 48) 21991579746819) 48) 3686400) 48) 12288) 48) 207299805184) 48) 13542098993155) 48) 35459249995973) 48) 17798344491076) 48) 13194140602629) 48) 384) 48) 235929600) 48) 138580066304) 48) 67108868) 48) 57451630034944) 48) 137438953472) 48) 21990232555530)
def certWord147 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4312805376 48) 0) 48) 83886080) 48) 0) 48) 343597396036) 48) 43980465934594) 48) 67387584) 48) 0) 48) 1572864) 48) 16777220) 48) 22266184204288) 48) 343610564680) 48) 9) 48) 128) 48) 16384) 48) 2097152) 48) 150994944) 48) 5368853644) 48) 35253091565568) 48) 26388280135941) 48) 67387584) 48) 3239084032) 48) 1048576) 48) 1241279102976) 48) 26664230715392) 48) 137438953472) 48) 48378512724224)
def certWord148 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 50610304 48) 5587955884032) 48) 288903921745) 48) 79998077632515) 48) 4675071901961) 48) 17592207094280) 48) 843874816) 48) 17056384) 48) 0) 48) 524288) 48) 150994944) 48) 2147483845) 48) 18210661351748) 48) 13194140635393) 48) 52707456) 48) 4096) 48) 1310720) 48) 285212672) 48) 22548578513) 48) 17729624997888) 48) 4) 48) 74409082880) 48) 4096) 48) 0) 48) 13542082215936) 48) 22548578565) 48) 17798344487236) 48) 13195268899330)
def certWord149 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1344 48) 20480) 48) 280315035648) 48) 14366699159552) 48) 22548578304) 48) 343597383680) 48) 21990232555538) 48) 320) 48) 5655668727808) 48) 1572864) 48) 141767475200) 48) 8589934592) 48) 274877906944) 48) 74766790697217) 48) 512) 48) 5655668727808) 48) 2097152) 48) 13542031884288) 48) 7516192768) 48) 1030792160068) 48) 4398046511107) 48) 128) 48) 4762181304320) 48) 287830441984) 48) 352325716) 48) 4948876066816) 48) 549755830596) 48) 4398046511104)
def certWord150 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1835008 48) 167772162) 48) 57449482551314) 48) 17592203690760) 48) 8796093845761) 48) 4735040) 48) 86016) 48) 524288) 48) 335544323) 48) 22265110799568) 48) 35321811042304) 48) 13194139533329) 48) 68436032) 48) 16384) 48) 1835008) 48) 67108864) 48) 8589934592) 48) 481036354372) 48) 8796093022213) 48) 54007988224) 48) 86016) 48) 524288) 48) 67108867) 48) 4681514352640) 48) 343597383680) 48) 8796093022213)
def certWord151 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 192 48) 4379901952) 48) 6509821952) 48) 50331650) 48) 53052509782016) 48) 137438970180) 48) 13194139799810) 48) 128) 48) 28672) 48) 524288) 48) 150994945) 48) 4673998159872) 48) 412316861060) 48) 13194139533312) 48) 512) 48) 32768) 48) 2359296) 48) 16777216) 48) 4294967296) 48) 274877906944) 48) 21990232555525) 48) 52445184) 48) 1091571712) 48) 10804527104) 48) 966401196032) 48) 2147483648) 48) 755914244096) 48) 4398047088896)
def certWord152 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 128 48) 3373277184) 48) 1048576) 48) 67108864) 48) 22265110462464) 48) 343597383680) 48) 4398046511105) 48) 69484608) 48) 12288) 48) 1048576) 48) 0) 48) 5368709185) 48) 17729624997888) 48) 17592187097346) 48) 1152) 48) 12288) 48) 138580590592) 48) 33554432) 48) 5368709120) 48) 481036337152) 48) 13194139533312) 48) 320) 48) 0) 48) 284608954368) 48) 416645382146) 48) 57450556293130) 48) 17592186052932) 48) 13194139533321)
def certWord153 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 67387584 48) 3306172416) 48) 211594772480) 48) 13267153977344) 48) 5368709120) 48) 137438954116) 48) 1052929) 48) 0) 48) 20480) 48) 142875033600) 48) 100663300) 48) 4676145643520) 48) 549755826500) 48) 13194140635395) 48) 0) 48) 8192) 48) 284608692224) 48) 50331648) 48) 6442450944) 48) 343597383680) 48) 13194139533316) 48) 64) 48) 57344) 48) 2621440) 48) 150994944) 48) 3221225472) 48) 412316860416) 48) 17592186044426)
def certWord154 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4096 48) 207299543040) 48) 134217732) 48) 39857296506880) 48) 16708) 48) 4398046511110) 48) 17055872) 48) 24576) 48) 786432) 48) 33554432) 48) 2147483648) 48) 68719489348) 48) 4398046511104) 48) 3686528) 48) 3306160128) 48) 524288) 48) 67108868) 48) 4673998159872) 48) 824633720832) 48) 52776558133254) 48) 256) 48) 4096) 48) 3145728) 48) 0) 48) 4294967296) 48) 132) 48) 5)
def certWord155 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 64 48) 0) 48) 15099756544) 48) 33554432) 48) 1073742025) 48) 17798344474624) 48) 266498) 48) 192) 48) 4497350656) 48) 2359296) 48) 1241295880192) 48) 3221225472) 48) 137438953472) 48) 21990232555521) 48) 0) 48) 168824832) 48) 524288) 48) 2) 48) 53052509782016) 48) 481036337152) 48) 17592186102017) 48) 68436032) 48) 3306172416) 48) 786432) 48) 17665200488448) 48) 7516192782) 48) 17592186057028) 48) 4398046552320)
def certWord156 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 33832960 48) 24576) 48) 524288) 48) 352321536) 48) 2147483666) 48) 17729624998532) 48) 8796093022211) 48) 70271104) 48) 4514123776) 48) 0) 48) 33554432) 48) 61847529062400) 48) 1443109012356) 48) 4398046511107) 48) 128) 48) 3373268992) 48) 1572864) 48) 966367641600) 48) 79439715107085) 48) 17660905521152) 48) 17592186589441) 48) 384) 48) 4312793088) 48) 2621440) 48) 0) 48) 44256416760073) 48) 17592186044416) 48) 8796093096194)
def certWord157 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 4735104 48) 0) 48) 262144) 48) 17940111949824) 48) 4294967557) 48) 17592186045572) 48) 8796093022213) 48) 33832960) 48) 4096) 48) 5505024) 48) 33554432) 48) 3221225472) 48) 68719477380) 48) 8796093079808) 48) 68436160) 48) 20480) 48) 276018757632) 48) 33554432) 48) 1073741824) 48) 68719489092) 48) 8796093022210) 48) 1589248) 48) 24576) 48) 1310720) 48) 50331650) 48) 4673998159890) 48) 17729624997888) 48) 5)
def certWord158 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 128 48) 168833024) 48) 1310720) 48) 16777216) 48) 2147483648) 48) 481036337152) 48) 26388279066624) 48) 1589312) 48) 8192) 48) 0) 48) 335544320) 48) 0) 48) 68719493444) 48) 4398046511104) 48) 68436096) 48) 0) 48) 1048576) 48) 17665250820099) 48) 35459249995841) 48) 17592186044804) 48) 4398046511106) 48) 67387520) 48) 0) 48) 524288) 48) 16777219) 48) 4675071901761) 48) 17660905521152) 48) 26388279857409)
def certWord159 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 2637824 48) 16384) 48) 142874771456) 48) 67108864) 48) 4294967296) 48) 8260) 48) 790786) 48) 128) 48) 4096) 48) 262144) 48) 33554432) 48) 8589934725) 48) 17660905521152) 48) 39582418599937) 48) 3686400) 48) 303046656) 48) 215889477632) 48) 201326592) 48) 79440788848640) 48) 137438970692) 48) 41216) 48) 768) 48) 20480) 48) 10805051392) 48) 16777216) 48) 61850750287872) 48) 549755813888) 48) 8796093022222)
def certWord160 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 64 48) 1225793536) 48) 142874771456) 48) 0) 48) 2147483648) 48) 137438966084) 48) 8796093022210) 48) 36716608) 48) 49152) 48) 3145728) 48) 17665200488448) 48) 8589934592) 48) 137438953604) 48) 5) 48) 50610304) 48) 168833024) 48) 78450786304) 48) 13748240646144) 48) 4294967296) 48) 206158430208) 48) 21990233362690) 48) 540672) 48) 4096) 48) 10804789248) 48) 0) 48) 5368709120) 48) 343597392196) 48) 4398046511104)
def certWord161 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1344 48) 45056) 48) 215889215488) 48) 167772160) 48) 3221225472) 48) 274877906944) 48) 4398046535936) 48) 640) 48) 3373281280) 48) 19395248128) 48) 33554435) 48) 39860517732352) 48) 618475290624) 48) 21990232629507) 48) 256) 48) 3356491776) 48) 142874771456) 48) 13816943345664) 48) 3221225472) 48) 17220) 48) 8796093829376) 48) 0) 48) 32768) 48) 1310720) 48) 691489734656) 48) 1073741964) 48) 17660905521152) 48) 24834)
def certWord162 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 256 48) 4379906048) 48) 786432) 48) 16777220) 48) 39857296506880) 48) 274877919748) 48) 1097986) 48) 192) 48) 4096) 48) 262144) 48) 134217728) 48) 1073742017) 48) 17660905521152) 48) 8796093022226) 48) 576) 48) 49152) 48) 2097152) 48) 3) 48) 4673998159872) 48) 0) 48) 52776558133248) 48) 33832960) 48) 168824832) 48) 0) 48) 50331648) 48) 10737418240) 48) 412316861316) 48) 0)
def certWord163 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 192 48) 8192) 48) 3145728) 48) 16777216) 48) 9070970929152) 48) 137438953472) 48) 52776558133253) 48) 69484544) 48) 40960) 48) 2621440) 48) 9143985373188) 48) 39859443990528) 48) 618475290624) 48) 3) 48) 64) 48) 0) 48) 0) 48) 134217728) 48) 5368709185) 48) 17592186044416) 48) 7) 48) 0) 48) 20480) 48) 0) 48) 201326596) 48) 39859443990528) 48) 0) 48) 4398046511108)
def certWord164 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 640 48) 32768) 48) 284608954368) 48) 691506511876) 48) 4676145643520) 48) 1443109012356) 48) 13194139533315) 48) 0) 48) 8192) 48) 276018757632) 48) 83886080) 48) 1073741830) 48) 17798344491844) 48) 4398046511105) 48) 70533248) 48) 34607104) 48) 10804527104) 48) 9693757964288) 48) 65) 48) 17660905521152) 48) 0) 48) 0) 48) 2165317632) 48) 1310720) 48) 3) 48) 22268331687950) 48) 17798344475268) 48) 13194139533324)
def certWord165 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 192 48) 20480) 48) 5505024) 48) 8869107466240) 48) 4294967493) 48) 17660905521152) 48) 13194139533314) 48) 3686528) 48) 4096) 48) 262144) 48) 67108864) 48) 2147483648) 48) 8260) 48) 8796093063425) 48) 64) 48) 8192) 48) 262144) 48) 33554432) 48) 7516192897) 48) 17592186044416) 48) 4398046511104) 48) 256) 48) 28672) 48) 262144) 48) 691540066304) 48) 6442450944) 48) 137438953472) 48) 4)
def certWord166 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 1589312 48) 0) 48) 1048576) 48) 966417973252) 48) 4676145643720) 48) 17592186056772) 48) 13194139533318) 48) 192) 48) 20480) 48) 284608954368) 48) 9143985373184) 48) 129) 48) 17660905521152) 48) 17592186044423) 48) 192) 48) 12288) 48) 284608692224) 48) 67108865) 48) 4673998159890) 48) 17592186061380) 48) 13194139533312) 48) 34881536) 48) 8192) 48) 2097152) 48) 0) 48) 61849676546048) 48) 0) 48) 39582419669249)
def certWord167 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 64 48) 20480) 48) 15100018688) 48) 141767475200) 48) 2147483650) 48) 17798344474624) 48) 4398047330561) 48) 0) 48) 0) 48) 1048576) 48) 67108864) 48) 5368709389) 48) 17729624999044) 48) 266496) 48) 512) 48) 1091567616) 48) 262144) 48) 16777216) 48) 4294967296) 48) 343597396292) 48) 4398046511105) 48) 1589440) 48) 16384) 48) 524288) 48) 13816909791232) 48) 79439715106816) 48) 137438953472) 48) 2)
def certWord168 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 280313987072 48) 13816909791232) 48) 0) 48) 137438954372) 48) 8796093550850)
def certWord169 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 13194139533313 48) 0) 48) 0) 48) 524288) 48) 33554432) 48) 0) 48) 137438953472) 48) 4398046511105)

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
  let x := (((w % PEqualNP.Outside.L_meta_28352_aux.certWord0) ^^^ seed) * PEqualNP.Outside.L_meta_28352_aux.certWord1) &&& PEqualNP.Outside.L_meta_28352_aux.certWord2
  let y := ((x ^^^ (x >>> 61)) * PEqualNP.Outside.L_meta_28352_aux.certWord3) &&& PEqualNP.Outside.L_meta_28352_aux.certWord2
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
  [PEqualNP.Outside.L_meta_28352_aux.certWord4,
   PEqualNP.Outside.L_meta_28352_aux.certWord5,
   PEqualNP.Outside.L_meta_28352_aux.certWord6,
   PEqualNP.Outside.L_meta_28352_aux.certWord7,
   PEqualNP.Outside.L_meta_28352_aux.certWord8,
   PEqualNP.Outside.L_meta_28352_aux.certWord9,
   PEqualNP.Outside.L_meta_28352_aux.certWord10,
   PEqualNP.Outside.L_meta_28352_aux.certWord11]

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

def dom_0 : Nat := 0x101010101010101
def goal_0 : Nat := 0x101010001000000
def roots_0 : List Nat := [0x100010001000100, 0x101000001010000, 0x101010100000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(8, 24), (8, 40), (16, 24), (16, 48), (32, 40), (32, 48)]
def r1sG : List Nat := [8, 8, 16, 16, 32, 32]
def r2sG : List Nat := [24, 40, 24, 48, 40, 48]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x2bca81f0
  | 3, 0 => 0x2bca81f0
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord12
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

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord15, 24), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord14, 8), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord15, 24)], [(PEqualNP.Outside.L_meta_28352_aux.certWord16, 2)], [(PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24)]]
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
def goal_1 : Nat := 0x303030203020000
def roots_1 : List Nat := [0x202020202020202, 0x300030003000300, 0x303000003030000, 0x303030300000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x202020202020202, 16, 17)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0x1111111111111111
def goal_2 : Nat := 0x1111111011001000
def roots_2 : List Nat := [0x1010101010101010, 0x1100110011001100, 0x1111000011110000, 0x1111111100000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0x3000300030003
def goal_3 : Nat := 0x3000200020000
def roots_3 : List Nat := [0x2000200020002, 0x3000000030000, 0x3000300000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 4 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord19, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_4 : Nat := 0x33003300330033
def goal_4 : Nat := 0x33003200220000
def roots_4 : List Nat := [0x22002200220022, 0x30003000300030, 0x33000000330000, 0x33003300000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30003000300030, 32, 36)] (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0x333300003333
def goal_5 : Nat := 0x333200003000
def roots_5 : List Nat := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0x33333333
def goal_6 : Nat := 0x33223000
def roots_6 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

namespace S_6
def pairsG : List (Nat × Nat) := [(1, 17), (4, 12), (5, 13), (5, 21), (8, 12), (8, 24), (9, 13), (9, 25), (16, 17), (16, 24), (20, 21), (20, 28)]
def r1sG : List Nat := [1, 4, 5, 5, 8, 8, 9, 9, 16, 16, 20, 20]
def r2sG : List Nat := [17, 12, 13, 21, 12, 24, 13, 25, 17, 24, 21, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_6.map (· &&& dom_6)
def goalM : Nat := goal_6 &&& dom_6
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x13ac53d7
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord20
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf000f0c0e0cd
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfa9af6c5e5cd
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_6 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_6 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_28352_aux.certWord21, 30)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord21, 30), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)]]
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
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_6 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_6 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_6 roots_6 goal_6 4 := by
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

theorem low_6 : Lower dom_6 roots_6 goal_6 4 := S_6.noCircuit

def dom_7 : Nat := 0x3333333333333333
def goal_7 : Nat := 0x3333333233223000
def roots_7 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

namespace S_7
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (4, 12), (4, 36), (5, 13), (5, 21), (5, 37), (8, 12), (8, 24), (8, 40), (9, 13), (9, 25), (9, 41), (16, 17), (16, 24), (16, 48), (20, 21), (20, 28), (20, 52), (32, 33), (32, 36), (32, 40), (32, 48)]
def r1sG : List Nat := [1, 1, 4, 4, 5, 5, 5, 8, 8, 8, 9, 9, 9, 16, 16, 16, 20, 20, 20, 32, 32, 32, 32]
def r2sG : List Nat := [17, 33, 12, 36, 13, 21, 37, 12, 24, 40, 13, 25, 41, 17, 24, 48, 21, 28, 52, 33, 36, 40, 48]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_7.map (· &&& dom_7)
def goalM : Nat := goal_7 &&& dom_7
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x9c1be658
  | 6, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord22
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | 6, 0, 0 => 0x58d15
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord23
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord24
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 23 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 23 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 6 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
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
  | 4 => 1
  | 5 => 19
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x995298d1
  | 5, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord25
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord26
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 3 => checkCutEntry dom_5 roots_5 5 s ws hint
  | 4 => checkCutEntry dom_6 roots_6 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_7 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_7 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_7 == dom_7) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_7 goalM u ys) : RunD dom_7 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_7 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
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
  scr dom_7 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_7 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_7 roots_7 goal_7 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_7 goal_7 := by
    have h0 : isConstB dom_7 goal_7 = false := by decide +kernel
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

end S_7

theorem low_7 : Lower dom_7 roots_7 goal_7 7 := S_7.noCircuit

def dom_8 : Nat := 0x404040404040404
def goal_8 : Nat := 0x404040004000000
def roots_8 : List Nat := [0x400040004000400, 0x404000004040000, 0x404040400000000]

namespace S_8
def pairsG : List (Nat × Nat) := [(10, 26), (10, 42), (18, 26), (18, 50), (34, 42), (34, 50)]
def r1sG : List Nat := [10, 10, 18, 18, 34, 34]
def r2sG : List Nat := [26, 42, 26, 50, 42, 50]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_8.map (· &&& dom_8)
def goalM : Nat := goal_8 &&& dom_8
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x8ca6dfa5
  | 3, 0 => 0x8ca6dfa5
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord27
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord15, 24), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord14, 8), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord15, 24)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_8 == dom_8) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_8 goalM u ys) : RunD dom_8 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_8 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_8 roots_8 goal_8 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_8 goal_8 := by
    have h0 : isConstB dom_8 goal_8 = false := by decide +kernel
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

end S_8

theorem low_8 : Lower dom_8 roots_8 goal_8 4 := S_8.noCircuit

def dom_9 : Nat := 0xc0c0c0c0c0c0c0c
def goal_9 : Nat := 0xc0c0c080c080808
def roots_9 : List Nat := [0x808080808080808, 0xc000c000c000c00, 0xc0c00000c0c0000, 0xc0c0c0c00000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x808080808080808, 2, 3)] (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0xf000f000f000f
def goal_10 : Nat := 0xf000a000a0008
def roots_10 : List Nat := [0xa000a000a000a, 0xc000c000c000c, 0xf0000000f0000, 0xf000f00000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord28, 12), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_11 : Nat := 0xf0f00000f0f
def goal_11 : Nat := 0xf0a00000808
def roots_11 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 4 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord29, 7), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_12 : Nat := 0xf0f0f0f
def goal_12 : Nat := 0xf0a0808
def roots_12 : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]

theorem low_12 : Lower dom_12 roots_12 goal_12 4 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xf0f0f0f0f0f0f0f
def goal_13 : Nat := 0xf0f0f0a0f0a0808
def roots_13 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

namespace S_13
def pairsG : List (Nat × Nat) := [(1, 3), (1, 17), (1, 33), (2, 3), (8, 24), (8, 40), (9, 11), (9, 25), (9, 41), (10, 11), (10, 26), (10, 42), (16, 17), (16, 24), (16, 48), (18, 19), (18, 26), (18, 50), (32, 33), (32, 40), (32, 48), (34, 35), (34, 42), (34, 50)]
def r1sG : List Nat := [1, 1, 1, 2, 8, 8, 9, 9, 9, 10, 10, 10, 16, 16, 16, 18, 18, 18, 32, 32, 32, 34, 34, 34]
def r2sG : List Nat := [3, 17, 33, 3, 24, 40, 11, 25, 41, 11, 26, 42, 17, 24, 48, 19, 26, 50, 33, 40, 48, 35, 42, 50]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_13.map (· &&& dom_13)
def goalM : Nat := goal_13 &&& dom_13
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xa052ac9e37f8ccf4
  | 6, 0 => 0xc3827481
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord30
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xd6345856885
  | 6, 0, 0 => 0x58d15
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord31
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord32
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 24 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 24 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 7 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 7 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 7 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 7 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
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
  | 4 => 4
  | 5 => 24
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord33
  | 5, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord34
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x100000800003
  | 5, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord35
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_9 roots_9 5 s ws hint
  | 2 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 3 => checkCutEntry dom_11 roots_11 4 s ws hint
  | 4 => checkCutEntry dom_12 roots_12 4 s ws hint
  | 5 => checkCutEntry dom_8 roots_8 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_13 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_13 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_28352_aux.certWord13, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_13 == dom_13) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_13 goalM u ys) : RunD dom_13 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_13 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := z5_0
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
  scr dom_13 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_13 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_13 roots_13 goal_13 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_13 goal_13 := by
    have h0 : isConstB dom_13 goal_13 = false := by decide +kernel
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

end S_13

theorem low_13 : Lower dom_13 roots_13 goal_13 7 := S_13.noCircuit

def dom_14 : Nat := 0xffff
def goal_14 : Nat := 0xf8c8
def roots_14 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

theorem low_14 : Lower dom_14 roots_14 goal_14 4 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord36, 14), (PEqualNP.Outside.L_meta_28352_aux.certWord19, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_15 : Nat := 0xffffffff
def goal_15 : Nat := 0xffeaf8c8
def roots_15 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_15
def pairsG : List (Nat × Nat) := [(1, 3), (1, 17), (2, 3), (2, 6), (4, 6), (4, 12), (5, 7), (5, 13), (5, 21), (8, 12), (8, 24), (9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (10, 26), (16, 17), (16, 24), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28)]
def r1sG : List Nat := [1, 1, 2, 2, 4, 4, 5, 5, 5, 8, 8, 9, 9, 9, 10, 10, 10, 16, 16, 18, 18, 18, 20, 20, 20]
def r2sG : List Nat := [3, 17, 3, 6, 6, 12, 7, 13, 21, 12, 24, 11, 13, 25, 11, 14, 26, 17, 24, 19, 22, 26, 21, 22, 28]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_15.map (· &&& dom_15)
def goalM : Nat := goal_15 &&& dom_15
def NN : Nat → Nat
  | 5 => 4
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord37
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord38
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord39
  | 6, 0, 0 => 0x6ad15
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord40
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord41
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 8 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
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
  | 4 => 4
  | 5 => 3
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord42
  | 5, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord43
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x400000
  | 5, 0 => 0x100000800001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 3 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_6 roots_6 4 s ws hint
  | 1 => checkCutEntry dom_12 roots_12 4 s ws hint
  | 2 => checkCutEntry dom_14 roots_14 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_28352_aux.certWord36, 14), (PEqualNP.Outside.L_meta_28352_aux.certWord19, 4)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord28, 12)], [(PEqualNP.Outside.L_meta_28352_aux.certWord44, 15), (PEqualNP.Outside.L_meta_28352_aux.certWord36, 14), (PEqualNP.Outside.L_meta_28352_aux.certWord28, 12), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord29, 7), (PEqualNP.Outside.L_meta_28352_aux.certWord36, 14), (PEqualNP.Outside.L_meta_28352_aux.certWord19, 4), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord29, 7), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2)], [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord45, 6), (PEqualNP.Outside.L_meta_28352_aux.certWord28, 12), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord16, 2), (PEqualNP.Outside.L_meta_28352_aux.certWord19, 4), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)], [(PEqualNP.Outside.L_meta_28352_aux.certWord44, 15), (PEqualNP.Outside.L_meta_28352_aux.certWord45, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15 == dom_15) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15 goalM u ys) : RunD dom_15 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := z5_0
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
  scr dom_15 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_15 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15 roots_15 goal_15 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15 goal_15 := by
    have h0 : isConstB dom_15 goal_15 = false := by decide +kernel
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

end S_15

theorem low_15 : Lower dom_15 roots_15 goal_15 7 := S_15.noCircuit

def dom_16 : Nat := 0x5555555555555555
def goal_16 : Nat := 0x5555555055405040
def roots_16 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 7 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13

def dom_17 : Nat := 0x4444444444444444
def goal_17 : Nat := 0x4444444044404040
def roots_17 : List Nat := [0x4040404040404040, 0x4400440044004400, 0x4444000044440000, 0x4444444400000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_18 : Nat := 0xcccccccccccccccc
def goal_18 : Nat := 0xccccccc8ccc8c8c8
def roots_18 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888888888888888, 2, 3)] (by decide +kernel) (by decide +kernel) low_17

def dom_19 : Nat := 0xff00ff00ff00ff
def goal_19 : Nat := 0xff00fa00ea00c8
def roots_19 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc, 1, 3)] (by decide +kernel) (by decide +kernel) low_4

def dom_20 : Nat := 0xffff0000ffff
def goal_20 : Nat := 0xfffa0000f8c8
def roots_20 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 6 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord46, 31), (PEqualNP.Outside.L_meta_28352_aux.certWord21, 30), (PEqualNP.Outside.L_meta_28352_aux.certWord47, 28), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19

def dom_21 : Nat := 0x555500005555
def goal_21 : Nat := 0x555000005040
def roots_21 : List Nat := [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 5 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord19, 4), (PEqualNP.Outside.L_meta_28352_aux.certWord15, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_22 : Nat := 0xff00ff
def goal_22 : Nat := 0xea00c8
def roots_22 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

theorem low_22 : Lower dom_22 roots_22 goal_22 4 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord36, 14), (PEqualNP.Outside.L_meta_28352_aux.certWord19, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_23 : Nat := 0x55555555
def goal_23 : Nat := 0x55405040
def roots_23 : List Nat := [0x44444444, 0x50505050, 0x55005500, 0x55550000]

theorem low_23 : Lower dom_23 roots_23 goal_23 4 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord17, 1), (PEqualNP.Outside.L_meta_28352_aux.certWord28, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_24 : Nat := 0x55005500550055
def goal_24 : Nat := 0x55005000400040
def roots_24 : List Nat := [0x44004400440044, 0x50005000500050, 0x55000000550000, 0x55005500000000]

theorem low_24 : Lower dom_24 roots_24 goal_24 4 :=
  lower_iso [(PEqualNP.Outside.L_meta_28352_aux.certWord15, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23

def dom_25 : Nat := 0xffffffffffffffff
def goal_25 : Nat := 0xfffffffaffeaf8c8
def roots_25 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_25
def pairsG : List (Nat × Nat) := [(1, 3), (1, 17), (1, 33), (2, 3), (2, 6), (4, 6), (4, 12), (4, 36), (5, 7), (5, 13), (5, 21), (5, 37), (8, 12), (8, 24), (8, 40), (9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 26), (10, 42), (16, 17), (16, 24), (16, 48), (18, 19), (18, 22), (18, 26), (18, 50), (20, 21), (20, 22), (20, 28), (20, 52), (32, 33), (32, 36), (32, 40), (32, 48), (34, 35), (34, 38), (34, 42), (34, 50)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 4, 4, 4, 5, 5, 5, 5, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 16, 16, 16, 18, 18, 18, 18, 20, 20, 20, 20, 32, 32, 32, 32, 34, 34, 34, 34]
def r2sG : List Nat := [3, 17, 33, 3, 6, 6, 12, 36, 7, 13, 21, 37, 12, 24, 40, 11, 13, 25, 41, 11, 14, 26, 42, 17, 24, 48, 19, 22, 26, 50, 21, 22, 28, 52, 33, 36, 40, 48, 35, 38, 42, 50]
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_25.map (· &&& dom_25)
def goalM : Nat := goal_25 &&& dom_25
def NN : Nat → Nat
  | 5 => 25
  | 6 => 99
  | 7 => 118
  | 8 => 17
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord48
  | 6, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord49
  | 6, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord50
  | 7, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord51
  | 7, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord52
  | 8, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord53
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord54
  | 0, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord55
  | 0, 2 => PEqualNP.Outside.L_meta_28352_aux.certWord56
  | 0, 3 => PEqualNP.Outside.L_meta_28352_aux.certWord57
  | 0, 4 => PEqualNP.Outside.L_meta_28352_aux.certWord58
  | 0, 5 => PEqualNP.Outside.L_meta_28352_aux.certWord59
  | 0, 6 => PEqualNP.Outside.L_meta_28352_aux.certWord60
  | 0, 7 => PEqualNP.Outside.L_meta_28352_aux.certWord61
  | 0, 8 => PEqualNP.Outside.L_meta_28352_aux.certWord62
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord63
  | 5, 0, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord64
  | 6, 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord65
  | 6, 0, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord66
  | 6, 0, 2 => PEqualNP.Outside.L_meta_28352_aux.certWord67
  | 6, 0, 3 => PEqualNP.Outside.L_meta_28352_aux.certWord68
  | 6, 0, 4 => PEqualNP.Outside.L_meta_28352_aux.certWord69
  | 6, 0, 5 => PEqualNP.Outside.L_meta_28352_aux.certWord70
  | 6, 0, 6 => PEqualNP.Outside.L_meta_28352_aux.certWord71
  | 7, 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord72
  | 7, 0, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord73
  | 7, 0, 2 => PEqualNP.Outside.L_meta_28352_aux.certWord74
  | 7, 0, 3 => PEqualNP.Outside.L_meta_28352_aux.certWord75
  | 7, 0, 4 => PEqualNP.Outside.L_meta_28352_aux.certWord76
  | 7, 0, 5 => PEqualNP.Outside.L_meta_28352_aux.certWord77
  | 7, 0, 6 => PEqualNP.Outside.L_meta_28352_aux.certWord78
  | 7, 0, 7 => PEqualNP.Outside.L_meta_28352_aux.certWord79
  | 8, 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord80
  | 8, 0, 1 => 0xd17a93c5ca947
  | 9, 0, 0 => 0x1a293c5ca946
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 46
  | 6 => 53
  | 7 => 60
  | 8 => 53
  | 9 => 46
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord81
  | 0, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord82
  | 0, 2 => PEqualNP.Outside.L_meta_28352_aux.certWord83
  | 0, 3 => PEqualNP.Outside.L_meta_28352_aux.certWord84
  | 0, 4 => PEqualNP.Outside.L_meta_28352_aux.certWord85
  | 0, 5 => PEqualNP.Outside.L_meta_28352_aux.certWord86
  | 0, 6 => PEqualNP.Outside.L_meta_28352_aux.certWord87
  | 0, 7 => PEqualNP.Outside.L_meta_28352_aux.certWord88
  | 0, 8 => PEqualNP.Outside.L_meta_28352_aux.certWord89
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord90
  | 0, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord91
  | 0, 2 => PEqualNP.Outside.L_meta_28352_aux.certWord92
  | 0, 3 => PEqualNP.Outside.L_meta_28352_aux.certWord93
  | 0, 4 => PEqualNP.Outside.L_meta_28352_aux.certWord94
  | 0, 5 => PEqualNP.Outside.L_meta_28352_aux.certWord95
  | 0, 6 => PEqualNP.Outside.L_meta_28352_aux.certWord96
  | 0, 7 => PEqualNP.Outside.L_meta_28352_aux.certWord97
  | 0, 8 => PEqualNP.Outside.L_meta_28352_aux.certWord98
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 42 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 42 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 70 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 70 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 70 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 70 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 7 0) :: stateWiresD n (ids >>> 7)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 7 0) :: stateWiresS n (ids >>> 7)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 35
  | 5 => 183
  | 6 => 638
  | 7 => 550
  | 8 => 11
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord99
  | 5, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord100
  | 5, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord101
  | 5, 2 => PEqualNP.Outside.L_meta_28352_aux.certWord102
  | 6, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord103
  | 6, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord104
  | 6, 2 => PEqualNP.Outside.L_meta_28352_aux.certWord105
  | 6, 3 => PEqualNP.Outside.L_meta_28352_aux.certWord106
  | 6, 4 => PEqualNP.Outside.L_meta_28352_aux.certWord107
  | 6, 5 => PEqualNP.Outside.L_meta_28352_aux.certWord108
  | 6, 6 => PEqualNP.Outside.L_meta_28352_aux.certWord109
  | 6, 7 => PEqualNP.Outside.L_meta_28352_aux.certWord110
  | 6, 8 => PEqualNP.Outside.L_meta_28352_aux.certWord111
  | 6, 9 => PEqualNP.Outside.L_meta_28352_aux.certWord112
  | 7, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord113
  | 7, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord114
  | 7, 2 => PEqualNP.Outside.L_meta_28352_aux.certWord115
  | 7, 3 => PEqualNP.Outside.L_meta_28352_aux.certWord116
  | 7, 4 => PEqualNP.Outside.L_meta_28352_aux.certWord117
  | 7, 5 => PEqualNP.Outside.L_meta_28352_aux.certWord118
  | 7, 6 => PEqualNP.Outside.L_meta_28352_aux.certWord119
  | 7, 7 => PEqualNP.Outside.L_meta_28352_aux.certWord120
  | 7, 8 => PEqualNP.Outside.L_meta_28352_aux.certWord121
  | 8, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord122
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord123
  | 4, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord124
  | 5, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord125
  | 5, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord126
  | 5, 2 => PEqualNP.Outside.L_meta_28352_aux.certWord127
  | 5, 3 => PEqualNP.Outside.L_meta_28352_aux.certWord128
  | 5, 4 => PEqualNP.Outside.L_meta_28352_aux.certWord129
  | 5, 5 => PEqualNP.Outside.L_meta_28352_aux.certWord130
  | 6, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord131
  | 6, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord132
  | 6, 2 => PEqualNP.Outside.L_meta_28352_aux.certWord133
  | 6, 3 => PEqualNP.Outside.L_meta_28352_aux.certWord134
  | 6, 4 => PEqualNP.Outside.L_meta_28352_aux.certWord135
  | 6, 5 => PEqualNP.Outside.L_meta_28352_aux.certWord136
  | 6, 6 => PEqualNP.Outside.L_meta_28352_aux.certWord137
  | 6, 7 => PEqualNP.Outside.L_meta_28352_aux.certWord138
  | 6, 8 => PEqualNP.Outside.L_meta_28352_aux.certWord139
  | 6, 9 => PEqualNP.Outside.L_meta_28352_aux.certWord140
  | 6, 10 => PEqualNP.Outside.L_meta_28352_aux.certWord141
  | 6, 11 => PEqualNP.Outside.L_meta_28352_aux.certWord142
  | 6, 12 => PEqualNP.Outside.L_meta_28352_aux.certWord143
  | 6, 13 => PEqualNP.Outside.L_meta_28352_aux.certWord144
  | 6, 14 => PEqualNP.Outside.L_meta_28352_aux.certWord145
  | 6, 15 => PEqualNP.Outside.L_meta_28352_aux.certWord146
  | 6, 16 => PEqualNP.Outside.L_meta_28352_aux.certWord147
  | 6, 17 => PEqualNP.Outside.L_meta_28352_aux.certWord148
  | 6, 18 => PEqualNP.Outside.L_meta_28352_aux.certWord149
  | 6, 19 => PEqualNP.Outside.L_meta_28352_aux.certWord150
  | 7, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord151
  | 7, 1 => PEqualNP.Outside.L_meta_28352_aux.certWord152
  | 7, 2 => PEqualNP.Outside.L_meta_28352_aux.certWord153
  | 7, 3 => PEqualNP.Outside.L_meta_28352_aux.certWord154
  | 7, 4 => PEqualNP.Outside.L_meta_28352_aux.certWord155
  | 7, 5 => PEqualNP.Outside.L_meta_28352_aux.certWord156
  | 7, 6 => PEqualNP.Outside.L_meta_28352_aux.certWord157
  | 7, 7 => PEqualNP.Outside.L_meta_28352_aux.certWord158
  | 7, 8 => PEqualNP.Outside.L_meta_28352_aux.certWord159
  | 7, 9 => PEqualNP.Outside.L_meta_28352_aux.certWord160
  | 7, 10 => PEqualNP.Outside.L_meta_28352_aux.certWord161
  | 7, 11 => PEqualNP.Outside.L_meta_28352_aux.certWord162
  | 7, 12 => PEqualNP.Outside.L_meta_28352_aux.certWord163
  | 7, 13 => PEqualNP.Outside.L_meta_28352_aux.certWord164
  | 7, 14 => PEqualNP.Outside.L_meta_28352_aux.certWord165
  | 7, 15 => PEqualNP.Outside.L_meta_28352_aux.certWord166
  | 7, 16 => PEqualNP.Outside.L_meta_28352_aux.certWord167
  | 7, 17 => PEqualNP.Outside.L_meta_28352_aux.certWord168
  | 8, 0 => PEqualNP.Outside.L_meta_28352_aux.certWord169
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_7 roots_7 7 s ws hint
  | 1 => checkCutEntry dom_13 roots_13 7 s ws hint
  | 2 => checkCutEntry dom_15 roots_15 7 s ws hint
  | 3 => checkCutEntry dom_16 roots_16 7 s ws hint
  | 4 => checkCutEntry dom_18 roots_18 6 s ws hint
  | 5 => checkCutEntry dom_19 roots_19 6 s ws hint
  | 6 => checkCutEntry dom_20 roots_20 6 s ws hint
  | 7 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 8 => checkCutEntry dom_21 roots_21 5 s ws hint
  | 9 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 10 => checkCutEntry dom_9 roots_9 5 s ws hint
  | 11 => checkCutEntry dom_5 roots_5 5 s ws hint
  | 12 => checkCutEntry dom_17 roots_17 5 s ws hint
  | 13 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 14 => checkCutEntry dom_12 roots_12 4 s ws hint
  | 15 => checkCutEntry dom_6 roots_6 4 s ws hint
  | 16 => checkCutEntry dom_11 roots_11 4 s ws hint
  | 17 => checkCutEntry dom_14 roots_14 4 s ws hint
  | 18 => checkCutEntry dom_22 roots_22 4 s ws hint
  | 19 => checkCutEntry dom_23 roots_23 4 s ws hint
  | 20 => checkCutEntry dom_24 roots_24 4 s ws hint
  | 21 => checkCutEntry dom_0 roots_0 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_25 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_22 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_25 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(PEqualNP.Outside.L_meta_28352_aux.certWord18, 3), (PEqualNP.Outside.L_meta_28352_aux.certWord14, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_25 == dom_25) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_25 goalM u ys) : RunD dom_25 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_25 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
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
theorem z5_24 : ∀ i, 24 ≤ i → i < 25 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 24 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 25 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (z5_24)))
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
theorem z6_96 : ∀ i, 96 ≤ i → i < 99 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 96 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 99 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (z6_96))))))))))))
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
theorem z7_112 : ∀ i, 112 ≤ i → i < 118 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 112 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 118 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (z7_112))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 17 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 16 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 17 → Z 8 i = true := range_split z8_0 (range_split z8_8 (z8_16))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_0 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := z9_0
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
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
def RootG (s : Nat) : Bool :=
  scr dom_25 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_25 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_25 roots_25 goal_25 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_25 goal_25 := by
    have h0 : isConstB dom_25 goal_25 = false := by decide +kernel
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

end S_25

theorem low_25 : Lower dom_25 roots_25 goal_25 10 := S_25.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_25_bits : ∀ r : Fin 64, roots_25.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_25_lt : ∀ r : Fin 64, dom_25.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_25 T)
    (hlow : Lower dom_25 roots_25 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_25, Avail mask256 roots_25 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_25 hfan 0 roots_25 roots_25 rfl hsup0
  set out := (execN C.gates roots_25).getD C.output 0
  have hout : out &&& dom_25 = T &&& dom_25 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_25_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_25 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_25_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_25).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_25)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_25.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_25 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_25).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_25 &&& mask256 = dom_25 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_25 = T &&& dom_25 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_25, hd63, hout]
  have hnc_m : ¬ IsConst dom_25 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_25 roots_25 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_25, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_25 roots_25 0 roots_25 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x => (x 0 && x 1) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 2 && x 3) || (x 2 && x 5) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_25.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem rootBound : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_25 10 hT6 (by unfold IsConst; decide) low_25

end PEqualNP.Outside.L_meta_28352_aux

namespace PEqualNP.Outside.L_meta_28352
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

def g0 : (Fin 8 → Bool) → Bool := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 6) || (x 2 && x 7) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 7)
def g1 : (Fin 8 → Bool) → Bool := fun x => g0 (Function.update x 6 false)
theorem dep0 : ∃ x : Fin 8 → Bool, g0 (Function.update x 6 (!x 6)) ≠ g0 x :=
  ⟨fun i => decide (i = 0), by decide +kernel⟩
theorem keep0 : ∃ x y : Fin 8 → Bool, g0 (Function.update x 6 false) ≠ g0 (Function.update y 6 false) :=
  ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 3), by decide +kernel⟩
def g2 : (Fin 8 → Bool) → Bool := fun x => g1 (Function.update x 2 false)
theorem dep1 : ∃ x : Fin 8 → Bool, g1 (Function.update x 2 (!x 2)) ≠ g1 x :=
  ⟨fun i => decide (i = 5), by decide +kernel⟩
theorem keep1 : ∃ x y : Fin 8 → Bool, g1 (Function.update x 2 false) ≠ g1 (Function.update y 2 false) :=
  ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 3), by decide +kernel⟩
def identify (i : Fin 8) : Fin 6 := match i.val with
  | 0 => 4
  | 1 => 2
  | 2 => 0
  | 3 => 0
  | 4 => 3
  | 5 => 1
  | 6 => 0
  | _ => 5
theorem image : (fun x : Fin 6 → Bool => g2 (x ∘ identify)) = PEqualNP.Outside.L_meta_28352_aux.fG := by decide +kernel

theorem lower (t : ℕ) (h0 : HasCircuitSize 8 g0 t) : 12 ≤ t := by
  obtain ⟨s1, c1, h1⟩ := one_gate_at 7 g0 6 false t dep0 keep0 h0
  change HasCircuitSize 8 g1 s1 at h1
  obtain ⟨s2, c2, h2⟩ := one_gate_at 7 g1 2 false s1 dep1 keep1 h1
  change HasCircuitSize 8 g2 s2 at h2
  have r := relabel_size identify g2 s2 h2
  rw [image] at r
  have hl := PEqualNP.Outside.L_meta_28352_aux.rootBound s2 r
  omega

def wg : List Gate := [⟨GateOp.or, [7, 6]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [9, 1]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.and, [4, 14]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [17, 18]⟩]

theorem wfits : ∀ g ∈ wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wg, 19⟩ (List.ofFn x) = g0 x := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem bridge : ∀ x : Fin 8 → Bool, g0 x = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel

end PEqualNP.Outside.L_meta_28352

theorem PEqualNP.Outside.L_meta_28352 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  have h := PEqualNP.Outside.L_meta_28352.lower gates.length ⟨⟨gates, o⟩, legal, le_rfl, fun x => (computes x).trans (PEqualNP.Outside.L_meta_28352.bridge x).symm⟩
  have hw : PEqualNP.Outside.L_meta_28352.wg.length = 12 := rfl
  exact ⟨PEqualNP.Outside.L_meta_28352.wg, 19, PEqualNP.Outside.L_meta_28352.wfits, by omega, fun x => (PEqualNP.Outside.L_meta_28352.weval x).trans (PEqualNP.Outside.L_meta_28352.bridge x)⟩

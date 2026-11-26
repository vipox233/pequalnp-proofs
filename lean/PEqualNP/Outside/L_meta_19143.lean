import PEqualNP.Defs
import PEqualNP.Library.Helpers.PromiseCol

namespace PEqualNP.Outside.L_meta_19143
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Library.Helpers.PromiseCol

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1,t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [
(true,9,39),(true,8,33),(true,6,10),(true,47,54),(true,35,66),(true,1,52),(true,4,62),(true,24,58),(true,25,60),(true,5,20),(true,11,32),(true,28,53),
(true,0,34),(true,0,67),(true,2,18),(true,2,37),(true,3,26),(true,3,47),(true,4,21),(true,10,52),(true,12,50),(true,13,36),(true,13,61),(true,14,42),
(true,15,75),(true,16,65),(true,19,43),(true,21,72),(true,23,51),(true,25,45),(true,28,73),(true,30,74),(true,36,41),(true,36,68),(true,39,48),(true,40,42),
(true,40,46),(true,43,71),(true,44,69),(true,61,64),(true,18,96),(true,27,101),(true,55,78),(true,9,55),(true,107,73),(true,108,76),(true,109,99),(true,6,14),
(true,111,21),(true,112,51),(true,113,63),(true,114,93),(true,15,19),(true,45,100),(true,0,52),(true,118,87),(true,119,97),(true,17,24),(true,121,37),(true,122,72),
(true,123,95),(true,0,56),(true,125,68),(true,126,91),(true,70,80),(true,128,100),(true,129,102),(true,7,22),(true,131,61),(true,132,77),(true,133,93),(true,28,42),
(true,135,44),(true,136,65),(true,137,66),(true,138,84),(true,16,29),(true,140,38),(true,141,48),(true,142,77),(true,106,27),(true,144,42),(true,145,57),(true,146,86),
(true,17,31),(true,148,59),(true,149,62),(true,150,76),(true,151,90),(true,38,55),(true,153,85),(true,154,88),(true,155,102),(true,1,48),(true,157,50),(true,158,58),
(true,159,91),(true,160,94),(true,104,15),(true,162,92),(true,65,69),(true,164,71),(true,15,43),(true,166,45),(true,167,74),(true,168,80),(true,169,98),(true,64,79),
(true,171,81),(true,172,97),(true,105,26),(true,174,46),(true,175,82),(true,48,54),(true,106,29),(true,178,59),(true,179,103),(true,105,49),(true,181,63),(true,182,94),
(true,25,59),(true,184,79),(true,185,83),(true,186,92),(true,70,81),(true,188,89),(true,189,98),(true,3,25),(true,191,31),(true,192,41),(true,193,84),(true,194,103),
(true,20,29),(true,196,54),(true,197,60),(true,198,83),(true,199,85),(true,34,64),(true,201,70),(true,202,88),(true,22,26),(true,204,35),(true,205,54),(true,206,57),
(true,207,89),(true,4,67),(true,209,86),(true,210,87),(true,211,90),(true,104,75),(true,213,95),(true,9,18),(true,215,24),(true,216,25),(true,41,45),(true,218,62),
(true,219,99),(false,110,115),(false,120,124),(false,127,130),(false,134,139),(false,143,147),(false,152,156),(false,161,163),(false,165,170),(false,173,176),(false,180,183),(false,187,190),
(false,195,200),(false,203,208),(false,212,214),(false,116,117),(false,82,177),(false,217,220),(true,221,222),(true,223,224),(true,225,226),(true,227,228),(true,229,230),(true,231,232),
(true,233,234),(true,235,236),(true,238,239),(true,240,241),(true,242,243),(true,244,245),(true,246,247),(true,248,249),(true,250,251),(true,252,237)]

def circuit : Circuit := ⟨codes.map asGate, 253⟩
def rows : List ℕ := ([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ)

theorem fan : FanInTwo circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem good : PEqualNP.Represents.Represents
    (fun u v : Fin 32 => (rows.getD u.val 0).testBit v.val) circuit := by
  apply represents_of_pcols (N := 10) (by decide) circuit rows
  · have hh : rows.all (fun x => decide (x < 2 ^ 32)) = true := by decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hh x hx)
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_19143

open PEqualNP.Outside.L_meta_19143
theorem PEqualNP.Outside.L_meta_19143 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 190 ∧ PEqualNP.Represents.Represents (fun u v : Fin 32 => (([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ).getD u.val 0).testBit v.val) C := by
  exact ⟨circuit, fan, by decide +kernel, good⟩

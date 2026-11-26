import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19835

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 12]⟩,
      ⟨GateOp.or, [10, 15]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.or, [18, 19]⟩,
      ⟨GateOp.and, [0, 20]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [22, 18]⟩,
      ⟨GateOp.and, [1, 23]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [25, 17]⟩,
      ⟨GateOp.and, [2, 26]⟩,
      ⟨GateOp.or, [17, 19]⟩,
      ⟨GateOp.and, [3, 28]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [30, 18]⟩,
      ⟨GateOp.and, [4, 31]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [33, 16]⟩,
      ⟨GateOp.and, [5, 34]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [36, 16]⟩,
      ⟨GateOp.and, [6, 37]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.and, [7, 39]⟩,
      ⟨GateOp.or, [21, 24]⟩,
      ⟨GateOp.or, [41, 27]⟩,
      ⟨GateOp.or, [42, 29]⟩,
      ⟨GateOp.or, [43, 32]⟩,
      ⟨GateOp.or, [44, 35]⟩,
      ⟨GateOp.or, [45, 38]⟩,
      ⟨GateOp.or, [46, 40]⟩
    ],
    output := 47 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (10768418131862349930 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19835

theorem PEqualNP.Outside.L_meta_19835 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10768418131862349930 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19835.ckt, PEqualNP.Outside.L_meta_19835.mono, by decide, PEqualNP.Outside.L_meta_19835.rep⟩

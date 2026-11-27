import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25569
import PEqualNP.Outside.L_meta_25559
import PEqualNP.Outside.L_meta_25562

namespace PEqualNP.Outside.L_meta_25784_aux
open CircuitLowerBounds MetaComplexity.NestedCover L_meta_25569_aux

private theorem source_split {n m : Nat} {S : Finset Nat} (small : ∀ w ∈ S, w < n+m) :
    ∃ (R : Finset (Fin n)) (B : Finset (Fin m)),
      S = R.image Fin.val ∪ B.image (fun j => n+j.val) ∧ S.card ≤ R.card+B.card := by
  let R := Finset.univ.filter (fun i : Fin n => i.val ∈ S)
  let B := Finset.univ.filter (fun j : Fin m => n+j.val ∈ S)
  have eq : S = R.image Fin.val ∪ B.image (fun j => n+j.val) := by
    ext w
    constructor
    · intro hw
      by_cases h : w<n
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨w,h⟩, by simp [R,hw], rfl⟩)
      · have lt : w - n < m := by have := small w hw; omega
        have e : n+(w-n)=w := by omega
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨w-n,lt⟩, by simp [B,e,hw], e⟩)
    · intro hw
      rcases Finset.mem_union.mp hw with hw|hw
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hi).2
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hj).2
  refine ⟨R,B,eq,?_⟩
  rw [eq]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

private theorem region_cap {n m : Nat} {G : Fin n → Fin m → Bool} {C : Circuit}
    (dr : ∀ a b : Fin n, a ≠ b → 6 ≤ (Finset.univ.filter (fun col => G a col ≠ G b col)).card)
    (dc : ∀ a b : Fin m, a ≠ b → 6 ≤ (Finset.univ.filter (fun row => G row a ≠ G row b)).card)
    (back : ReadsBack (n+m) C) (rep : Represents.Represents G C)
    {S E : Finset Nat} (raw : ∀ w ∈ S, w < n+m) (tree : tree69 (n+m) C S E) :
    (E = ∅ → S.card ≤ 4) ∧ (∀ b, E = {b} → S.card ≤ 6) := by
  obtain ⟨R,B,hS,hcard⟩ := source_split raw
  rw [hS] at tree
  obtain ⟨reg,root,hreg,hroot,hzero,hentry,hgates,huse⟩ := tree
  have valid : reg ⊆ Finset.range C.size := fun _ hj => (Finset.mem_filter.mp (hreg hj)).1
  constructor
  · rintro rfl
    apply hcard.trans
    apply L_meta_25559 n m G C R B reg root
      (fun a b h => (by decide : 5 ≤ 6).trans (dr a b h))
      (fun a b h => (by decide : 5 ≤ 6).trans (dc a b h)) back rep valid hroot _ hzero huse
    intro j hj
    obtain ⟨op,len,hin⟩ := hgates j hj
    exact ⟨op,len,fun w hw => (hin w hw).resolve_right (Finset.notMem_empty w)⟩
  · intro b hb
    subst E
    obtain ⟨out,lt,one⟩ := hentry b (Finset.mem_singleton_self b)
    apply hcard.trans
    apply L_meta_25562 n m G C R B reg root b dr dc back rep valid hroot out lt one _ hzero huse
    intro j hj
    obtain ⟨op,len,hin⟩ := hgates j hj
    exact ⟨op,len,fun w hw => (hin w hw).imp_right Finset.mem_singleton.mp⟩

private theorem card_regions (L : List (Finset Nat)) (k : Nat)
    (cap : ∀ S ∈ L, (S : Finset Nat).card ≤ k) :
    (L.toFinset.biUnion id).card ≤ k * L.length := by
  classical
  induction L with
  | nil => simp
  | cons S L ih =>
    have e : (S::L).toFinset.biUnion id = S ∪ L.toFinset.biUnion id := by
      ext w; simp [Finset.mem_biUnion]
    rw [e, List.length_cons, Nat.mul_succ]
    exact (Finset.card_union_le _ _).trans (by
      have h := cap S (List.mem_cons_self ..)
      have t := ih (fun A hA => cap A (List.mem_cons_of_mem _ hA))
      omega)

private theorem mask_sum (L : List Nat) (S : Finset Nat) :
    (∑ w ∈ S, L.count w) = L.countP (fun w => decide (w∈S)) := by
  classical
  let F := L.filter (fun w => decide (w∈S))
  have sub : F.toFinset ⊆ S := by
    intro w hw
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  calc
    _ = ∑ w ∈ S, F.count w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (List.count_filter (by simpa using hw)).symm
    _ = ∑ w ∈ F.toFinset, F.count w := by
      symm
      exact Finset.sum_subset sub (fun w _ hw =>
        List.count_eq_zero.mpr (fun hit => hw (List.mem_toFinset.mpr hit)))
    _ = F.length := List.sum_toFinset_count_eq_length F
    _ = _ := List.countP_eq_length_filter.symm

private theorem budget (N : Nat) (C : Circuit) (sh : shapes69 C) (back : ReadsBack N C) :
    let raw := Finset.range N
    let r := reads69 C
    let pre := (gates69 C).filter (fun j => j+1<C.size)
    let R := ∑ w ∈ raw, (r w-1)
    let J := ∑ j ∈ pre, (r (N+j)-1)
    let D := (neg69 C).card+R+J
    ((raw.filter (fun w => 0<r w)).card ≤ (once69 N C).card+R) ∧
      exits69 N C ≤ 2*D ∧ entries69 N C ≤ 2*D := by
  classical
  dsimp only
  let U := Finset.range N
  let T := gates69 C
  let P := T.filter (fun j => j+1<C.size)
  let r := reads69 C
  let Z := neg69 C
  let A := T \ ordinary N C
  let R := ∑ w ∈ U, (r w-1)
  let J := ∑ j ∈ P, (r (N+j)-1)
  let D := Z.card+R+J
  have rawsp {w : Nat} (hw : w<N) : w∈special N C ↔ 2≤r w := by
    simp only [special, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro (⟨_,hh⟩ | ⟨j,_,e⟩)
      · exact hh
      · omega
    · exact fun h => Or.inl ⟨by omega,h⟩
  have gatsp {j : Nat} (hj : j<C.size) : N+j∈special N C ↔ j∈Z ∨ 2≤r (N+j) := by
    simp only [special, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro (⟨_,hh⟩ | ⟨i,hi,e⟩)
      · exact Or.inr hh
      · have : i=j := by omega
        exact Or.inl (this ▸ hi)
    · rintro (hz|hm)
      · exact Or.inr ⟨j,hz,rfl⟩
      · exact Or.inl ⟨by omega,hm⟩
  have early {j : Nat} (hj : j<C.size) (used : 0<r (N+j)) : j+1<C.size := by
    by_contra! late
    have z : r (N+j)=0 := by
      unfold r reads69 readsIn
      apply Finset.sum_eq_zero
      intro i hi
      apply List.count_eq_zero.mpr
      intro hit
      have ilt : i<C.size := Finset.mem_range.mp hi
      have := back i ilt (N+j) hit
      omega
    omega
  have a_eq : A = T.filter (fun j => N+j∈special N C) := by
    ext j; simp [A,T,ordinary]; tauto
  have raw_card : (U.filter (fun w => 0<r w)).card ≤ (once69 N C).card+R := by
    change _ ≤ (U.filter (fun w => r w=1)).card+_
    simp only [Finset.card_filter, R, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w _
    split_ifs <;> omega
  have gate_card : A.card ≤ Z.card+J := by
    rw [a_eq, Finset.card_filter]
    change _ ≤ (T.filter (fun j => (gateAt C j).op = .not)).card + ∑ j ∈ P, (r (N+j)-1)
    rw [Finset.card_filter, show (∑ j ∈ P, (r (N+j)-1)) =
      ∑ j ∈ T, if j+1<C.size then r (N+j)-1 else 0 from Finset.sum_filter _ _, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have js : j<C.size := Finset.mem_range.mp hj
    have h := gatsp js
    have hm : 2≤r (N+j) → j+1<C.size := fun many => early js (by omega)
    have hz : j∈Z ↔ (gateAt C j).op = .not := by simp [Z, neg69, hj, T]
    rw [hz] at h
    by_cases hs : N+j∈special N C
    · rcases h.mp hs with hn|many
      · simp [hs, hn]
      · simp [hs, hm many]
        omega
    · simp [hs]
  have exit : exits69 N C ≤ 2*D := by
    calc
      _ ≤ ∑ _ ∈ A, 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have js : j<C.size := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
        have mem : gateAt C j ∈ C.gates :=
          L_meta_25562_aux.Profile.Wire.gateAt_mem js
        have len : (gateAt C j).inputs.length ≤ 2 := by rcases sh _ mem with h|h <;> omega
        exact (List.countP_le_length ..).trans len
      _ = 2*A.card := by simp [Nat.mul_comm]
      _ ≤ _ := by omega
  have special_reads : (∑ w ∈ special N C, r w) ≤ 2*D := by
    have sub : special N C ⊆ Finset.range (N+C.size) := by
      intro w hw
      rcases Finset.mem_union.mp hw with h|h
      · exact (Finset.mem_filter.mp h).1
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        have js : j<C.size := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        exact Finset.mem_range.mpr (by omega)
    have e : special N C = (Finset.range (N+C.size)).filter (fun w => w∈special N C) := by
      ext w; exact ⟨fun hw => Finset.mem_filter.mpr ⟨sub hw,hw⟩, fun hw => (Finset.mem_filter.mp hw).2⟩
    rw [e, Finset.sum_filter, Finset.sum_range_add]
    have rbound : (∑ w ∈ U, if w∈special N C then r w else 0) ≤ 2*R := by
      dsimp only [R]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro w hw
      have h := rawsp (Finset.mem_range.mp hw)
      by_cases hs : w∈special N C
      · simp only [if_pos hs]
        have := h.mp hs
        omega
      · simp [hs]
    have jbound : (∑ j ∈ T, if N+j∈special N C then r (N+j) else 0) ≤ 2*(Z.card+J) := by
      dsimp only [J,P,Z]
      rw [Nat.mul_add, Finset.sum_filter, neg69, Finset.card_filter,
        Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j hj
      have js : j<C.size := Finset.mem_range.mp hj
      have h := gatsp js
      have hz : j∈Z ↔ (gateAt C j).op = .not := by simp [Z, neg69, hj, T]
      rw [hz] at h
      by_cases hs : N+j∈special N C
      · by_cases he : j+1<C.size
        · rcases h.mp hs with hn|many
          · simp [hs, he, hn]
            omega
          · simp [hs, he]
            omega
        · have hz0 : r (N+j)=0 := by
            by_contra hn
            exact he (early js (by omega))
          simp [hs, hz0]
      · simp [hs]
    change (∑ w ∈ U, if w∈special N C then r w else 0) +
      (∑ j ∈ T, if N+j∈special N C then r (N+j) else 0) ≤ _
    omega
  have entry : entries69 N C ≤ 2*D := by
    calc
      _ ≤ ∑ j ∈ T, (gateAt C j).inputs.countP (fun w => decide (w∈special N C)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact fun j hj => (Finset.mem_filter.mp hj).1
        · exact fun _ _ _ => Nat.zero_le _
      _ = ∑ w ∈ special N C, r w := by
        simp_rw [← mask_sum]
        exact Finset.sum_comm
      _ ≤ _ := special_reads
  exact ⟨raw_card,exit,entry⟩

end PEqualNP.Outside.L_meta_25784_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_25569_aux PEqualNP.Outside.L_meta_25784_aux in
theorem PEqualNP.Outside.L_meta_25784 :
∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → 6 ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
  (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → 6 ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
  PEqualNP.Represents.Represents G C →
  let gates := Finset.range C.size
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)) gates
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  0 < C.size → C.output + 1 = (n + m) + C.size →
  (∀ j < C.size, j + 1 < C.size → 0 < reads ((n + m) + j)) →
  let q := ((Finset.range (n + m)).filter (fun w => 0 < reads w)).card
  let defect := neg.card + (∑ w ∈ Finset.range (n + m), (reads w - 1)) +
    (∑ j ∈ gates.filter (fun j => j + 1 < C.size), (reads ((n + m) + j) - 1))
  q ≤ 33 * defect + 4 := by
  classical
  intro n m G C dr dc rep
  dsimp only
  intro sh back pos last live
  obtain ⟨pure,chains,hpure,hchains,_,cover,pureTree,chainTree⟩ := finish69 (n+m) C sh back pos last live
  have raw (S : Finset Nat) (hs : S ∈ pure++chains) (w : Nat) (hw : w∈S) : w<n+m := by
    have h : w∈once69 (n+m) C := cover ▸ Finset.mem_biUnion.mpr ⟨S,List.mem_toFinset.mpr hs,hw⟩
    exact Finset.mem_range.mp (Finset.mem_filter.mp h).1
  have pcap := card_regions pure 4 (fun S hs =>
    (region_cap dr dc back rep (raw S (List.mem_append_left _ hs)) (pureTree S hs).2).1 rfl)
  have ccap := card_regions chains 6 (fun S hs => by
    obtain ⟨b,hb⟩ := (chainTree S hs).2
    exact (region_cap dr dc back rep (raw S (List.mem_append_right _ hs)) hb).2 b rfl)
  have e : once69 (n+m) C = pure.toFinset.biUnion id ∪ chains.toFinset.biUnion id := by
    rw [← cover]
    ext w
    simp only [Finset.mem_biUnion, List.mem_toFinset, List.mem_append, Finset.mem_union, id_eq]
    aesop
  have once := (Finset.card_union_le (pure.toFinset.biUnion id) (chains.toFinset.biUnion id))
  rw [← e] at once
  obtain ⟨hq,hex,hen⟩ := budget (n+m) C sh back
  change ((Finset.range (n+m)).filter (fun w => 0<reads69 C w)).card ≤
    33 * ((neg69 C).card + (∑ w ∈ Finset.range (n+m), (reads69 C w-1)) +
      (∑ j ∈ (gates69 C).filter (fun j => j+1<C.size), (reads69 C (n+m+j)-1))) + 4
  omega

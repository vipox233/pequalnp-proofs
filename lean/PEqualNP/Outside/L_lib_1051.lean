import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1051

def pairOf {n : ℕ} (p : Fin (2 * n)) : Fin n :=
  ⟨min p.val (2 * n - 1 - p.val), by omega⟩

noncomputable def splitPairs {n : ℕ} (o : Fin (2 * n) → Fin (2 * n)) (i : Fin (2 * n)) : Finset (Fin n) :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  Finset.univ.filter (fun j : Fin n =>
    (∃ a : Fin (2 * n), a.val < i.val ∧ pairOf (o a) = j) ∧
    (∃ b : Fin (2 * n), i.val ≤ b.val ∧ pairOf (o b) = j))

def mcolFn {n : ℕ} (p : Fin (2 * n)) (j : Fin n) : ZMod 2 :=
  if min p.val (2 * n - 1 - p.val) = j.val then (1 : ZMod 2) else 0

private lemma mcolFn_eq_single {n : ℕ} (p : Fin (2 * n)) :
    mcolFn p = Pi.single (pairOf p) (1 : ZMod 2) := by
  ext j
  simp only [mcolFn, pairOf, Pi.single_apply]
  by_cases h : j = ⟨min p.val (2 * n - 1 - p.val), by omega⟩
  · subst h; simp
  · have hne : min p.val (2 * n - 1 - p.val) ≠ j.val := by
      intro heq; apply h; exact Fin.ext heq.symm
    simp [h, hne]

private lemma mem_span_single_iff {n : ℕ} (S : Finset (Fin n)) (v : Fin n → ZMod 2) :
    v ∈ Submodule.span (ZMod 2) ((S : Set (Fin n)).image (fun j => Pi.single j (1 : ZMod 2))) ↔
      ∀ j : Fin n, j ∉ S → v j = 0 := by
  constructor
  · intro hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k, hk, rfl⟩ j hj
      have hjk : j ≠ k := fun h => hj (h ▸ hk)
      simp [Pi.single_eq_of_ne hjk]
    · intro j _; rfl
    · intro x y _ _ hx hy j hj
      simp [hx j hj, hy j hj]
    · intro c x _ hx j hj
      simp [hx j hj]
  · intro hv
    have hv_eq : v = ∑ j ∈ S, v j • Pi.single j (1 : ZMod 2) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases hj : j ∈ S
      · rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hbj; simp [Ne.symm hbj]
        · intro h; exact absurd hj h
      · rw [hv j hj]
        symm
        apply Finset.sum_eq_zero
        intro b hb
        have hjb : j ≠ b := fun h => hj (h ▸ hb)
        simp [hjb]
    rw [hv_eq]
    apply Submodule.sum_mem
    intro j hj
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

private lemma span_single_inf {n : ℕ} (S₁ S₂ : Finset (Fin n)) :
    (Submodule.span (ZMod 2) ((S₁ : Set (Fin n)).image (fun j => Pi.single j (1 : ZMod 2))) ⊓
      Submodule.span (ZMod 2) ((S₂ : Set (Fin n)).image (fun j => Pi.single j (1 : ZMod 2))) :
        Submodule (ZMod 2) (Fin n → ZMod 2)) =
    Submodule.span (ZMod 2) (((S₁ ∩ S₂ : Finset (Fin n)) : Set (Fin n)).image (fun j => Pi.single j (1 : ZMod 2))) := by
  ext v
  simp only [Submodule.mem_inf, mem_span_single_iff, Finset.mem_inter, not_and_or]
  constructor
  · intro ⟨h1, h2⟩ j hj
    rcases hj with hj1 | hj2
    · exact h1 j hj1
    · exact h2 j hj2
  · intro h
    exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩

private lemma finrank_span_single {n : ℕ} (S : Finset (Fin n)) :
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) ((S : Set (Fin n)).image (fun j => Pi.single j (1 : ZMod 2)))) = S.card := by
  have hli : LinearIndependent (ZMod 2) (fun j : ↥S => Pi.single (M := fun _ : Fin n => ZMod 2) j.1 (1 : ZMod 2)) := by
    have hfull : LinearIndependent (ZMod 2) (fun j : Fin n => Pi.single (M := fun _ : Fin n => ZMod 2) j (1 : ZMod 2)) := by
      have hfun : (⇑(Pi.basisFun (ZMod 2) (Fin n))) =
          (fun j : Fin n => Pi.single (M := fun _ : Fin n => ZMod 2) j (1 : ZMod 2)) := by
        funext j
        exact Pi.basisFun_apply (ZMod 2) (Fin n) j
      rw [← hfun]
      exact (Pi.basisFun (ZMod 2) (Fin n)).linearIndependent
    exact hfull.comp (fun j : ↥S => j.1) Subtype.val_injective
  have hrange : Set.range (fun j : ↥S => Pi.single (M := fun _ : Fin n => ZMod 2) j.1 (1 : ZMod 2)) =
      (S : Set (Fin n)).image (fun j => Pi.single j (1 : ZMod 2)) := by
    ext v; simp
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_coe]

private lemma mem_take_ofFn_iff {n : ℕ} (o : Fin (2 * n) → Fin (2 * n)) (i : Fin (2 * n)) (p : Fin (2 * n)) :
    p ∈ (List.ofFn o).take i.val ↔ ∃ a : Fin (2 * n), a.val < i.val ∧ o a = p := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hmlt : m < i.val := by
      rw [List.length_take, List.length_ofFn] at hm; omega
    have hmlt2 : m < 2 * n := by omega
    refine ⟨⟨m, hmlt2⟩, hmlt, ?_⟩
    simp [List.getElem_take, List.getElem_ofFn]
  · rintro ⟨a, ha, rfl⟩
    have hlt : a.val < ((List.ofFn o).take i.val).length := by
      rw [List.length_take, List.length_ofFn]; omega
    exact ⟨a.val, hlt, by simp [List.getElem_take, List.getElem_ofFn]⟩

private lemma mem_drop_ofFn_iff {n : ℕ} (o : Fin (2 * n) → Fin (2 * n)) (i : Fin (2 * n)) (p : Fin (2 * n)) :
    p ∈ (List.ofFn o).drop i.val ↔ ∃ b : Fin (2 * n), i.val ≤ b.val ∧ o b = p := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hmlt : i.val + m < 2 * n := by
      rw [List.length_drop, List.length_ofFn] at hm; omega
    refine ⟨⟨i.val + m, hmlt⟩, by dsimp; omega, ?_⟩
    simp [List.getElem_drop, List.getElem_ofFn]
  · rintro ⟨b, hb, rfl⟩
    have hlt : b.val - i.val < ((List.ofFn o).drop i.val).length := by
      rw [List.length_drop, List.length_ofFn]; omega
    refine ⟨b.val - i.val, hlt, ?_⟩
    simp only [List.getElem_drop, List.getElem_ofFn]
    congr 1; apply Fin.ext; dsimp; omega

lemma charge_eq_splitPairs {n : ℕ} (o : Fin (2 * n) → Fin (2 * n)) (i : Fin (2 * n)) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let L := (List.ofFn o).take i.val
    let R := (List.ofFn o).drop i.val
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (↑((L.map mcolFn).toFinset) : Set (Fin n → ZMod 2)) ⊓
       Submodule.span (ZMod 2) (↑((R.map mcolFn).toFinset) : Set (Fin n → ZMod 2)) :
        Submodule (ZMod 2) (Fin n → ZMod 2)) =
    (splitPairs o i).card := by
  dsimp only
  let S₁ : Finset (Fin n) :=
    @Finset.filter (Fin n) (fun j => ∃ a : Fin (2 * n), a.val < i.val ∧ pairOf (o a) = j)
      (fun _ => Classical.propDecidable _) Finset.univ
  let S₂ : Finset (Fin n) :=
    @Finset.filter (Fin n) (fun j => ∃ b : Fin (2 * n), i.val ≤ b.val ∧ pairOf (o b) = j)
      (fun _ => Classical.propDecidable _) Finset.univ
  have h1 : (↑(@List.toFinset (Fin n → ZMod 2) (fun a b => Classical.propDecidable (a = b))
        (((List.ofFn o).take i.val).map mcolFn)) : Set (Fin n → ZMod 2)) =
      (S₁ : Set (Fin n)).image (fun j => Pi.single j (1 : ZMod 2)) := by
    ext v
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map, Set.mem_image, S₁,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [mem_take_ofFn_iff] at hp
      rcases hp with ⟨a, ha, rfl⟩
      exact ⟨pairOf (o a), ⟨a, ha, rfl⟩, (mcolFn_eq_single (o a)).symm⟩
    · rintro ⟨j, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨o a, (mem_take_ofFn_iff o i (o a)).mpr ⟨a, ha, rfl⟩, mcolFn_eq_single (o a)⟩
  have h2 : (↑(@List.toFinset (Fin n → ZMod 2) (fun a b => Classical.propDecidable (a = b))
        (((List.ofFn o).drop i.val).map mcolFn)) : Set (Fin n → ZMod 2)) =
      (S₂ : Set (Fin n)).image (fun j => Pi.single j (1 : ZMod 2)) := by
    ext v
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map, Set.mem_image, S₂,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [mem_drop_ofFn_iff] at hp
      rcases hp with ⟨b, hb, rfl⟩
      exact ⟨pairOf (o b), ⟨b, hb, rfl⟩, (mcolFn_eq_single (o b)).symm⟩
    · rintro ⟨j, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨o b, (mem_drop_ofFn_iff o i (o b)).mpr ⟨b, hb, rfl⟩, mcolFn_eq_single (o b)⟩
  have hinter : S₁ ∩ S₂ = splitPairs o i := by
    ext j
    simp [S₁, S₂, splitPairs]
  rw [h1, h2, span_single_inf, hinter, finrank_span_single]

lemma one_le_peak_bijective {n : ℕ} (hn : 0 < n) (o : Fin (2 * n) → Fin (2 * n))
    (ho : Function.Bijective o) :
    1 ≤ (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs o i).card) := by
  let i1 : Fin (2 * n) := ⟨1, by omega⟩
  have hle : (splitPairs o i1).card ≤
      (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs o i).card) :=
    Finset.le_sup (f := fun i => (splitPairs o i).card) (Finset.mem_univ i1)
  suffices hpos : 1 ≤ (splitPairs o i1).card by omega
  let a0 : Fin (2 * n) := ⟨0, by omega⟩
  let p0 : Fin (2 * n) := o a0
  obtain ⟨b, hb⟩ := ho.2 (Fin.rev p0)
  have hbne : b ≠ a0 := by
    intro heq
    rw [heq] at hb
    have hval := congrArg Fin.val hb
    simp only [Fin.val_rev, p0] at hval
    omega
  have hbge : 1 ≤ b.val := by
    have : b.val ≠ 0 := fun h => hbne (Fin.ext h)
    omega
  have hmem : pairOf p0 ∈ splitPairs o i1 := by
    simp only [splitPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨a0, by simp [a0, i1], rfl⟩, ⟨b, hbge, ?_⟩⟩
    rw [hb]
    apply Fin.ext
    simp only [pairOf, Fin.val_rev]
    omega
  exact Finset.one_le_card.mpr ⟨pairOf p0, hmem⟩

def foldedFn {n : ℕ} (i : Fin (2 * n)) : Fin (2 * n) :=
  let v : Fin (2 * n) := ⟨i.val / 2, Nat.lt_of_le_of_lt (Nat.div_le_self i.val 2) i.isLt⟩
  if i.val % 2 = 0 then Fin.rev v else v

noncomputable def arcFn {n : ℕ} (r : ℕ) (p : Fin (2 * n)) : Finset (Fin (2 * n)) :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  (Finset.univ : Finset (Fin (2 * n))).filter (fun z =>
    ∃ a : Fin (5 * r - 2), (p.val + a.val) % (2 * n) = z.val)

noncomputable def poolFn {n : ℕ} (r : ℕ) (ps : List (Fin (2 * n))) : Finset (Fin (2 * n)) :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  ps.toFinset.biUnion (arcFn r)

private lemma foldedFn_val_even {n : ℕ} (i : Fin (2 * n)) (he : i.val % 2 = 0) :
    (foldedFn i).val = 2 * n - 1 - i.val / 2 := by
  simp [foldedFn, he, Fin.val_rev]
  omega

private lemma foldedFn_val_odd {n : ℕ} (i : Fin (2 * n)) (ho : i.val % 2 ≠ 0) :
    (foldedFn i).val = i.val / 2 := by
  simp [foldedFn, ho]

private def foldedInv {n : ℕ} (p : Fin (2 * n)) : Fin (2 * n) :=
  if h : p.val < n then ⟨2 * p.val + 1, by omega⟩
  else ⟨2 * (2 * n - 1 - p.val), by omega⟩

private lemma foldedInv_leftInverse {n : ℕ} : Function.LeftInverse (@foldedInv n) (@foldedFn n) := by
  intro i
  ext
  by_cases he : i.val % 2 = 0
  · have hval := foldedFn_val_even i he
    have hge : ¬ (foldedFn i).val < n := by omega
    simp only [foldedInv, hge, ↓reduceDIte]
    omega
  · have hval := foldedFn_val_odd i he
    have hlt : (foldedFn i).val < n := by omega
    simp only [foldedInv, hlt, ↓reduceDIte]
    omega

private lemma foldedInv_rightInverse {n : ℕ} : Function.RightInverse (@foldedInv n) (@foldedFn n) := by
  intro p
  ext
  by_cases hlt : p.val < n
  · have hg : (foldedInv p).val = 2 * p.val + 1 := by simp [foldedInv, hlt]
    have ho : (foldedInv p).val % 2 ≠ 0 := by omega
    rw [foldedFn_val_odd _ ho, hg]
    omega
  · have hg : (foldedInv p).val = 2 * (2 * n - 1 - p.val) := by simp [foldedInv, hlt]
    have he : (foldedInv p).val % 2 = 0 := by omega
    rw [foldedFn_val_even _ he, hg]
    omega

lemma foldedFn_bijective (n : ℕ) : Function.Bijective (@foldedFn n) :=
  Function.bijective_iff_has_inverse.mpr ⟨@foldedInv n, foldedInv_leftInverse, foldedInv_rightInverse⟩

private lemma mem_take_ofFn_folded_iff {n : ℕ} (u : ℕ) (hu : u ≤ 2 * n) (j : Fin (2 * n)) :
    j ∈ (List.ofFn (@foldedFn n)).take u ↔
      j.val < u / 2 ∨ 2 * n - (u + 1) / 2 ≤ j.val := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, hkj⟩
    have hk_lt_u : k < u := by
      simp only [List.length_take, List.length_ofFn] at hk
      omega
    have hk_lt_2n : k < 2 * n := by omega
    have hfk : foldedFn ⟨k, hk_lt_2n⟩ = j := by
      simpa [List.getElem_take, List.getElem_ofFn] using hkj
    by_cases he : k % 2 = 0
    · have hval : j.val = 2 * n - 1 - k / 2 := by
        rw [← hfk]
        exact foldedFn_val_even ⟨k, hk_lt_2n⟩ he
      right
      omega
    · have hval : j.val = k / 2 := by
        rw [← hfk]
        exact foldedFn_val_odd ⟨k, hk_lt_2n⟩ he
      left
      omega
  · intro hj
    refine ⟨(foldedInv j).val, ?_, ?_⟩
    · simp only [List.length_take, List.length_ofFn]
      by_cases hlt : j.val < n
      · have hg : (foldedInv j).val = 2 * j.val + 1 := by simp [foldedInv, hlt]
        omega
      · have hg : (foldedInv j).val = 2 * (2 * n - 1 - j.val) := by simp [foldedInv, hlt]
        omega
    · simp only [List.getElem_take, List.getElem_ofFn, Fin.eta]
      exact foldedInv_rightInverse j

private lemma mem_drop_ofFn_folded_iff {n : ℕ} (u : ℕ) (hu : u ≤ 2 * n) (j : Fin (2 * n)) :
    j ∈ (List.ofFn (@foldedFn n)).drop u ↔
      u / 2 ≤ j.val ∧ j.val < 2 * n - (u + 1) / 2 := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, hkj⟩
    have hk_lt : u + k < 2 * n := by
      simp only [List.length_drop, List.length_ofFn] at hk
      omega
    have hfk : foldedFn ⟨u + k, hk_lt⟩ = j := by
      simpa [List.getElem_drop, List.getElem_ofFn] using hkj
    by_cases he : (u + k) % 2 = 0
    · have hval : j.val = 2 * n - 1 - (u + k) / 2 := by
        rw [← hfk]
        exact foldedFn_val_even ⟨u + k, hk_lt⟩ he
      omega
    · have hval : j.val = (u + k) / 2 := by
        rw [← hfk]
        exact foldedFn_val_odd ⟨u + k, hk_lt⟩ he
      omega
  · rintro ⟨h1, h2⟩
    have hinv_ge : u ≤ (foldedInv j).val := by
      by_cases hlt : j.val < n
      · have hg : (foldedInv j).val = 2 * j.val + 1 := by simp [foldedInv, hlt]
        omega
      · have hg : (foldedInv j).val = 2 * (2 * n - 1 - j.val) := by simp [foldedInv, hlt]
        omega
    refine ⟨(foldedInv j).val - u, ?_, ?_⟩
    · simp only [List.length_drop, List.length_ofFn]
      have hlt := (foldedInv j).isLt
      omega
    · simp only [List.getElem_drop, List.getElem_ofFn]
      have heq : (⟨u + ((foldedInv j).val - u), by omega⟩ : Fin (2 * n)) = foldedInv j := by
        ext
        dsimp only
        omega
      rw [heq]
      exact foldedInv_rightInverse j

lemma folded_order (n : ℕ) (hn : 0 < n) :
    Function.Bijective (@foldedFn n) ∧
    ∀ u : Fin (2 * n + 1),
      letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      let S := ((List.ofFn (@foldedFn n)).take u.val).toFinset
      ((Finset.univ : Finset (Fin (2 * n))).filter (fun j =>
        j ∈ S ∧ ∀ z ∈ S, (z.val + 1) % (2 * n) ≠ j.val)).card ≤ 1 := by
  refine ⟨foldedFn_bijective n, ?_⟩
  intro u
  dsimp only
  have hu : u.val ≤ 2 * n := by omega
  have hmem : ∀ j : Fin (2 * n),
      j ∈ ((List.ofFn (@foldedFn n)).take u.val) ↔
        j.val < u.val / 2 ∨ 2 * n - (u.val + 1) / 2 ≤ j.val :=
    mem_take_ofFn_folded_iff u.val hu
  refine Finset.card_le_one.mpr ?_
  intro j1 hj1 j2 hj2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset] at hj1 hj2
  rcases hj1 with ⟨hj1S, hno1⟩
  rcases hj2 with ⟨hj2S, hno2⟩
  by_cases hu0 : u.val = 0
  · rw [hmem, hu0] at hj1S
    omega
  · by_cases hu2n : u.val = 2 * n
    · exfalso
      let z : Fin (2 * n) := ⟨(j1.val + 2 * n - 1) % (2 * n), Nat.mod_lt _ (by omega)⟩
      have hzS : z ∈ (List.ofFn (@foldedFn n)).take u.val := by
        rw [hmem, hu2n]
        omega
      have hstep : (z.val + 1) % (2 * n) = j1.val := by
        have hjlt := j1.isLt
        by_cases hj0 : j1.val = 0
        · have hzval : z.val = 2 * n - 1 := by
            change (j1.val + 2 * n - 1) % (2 * n) = 2 * n - 1
            rw [hj0]
            simp only [zero_add]
            exact Nat.mod_eq_of_lt (by omega)
          rw [hzval, hj0]
          have : 2 * n - 1 + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
        · have hzval : z.val = j1.val - 1 := by
            change (j1.val + 2 * n - 1) % (2 * n) = j1.val - 1
            have : j1.val + 2 * n - 1 = (j1.val - 1) + 2 * n := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hzval]
          have : j1.val - 1 + 1 = j1.val := by omega
          rw [this, Nat.mod_eq_of_lt hjlt]
      exact hno1 z hzS hstep
    · have huniq : ∀ j : Fin (2 * n),
          j ∈ (List.ofFn (@foldedFn n)).take u.val →
          (∀ z ∈ (List.ofFn (@foldedFn n)).take u.val, (z.val + 1) % (2 * n) ≠ j.val) →
          j.val = 2 * n - (u.val + 1) / 2 := by
        intro j hjS hno
        by_contra hval_ne
        by_cases hj0 : j.val = 0
        · let z : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
          have hzS : z ∈ (List.ofFn (@foldedFn n)).take u.val := by
            rw [hmem]
            right
            change 2 * n - (u.val + 1) / 2 ≤ 2 * n - 1
            omega
          have hstep : (z.val + 1) % (2 * n) = j.val := by
            rw [hj0]
            have : z.val + 1 = 2 * n := by
              change 2 * n - 1 + 1 = 2 * n
              omega
            rw [this, Nat.mod_self]
          exact hno z hzS hstep
        · let z : Fin (2 * n) := ⟨j.val - 1, by omega⟩
          have hzS : z ∈ (List.ofFn (@foldedFn n)).take u.val := by
            rw [hmem] at hjS ⊢
            change j.val - 1 < u.val / 2 ∨ 2 * n - (u.val + 1) / 2 ≤ j.val - 1
            omega
          have hstep : (z.val + 1) % (2 * n) = j.val := by
            have : z.val + 1 = j.val := by
              change j.val - 1 + 1 = j.val
              omega
            rw [this, Nat.mod_eq_of_lt j.isLt]
          exact hno z hzS hstep
      ext
      rw [huniq j1 hj1S hno1, huniq j2 hj2S hno2]

private lemma pairOf_foldedFn_val {n : ℕ} (a : Fin (2 * n)) :
    (pairOf (foldedFn a)).val = a.val / 2 := by
  by_cases he : a.val % 2 = 0
  · have hval := foldedFn_val_even a he
    simp only [pairOf, hval]
    omega
  · have hval := foldedFn_val_odd a he
    simp only [pairOf, hval]
    omega

lemma folded_splitPairs_card_le (n : ℕ) (i : Fin (2 * n)) :
    (splitPairs (@foldedFn n) i).card ≤ 1 := by
  let j0 : Fin n := ⟨i.val / 2, by omega⟩
  have hsub : splitPairs (@foldedFn n) i ⊆ {j0} := by
    intro j hj
    simp only [splitPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rcases hj with ⟨⟨a, ha_lt, ha_eq⟩, ⟨b, hb_le, hb_eq⟩⟩
    have ha_val : a.val / 2 = j.val := by
      rw [← pairOf_foldedFn_val a, ha_eq]
    have hb_val : b.val / 2 = j.val := by
      rw [← pairOf_foldedFn_val b, hb_eq]
    rw [Finset.mem_singleton]
    ext
    change j.val = i.val / 2
    omega
  exact (Finset.card_le_card hsub).trans (by simp)

lemma folded_strip_card_le (n r : ℕ) (hn : 0 < n) (hr : 4 ≤ r) (i : Fin (2 * n)) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let L := (List.ofFn (@foldedFn n)).take i.val
    let R := (List.ofFn (@foldedFn n)).drop i.val
    ((poolFn r L ∩ poolFn r R) ∪ arcFn r (foldedFn i)).card ≤ min (2 * n) (2 * (5 * r - 3) + 1) := by
  dsimp only
  set L := (List.ofFn (@foldedFn n)).take i.val
  set R := (List.ofFn (@foldedFn n)).drop i.val
  set D := 5 * r - 3
  refine le_min ((Finset.card_le_univ _).trans (by simp [Fintype.card_fin])) ?_
  by_cases hsmall : 2 * n ≤ 2 * D + 1
  · exact ((Finset.card_le_univ _).trans (by simp [Fintype.card_fin])).trans hsmall
  have hbig : 2 * D + 1 < 2 * n := by omega
  by_cases hi0 : i.val = 0
  · have hL_nil : L = [] := by
      simp [L, hi0]
    have hpoolL : poolFn r L = ∅ := by
      simp [poolFn, hL_nil]
    let f : ℕ → Fin (2 * n) := fun a => ⟨((foldedFn i).val + a) % (2 * n), Nat.mod_lt _ (by omega)⟩
    refine (Finset.card_le_card (t := (Finset.range (5 * r - 2)).image f) ?_).trans ?_
    · intro z hz
      simp only [Finset.mem_union, Finset.mem_inter] at hz
      rcases hz with ⟨hzL, _⟩ | hzArc
      · rw [hpoolL] at hzL
        exact absurd hzL (Finset.notMem_empty z)
      · simp only [arcFn, Finset.mem_filter, Finset.mem_univ, true_and] at hzArc
        rcases hzArc with ⟨a, ha⟩
        rw [Finset.mem_image]
        refine ⟨a.val, Finset.mem_range.mpr a.isLt, ?_⟩
        ext
        exact ha
    · calc ((Finset.range (5 * r - 2)).image f).card
          ≤ (Finset.range (5 * r - 2)).card := Finset.card_image_le
        _ = 5 * r - 2 := Finset.card_range _
        _ ≤ 2 * D + 1 := by omega
  · set a0 := i.val / 2
    set b0 := 2 * n - (i.val + 1) / 2
    have hi_le : i.val ≤ 2 * n := by omega
    have ha0_lt_n : a0 < n := by omega
    have hb0_ge_n : n ≤ b0 := by omega
    have hb0_lt_2n : b0 < 2 * n := by omega
    let f1 : ℕ → Fin (2 * n) := fun b => ⟨(a0 + b) % (2 * n), Nat.mod_lt _ (by omega)⟩
    let f2 : ℕ → Fin (2 * n) := fun b => ⟨(b0 + b) % (2 * n), Nat.mod_lt _ (by omega)⟩
    let S1 : Finset (Fin (2 * n)) := (Finset.range D).image f1
    let S2 : Finset (Fin (2 * n)) := (Finset.range D).image f2
    let e : Fin (2 * n) :=
      if i.val % 2 = 0 then ⟨b0 - 1, by omega⟩
      else ⟨(a0 + D) % (2 * n), Nat.mod_lt _ (by omega)⟩
    refine (Finset.card_le_card (t := (S1 ∪ S2) ∪ {e}) ?_).trans ?_
    · intro z hz
      simp only [Finset.mem_union, Finset.mem_inter] at hz
      rcases hz with ⟨hzL, hzR⟩ | hzArc
      · simp only [poolFn, Finset.mem_biUnion, List.mem_toFinset] at hzL hzR
        rcases hzL with ⟨p, hpL, hzp⟩
        rcases hzR with ⟨q, hqR, hzq⟩
        have hp_lt : p.val < 2 * n := p.isLt
        have hq_lt : q.val < 2 * n := q.isLt
        simp only [arcFn, Finset.mem_filter, Finset.mem_univ, true_and] at hzp hzq
        rcases hzp with ⟨d1, hd1⟩
        rcases hzq with ⟨d2, hd2⟩
        have hp_spec : p.val < a0 ∨ b0 ≤ p.val := (mem_take_ofFn_folded_iff i.val hi_le p).mp hpL
        have hq_spec : a0 ≤ q.val ∧ q.val < b0 := (mem_drop_ofFn_folded_iff i.val hi_le q).mp hqR
        have hd1_le : d1.val ≤ D := by omega
        have hd2_le : d2.val ≤ D := by omega
        by_cases hz_in_R : a0 ≤ z.val ∧ z.val < b0
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          rw [Finset.mem_image]
          refine ⟨z.val - a0, Finset.mem_range.mpr ?_, ?_⟩
          · rcases hp_spec with hp1 | hp2
            · have hno_wrap : p.val + d1.val < 2 * n := by omega
              rw [Nat.mod_eq_of_lt hno_wrap] at hd1
              omega
            · have hwrap : 2 * n ≤ p.val + d1.val := by
                by_contra hlt
                have hlt' : p.val + d1.val < 2 * n := by omega
                rw [Nat.mod_eq_of_lt hlt'] at hd1
                omega
              have hlt4n : p.val + d1.val - 2 * n < 2 * n := by omega
              have hmod : (p.val + d1.val) % (2 * n) = p.val + d1.val - 2 * n := by
                have heq : p.val + d1.val = (p.val + d1.val - 2 * n) + 2 * n := by omega
                conv_lhs => rw [heq]
                rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt4n]
              rw [hmod] at hd1
              omega
          · ext
            change (a0 + (z.val - a0)) % (2 * n) = z.val
            have : a0 + (z.val - a0) = z.val := by omega
            rw [this, Nat.mod_eq_of_lt z.isLt]
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          rw [Finset.mem_image]
          by_cases hwrap : q.val + d2.val < 2 * n
          · rw [Nat.mod_eq_of_lt hwrap] at hd2
            have hzb0 : b0 ≤ z.val := by omega
            refine ⟨z.val - b0, Finset.mem_range.mpr (by omega), ?_⟩
            ext
            change (b0 + (z.val - b0)) % (2 * n) = z.val
            have : b0 + (z.val - b0) = z.val := by omega
            rw [this, Nat.mod_eq_of_lt z.isLt]
          · have hlt4n : q.val + d2.val - 2 * n < 2 * n := by omega
            have hmod : (q.val + d2.val) % (2 * n) = q.val + d2.val - 2 * n := by
              have heq : q.val + d2.val = (q.val + d2.val - 2 * n) + 2 * n := by omega
              conv_lhs => rw [heq]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt4n]
            rw [hmod] at hd2
            refine ⟨z.val + 2 * n - b0, Finset.mem_range.mpr (by omega), ?_⟩
            ext
            change (b0 + (z.val + 2 * n - b0)) % (2 * n) = z.val
            have : b0 + (z.val + 2 * n - b0) = z.val + 2 * n := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt z.isLt]
      · simp only [arcFn, Finset.mem_filter, Finset.mem_univ, true_and] at hzArc
        rcases hzArc with ⟨a, ha⟩
        by_cases he : i.val % 2 = 0
        · have hfi : (foldedFn i).val = b0 - 1 := by
            rw [foldedFn_val_even i he]
            omega
          rw [hfi] at ha
          by_cases ha0 : a.val = 0
          · apply Finset.mem_union_right
            rw [Finset.mem_singleton]
            ext
            simp only [e, he, ↓reduceIte]
            rw [← ha, ha0, add_zero, Nat.mod_eq_of_lt (by omega)]
          · apply Finset.mem_union_left
            apply Finset.mem_union_right
            rw [Finset.mem_image]
            refine ⟨a.val - 1, Finset.mem_range.mpr (by omega), ?_⟩
            ext
            change (b0 + (a.val - 1)) % (2 * n) = z.val
            have : b0 + (a.val - 1) = b0 - 1 + a.val := by omega
            rw [this, ha]
        · have hfi : (foldedFn i).val = a0 := foldedFn_val_odd i he
          rw [hfi] at ha
          by_cases haD : a.val < D
          · apply Finset.mem_union_left
            apply Finset.mem_union_left
            rw [Finset.mem_image]
            refine ⟨a.val, Finset.mem_range.mpr haD, ?_⟩
            ext
            exact ha
          · have ha_eq : a.val = D := by omega
            apply Finset.mem_union_right
            rw [Finset.mem_singleton]
            ext
            simp only [e, he, ↓reduceIte]
            rw [← ha, ha_eq]
    · calc ((S1 ∪ S2) ∪ {e}).card
          ≤ (S1 ∪ S2).card + ({e} : Finset (Fin (2 * n))).card := Finset.card_union_le _ _
        _ ≤ (S1.card + S2.card) + 1 := by
            have h1 := Finset.card_union_le S1 S2
            simp only [Finset.card_singleton]
            omega
        _ ≤ (D + D) + 1 := by
            have hS1 : S1.card ≤ D := Finset.card_image_le.trans (by simp)
            have hS2 : S2.card ≤ D := Finset.card_image_le.trans (by simp)
            omega
        _ = 2 * D + 1 := by omega

def walkFn {n : ℕ} (hn : 0 < n) (c : Fin (2 * n)) (rev : Bool) (i : Fin (2 * n)) : Fin (2 * n) :=
  ⟨(c.val + (if rev then 2 * n - 1 - i.val else i.val)) % (2 * n),
    Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 1) hn)⟩

private lemma walkFn_true_eq {n : ℕ} (hn : 0 < n) (c : Fin (2 * n)) :
    walkFn hn c true = walkFn hn c false ∘ Fin.rev := by
  funext i
  ext
  simp only [walkFn, Function.comp_apply, Fin.val_rev, ↓reduceIte, Bool.false_eq_true]
  congr 1
  omega

private lemma splitPairs_zero {n : ℕ} (o : Fin (2 * n) → Fin (2 * n)) (i : Fin (2 * n))
    (hi : i.val = 0) : splitPairs o i = ∅ := by
  ext j
  simp [splitPairs, hi]

private lemma splitPairs_comp_rev {n : ℕ} (o : Fin (2 * n) → Fin (2 * n)) (i : Fin (2 * n))
    (hi : 0 < i.val) :
    splitPairs (o ∘ Fin.rev) i = splitPairs o ⟨2 * n - i.val, by omega⟩ := by
  ext j
  simp only [splitPairs, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨⟨a, ha, hja⟩, ⟨b, hb, hjb⟩⟩
    refine ⟨⟨Fin.rev b, ?_, ?_⟩, ⟨Fin.rev a, ?_, ?_⟩⟩
    · simp only [Fin.val_rev]; omega
    · simpa using hjb
    · simp only [Fin.val_rev]; omega
    · simpa using hja
  · rintro ⟨⟨a, ha, hja⟩, ⟨b, hb, hjb⟩⟩
    refine ⟨⟨Fin.rev b, ?_, ?_⟩, ⟨Fin.rev a, ?_, ?_⟩⟩
    · simp only [Fin.val_rev]; omega
    · simpa using hjb
    · simp only [Fin.val_rev]; omega
    · simpa using hja

private lemma sup_splitPairs_comp_rev_le {n : ℕ} (o : Fin (2 * n) → Fin (2 * n)) :
    (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs (o ∘ Fin.rev) i).card) ≤
    (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs o i).card) := by
  refine Finset.sup_le fun i _ => ?_
  by_cases hi : i.val = 0
  · rw [splitPairs_zero _ _ hi]
    simp
  · have hi' : 0 < i.val := Nat.pos_of_ne_zero hi
    rw [splitPairs_comp_rev o i hi']
    exact Finset.le_sup (f := fun k => (splitPairs o k).card)
      (Finset.mem_univ (⟨2 * n - i.val, by omega⟩ : Fin (2 * n)))

private lemma sup_splitPairs_comp_rev {n : ℕ} (o : Fin (2 * n) → Fin (2 * n)) :
    (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs (o ∘ Fin.rev) i).card) =
    (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs o i).card) := by
  apply le_antisymm (sup_splitPairs_comp_rev_le o)
  have h : (o ∘ Fin.rev) ∘ Fin.rev = o := by
    funext x
    simp
  conv_lhs => rw [← h]
  exact sup_splitPairs_comp_rev_le (o ∘ Fin.rev)

private lemma pairOf_walkFn_shift {n : ℕ} (hn : 0 < n) (c : Fin (2 * n)) (hc : n ≤ c.val)
    (a : Fin (2 * n)) :
    pairOf (walkFn hn c false a) =
      Fin.rev (pairOf (walkFn hn ⟨c.val - n, by omega⟩ false a)) := by
  ext
  simp only [pairOf, walkFn, Bool.false_eq_true, ↓reduceIte, Fin.val_rev]
  have ha : a.val < 2 * n := a.isLt
  have hc2 : c.val < 2 * n := c.isLt
  have h1 : (c.val + a.val) % (2 * n) =
      if c.val + a.val < 2 * n then c.val + a.val else c.val + a.val - 2 * n := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
  have h2 : (c.val - n + a.val) % (2 * n) =
      if c.val - n + a.val < 2 * n then c.val - n + a.val else c.val - n + a.val - 2 * n := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  split_ifs <;> omega

private lemma card_splitPairs_shift {n : ℕ} (hn : 0 < n) (c : Fin (2 * n)) (hc : n ≤ c.val)
    (i : Fin (2 * n)) :
    (splitPairs (walkFn hn c false) i).card =
      (splitPairs (walkFn hn ⟨c.val - n, by omega⟩ false) i).card := by
  refine Finset.card_bij (fun j _ => Fin.rev j) ?_ ?_ ?_
  · intro j hj
    simp only [splitPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rcases hj with ⟨⟨a, ha, hja⟩, ⟨b, hb, hjb⟩⟩
    refine ⟨⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩⟩
    · rw [← hja, pairOf_walkFn_shift hn c hc a, Fin.rev_rev]
    · rw [← hjb, pairOf_walkFn_shift hn c hc b, Fin.rev_rev]
  · intro j₁ _ j₂ _ h
    exact Fin.rev_injective h
  · intro j hj
    refine ⟨Fin.rev j, ?_, Fin.rev_rev j⟩
    simp only [splitPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rcases hj with ⟨⟨a, ha, hja⟩, ⟨b, hb, hjb⟩⟩
    refine ⟨⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩⟩
    · rw [pairOf_walkFn_shift hn c hc a, hja]
    · rw [pairOf_walkFn_shift hn c hc b, hjb]

private lemma card_filter_Ico_le {n a b : ℕ} :
    (Finset.univ.filter (fun j : Fin n => a ≤ j.val ∧ j.val < b)).card ≤ b - a := by
  have hcard : (Finset.Ico a b).card = b - a := Nat.card_Ico a b
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun j : Fin n => j.val) ?_ ?_
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_coe, Finset.mem_Ico]
    exact hj
  · intro j₁ _ j₂ _ h
    exact Fin.ext h

private lemma card_filter_Ico_eq {n a b : ℕ} (hb : b ≤ n) :
    (Finset.univ.filter (fun j : Fin n => a ≤ j.val ∧ j.val < b)).card = b - a := by
  have hcard : (Finset.Ico a b).card = b - a := Nat.card_Ico a b
  rw [← hcard]
  refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_Ico.mpr hj
  · intro j₁ _ j₂ _ h
    exact Fin.ext h
  · intro k hk
    rw [Finset.mem_Ico] at hk
    refine ⟨⟨k, by omega⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hk

private lemma pairOf_walkFn_val {n : ℕ} (hn : 0 < n) (c : Fin (2 * n)) (hc : c.val < n)
    (a : Fin (2 * n)) :
    (pairOf (walkFn hn c false a)).val =
      if c.val + a.val < n then c.val + a.val
      else if c.val + a.val < 2 * n then 2 * n - 1 - (c.val + a.val)
      else c.val + a.val - 2 * n := by
  simp only [pairOf, walkFn, Bool.false_eq_true, ↓reduceIte]
  have ha : a.val < 2 * n := a.isLt
  have hmod : (c.val + a.val) % (2 * n) =
      if c.val + a.val < 2 * n then c.val + a.val else c.val + a.val - 2 * n := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  split_ifs <;> omega

private lemma splitPairs_walkFn_card_le {n : ℕ} (hn : 0 < n) (c : Fin (2 * n)) (hc : c.val < n)
    (i : Fin (2 * n)) :
    (splitPairs (walkFn hn c false) i).card ≤ max c.val (n - c.val) := by
  have hi_lt : i.val < 2 * n := i.isLt
  by_cases h1 : i.val ≤ n - c.val
  · have hsub : splitPairs (walkFn hn c false) i ⊆
        Finset.univ.filter (fun j : Fin n => c.val ≤ j.val ∧ j.val < c.val + i.val) := by
      intro j hj
      simp only [splitPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rcases hj with ⟨⟨a, ha, hja⟩, _⟩
      have hv := congrArg Fin.val hja
      rw [pairOf_walkFn_val hn c hc a] at hv
      split_ifs at hv <;> omega
    have hc1 := Finset.card_le_card hsub
    have hc2 := card_filter_Ico_le (n := n) (a := c.val) (b := c.val + i.val)
    omega
  · by_cases h2 : i.val ≤ 2 * (n - c.val)
    · have hsub : splitPairs (walkFn hn c false) i ⊆
          Finset.univ.filter (fun j : Fin n => c.val ≤ j.val ∧ j.val < 2 * n - c.val - i.val) := by
        intro j hj
        simp only [splitPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        rcases hj with ⟨⟨a, ha, hja⟩, ⟨b, hb, hjb⟩⟩
        have hva := congrArg Fin.val hja
        have hvb := congrArg Fin.val hjb
        rw [pairOf_walkFn_val hn c hc a] at hva
        rw [pairOf_walkFn_val hn c hc b] at hvb
        have hb_lt : b.val < 2 * n := b.isLt
        split_ifs at hva hvb <;> omega
      have hc1 := Finset.card_le_card hsub
      have hc2 := card_filter_Ico_le (n := n) (a := c.val) (b := 2 * n - c.val - i.val)
      omega
    · by_cases h3 : i.val ≤ 2 * n - c.val
      · have hsub : splitPairs (walkFn hn c false) i ⊆
            Finset.univ.filter (fun j : Fin n => 2 * n - c.val - i.val ≤ j.val ∧ j.val < c.val) := by
          intro j hj
          simp only [splitPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          rcases hj with ⟨⟨a, ha, hja⟩, ⟨b, hb, hjb⟩⟩
          have hva := congrArg Fin.val hja
          have hvb := congrArg Fin.val hjb
          rw [pairOf_walkFn_val hn c hc a] at hva
          rw [pairOf_walkFn_val hn c hc b] at hvb
          have hb_lt : b.val < 2 * n := b.isLt
          split_ifs at hva hvb <;> omega
        have hc1 := Finset.card_le_card hsub
        have hc2 := card_filter_Ico_le (n := n) (a := 2 * n - c.val - i.val) (b := c.val)
        omega
      · have hsub : splitPairs (walkFn hn c false) i ⊆
            Finset.univ.filter (fun j : Fin n => c.val + i.val - 2 * n ≤ j.val ∧ j.val < c.val) := by
          intro j hj
          simp only [splitPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          rcases hj with ⟨_, ⟨b, hb, hjb⟩⟩
          have hvb := congrArg Fin.val hjb
          rw [pairOf_walkFn_val hn c hc b] at hvb
          have hb_lt : b.val < 2 * n := b.isLt
          split_ifs at hvb <;> omega
        have hc1 := Finset.card_le_card hsub
        have hc2 := card_filter_Ico_le (n := n) (a := c.val + i.val - 2 * n) (b := c.val)
        omega

private lemma le_sup_splitPairs_walkFn_right {n : ℕ} (hn : 0 < n) (c : Fin (2 * n)) (hc : c.val < n) :
    n - c.val ≤
      (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs (walkFn hn c false) i).card) := by
  let i₁ : Fin (2 * n) := ⟨n - c.val, by omega⟩
  have hsub : Finset.univ.filter (fun j : Fin n => c.val ≤ j.val ∧ j.val < n) ⊆
      splitPairs (walkFn hn c false) i₁ := by
    intro j hj
    simp only [splitPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have hj_lt : j.val < n := j.isLt
    refine ⟨⟨⟨j.val - c.val, by omega⟩, by simp [i₁]; omega, ?_⟩,
      ⟨⟨2 * n - 1 - c.val - j.val, by omega⟩, by simp [i₁]; omega, ?_⟩⟩
    · apply Fin.ext
      rw [pairOf_walkFn_val hn c hc]
      simp only
      split_ifs <;> omega
    · apply Fin.ext
      rw [pairOf_walkFn_val hn c hc]
      simp only
      split_ifs <;> omega
  have hcard := Finset.card_le_card hsub
  rw [card_filter_Ico_eq (le_refl n)] at hcard
  exact le_trans hcard (Finset.le_sup (f := fun i => (splitPairs (walkFn hn c false) i).card) (Finset.mem_univ i₁))

private lemma le_sup_splitPairs_walkFn_left {n : ℕ} (hn : 0 < n) (c : Fin (2 * n)) (hc : c.val < n) :
    c.val ≤
      (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs (walkFn hn c false) i).card) := by
  by_cases hc0 : c.val = 0
  · rw [hc0]
    exact Nat.zero_le _
  · have hc_pos : 0 < c.val := Nat.pos_of_ne_zero hc0
    let i₂ : Fin (2 * n) := ⟨2 * n - c.val, by omega⟩
    have hsub : Finset.univ.filter (fun j : Fin n => 0 ≤ j.val ∧ j.val < c.val) ⊆
        splitPairs (walkFn hn c false) i₂ := by
      intro j hj
      simp only [splitPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      refine ⟨⟨⟨2 * n - 1 - c.val - j.val, by omega⟩, by simp [i₂]; omega, ?_⟩,
        ⟨⟨2 * n - c.val + j.val, by omega⟩, by simp [i₂], ?_⟩⟩
      · apply Fin.ext
        rw [pairOf_walkFn_val hn c hc]
        simp only
        split_ifs <;> omega
      · apply Fin.ext
        rw [pairOf_walkFn_val hn c hc]
        simp only
        split_ifs <;> omega
    have hcard := Finset.card_le_card hsub
    rw [card_filter_Ico_eq (le_of_lt hc), Nat.sub_zero] at hcard
    exact le_trans hcard (Finset.le_sup (f := fun i => (splitPairs (walkFn hn c false) i).card) (Finset.mem_univ i₂))

private lemma walk_peak_eq_lt {n : ℕ} (hn : 0 < n) (c : Fin (2 * n)) (hc : c.val < n) :
    (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs (walkFn hn c false) i).card) =
      max c.val (n - c.val) := by
  apply le_antisymm
  · exact Finset.sup_le fun i _ => splitPairs_walkFn_card_le hn c hc i
  · exact max_le (le_sup_splitPairs_walkFn_left hn c hc) (le_sup_splitPairs_walkFn_right hn c hc)

private lemma walk_peak_eq_false (n : ℕ) (hn : 0 < n) (c : Fin (2 * n)) :
    (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs (walkFn hn c false) i).card) =
      max (c.val % n) (n - c.val % n) := by
  by_cases hc : c.val < n
  · rw [Nat.mod_eq_of_lt hc]
    exact walk_peak_eq_lt hn c hc
  · have hge : n ≤ c.val := Nat.le_of_not_lt hc
    have hlt : c.val - n < n := by omega
    have hsup :
        (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs (walkFn hn c false) i).card) =
        (Finset.univ : Finset (Fin (2 * n))).sup
          (fun i => (splitPairs (walkFn hn ⟨c.val - n, by omega⟩ false) i).card) := by
      congr 1
      funext i
      exact card_splitPairs_shift hn c hge i
    rw [hsup, walk_peak_eq_lt hn ⟨c.val - n, by omega⟩ hlt]
    have hmod : c.val % n = c.val - n := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    rw [hmod]

lemma walk_peak_eq (n : ℕ) (hn : 0 < n) (c : Fin (2 * n)) (rev : Bool) :
    (Finset.univ : Finset (Fin (2 * n))).sup (fun i => (splitPairs (walkFn hn c rev) i).card) =
      max (c.val % n) (n - c.val % n) := by
  cases rev with
  | true =>
    rw [walkFn_true_eq hn c, sup_splitPairs_comp_rev]
    exact walk_peak_eq_false n hn c
  | false =>
    exact walk_peak_eq_false n hn c

end PEqualNP.Outside.L_lib_1051

theorem PEqualNP.Outside.L_lib_1051 : (∀ (n r : Nat) (hn : 0 < n), 4 ≤ r →
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let k := 2*n
  let W := Fin k
  let V := Fin n → ZMod 2
  let mcol := fun (p : W) (j : Fin n) =>
    if min p.val (k-1-p.val) = j.val then (1 : ZMod 2) else 0
  let span := fun (ps : List W) => Submodule.span (ZMod 2)
    (↑((ps.map mcol).toFinset) : Set V)
  let arc := fun (p : W) => (Finset.univ : Finset W).filter (fun z =>
    ∃ a : Fin (5*r-2), (p.val+a.val)%k = z.val)
  let pool := fun (ps : List W) => ps.toFinset.biUnion arc
  let charge := fun (o : W → W) (i : W) =>
    let L := (List.ofFn o).take i.val
    let R := (List.ofFn o).drop i.val
    Module.finrank (ZMod 2) (span L ⊓ span R : Submodule (ZMod 2) V)
  let peak := fun (o : W → W) => (Finset.univ : Finset W).sup (charge o)
  let width := fun (o : W → W) => (Finset.univ : Finset W).sup (fun i =>
    let L := (List.ofFn o).take i.val
    let R := (List.ofFn o).drop i.val
    ((pool L ∩ pool R) ∪ arc (o i)).card + charge o i)
  let order := fun (o : W → W) => Function.Bijective o ∧ ∀ u : Fin (k+1),
    let S := ((List.ofFn o).take u.val).toFinset
    ((Finset.univ : Finset W).filter (fun j => j ∈ S ∧
      ∀ z ∈ S, (z.val+1)%k ≠ j.val)).card ≤ 1
  let walk := fun (c : W) (rev : Bool) (i : W) =>
    (⟨(c.val+(if rev then k-1-i.val else i.val))%k,
      Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 1) hn)⟩ : W)
  let folded := fun (i : W) =>
    let v : W := ⟨i.val/2, Nat.lt_of_le_of_lt (Nat.div_le_self i.val 2) i.isLt⟩
    if i.val % 2 = 0 then Fin.rev v else v
  order folded ∧ peak folded = 1 ∧ width folded ≤ min k (2*(5*r-3)+1)+1 ∧
    (∀ o : W → W, Function.Bijective o → 1 ≤ peak o) ∧
    (∀ (c : W) (rev : Bool),
      let t := c.val % n
      peak (walk c rev) = max t (n-t) ∧ peak (walk c rev) ≤ width (walk c rev)) ∧
    ∃ c : W, ∀ rev : Bool, peak (walk c rev) = (n+1)/2) := by
  intro n r hn hr k W V mcol span arc pool charge peak width order walk folded
  have hmcol : mcol = @PEqualNP.Outside.L_lib_1051.mcolFn n := by
    funext p j
    simp only [mcol, PEqualNP.Outside.L_lib_1051.mcolFn, k]
    split_ifs <;> rfl
  have hcharge : ∀ (o : W → W) (i : W),
      charge o i = (PEqualNP.Outside.L_lib_1051.splitPairs o i).card := by
    intro o i
    have hsub : (span ((List.ofFn o).take i.val) ⊓ span ((List.ofFn o).drop i.val) : Submodule (ZMod 2) V) =
        (Submodule.span (ZMod 2) (↑(@List.toFinset V (fun a b => Classical.propDecidable (a = b))
          (((List.ofFn o).take i.val).map PEqualNP.Outside.L_lib_1051.mcolFn)) : Set V) ⊓
         Submodule.span (ZMod 2) (↑(@List.toFinset V (fun a b => Classical.propDecidable (a = b))
          (((List.ofFn o).drop i.val).map PEqualNP.Outside.L_lib_1051.mcolFn)) : Set V) : Submodule (ZMod 2) V) := by
      simp only [span, hmcol]
    exact (congrArg (fun S : Submodule (ZMod 2) V => Module.finrank (ZMod 2) ↥S) hsub).trans
      (PEqualNP.Outside.L_lib_1051.charge_eq_splitPairs o i)
  have hpeak : ∀ o : W → W,
      peak o = (Finset.univ : Finset W).sup (fun i => (PEqualNP.Outside.L_lib_1051.splitPairs o i).card) := by
    intro o
    change (Finset.univ : Finset W).sup (charge o) = _
    congr 1
    funext i
    exact hcharge o i
  have hfolded : folded = @PEqualNP.Outside.L_lib_1051.foldedFn n := by
    funext i
    simp only [folded, PEqualNP.Outside.L_lib_1051.foldedFn]
    split_ifs <;> rfl
  have hwalk : ∀ (c : W) (rev : Bool), walk c rev = PEqualNP.Outside.L_lib_1051.walkFn hn c rev := by
    intro c rev
    funext i
    simp only [walk, PEqualNP.Outside.L_lib_1051.walkFn, k]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfolded]
    exact PEqualNP.Outside.L_lib_1051.folded_order n hn
  · rw [hpeak, hfolded]
    apply le_antisymm
    · exact Finset.sup_le fun i _ => PEqualNP.Outside.L_lib_1051.folded_splitPairs_card_le n i
    · exact PEqualNP.Outside.L_lib_1051.one_le_peak_bijective hn _ (PEqualNP.Outside.L_lib_1051.foldedFn_bijective n)
  · refine Finset.sup_le fun i _ => ?_
    have h1 := PEqualNP.Outside.L_lib_1051.folded_strip_card_le n r hn hr i
    have h2 : charge folded i ≤ 1 := by
      rw [hcharge, hfolded]
      exact PEqualNP.Outside.L_lib_1051.folded_splitPairs_card_le n i
    rw [hfolded]
    exact Nat.add_le_add h1 (by rw [← hfolded]; exact h2)
  · intro o ho
    rw [hpeak]
    exact PEqualNP.Outside.L_lib_1051.one_le_peak_bijective hn o ho
  · intro c rev
    constructor
    · rw [hpeak, hwalk]
      exact PEqualNP.Outside.L_lib_1051.walk_peak_eq n hn c rev
    · exact Finset.sup_mono_fun fun i _ => Nat.le_add_left _ _
  · refine ⟨⟨n / 2, by omega⟩, fun rev => ?_⟩
    rw [hpeak, hwalk, PEqualNP.Outside.L_lib_1051.walk_peak_eq n hn ⟨n / 2, by omega⟩ rev]
    have hmod : (n / 2) % n = n / 2 := Nat.mod_eq_of_lt (by omega)
    dsimp only
    rw [hmod]
    omega

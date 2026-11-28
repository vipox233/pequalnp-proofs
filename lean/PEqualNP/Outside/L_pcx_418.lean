import PEqualNP.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

namespace PEqualNP.Outside.L_pcx_418_aux

lemma eq_of_le_of_direction_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {A B : AffineSubspace K V} (hne : (A : Set V).Nonempty) (hle : A ≤ B)
    (hdir : A.direction = B.direction) : A = B := by
  ext v
  constructor
  · exact fun hv => hle hv
  · intro hv
    rcases hne with ⟨a, ha⟩
    have haB : a ∈ B := hle ha
    have hvsub : v -ᵥ a ∈ B.direction := AffineSubspace.vsub_mem_direction hv haB
    rw [← hdir] at hvsub
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hvsub ha
    simpa [vsub_vadd] using hmem

lemma exists_sub_empty_inter {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι] :
    ∀ (d : ℕ) (A : AffineSubspace K V) (F : Finset ι) (B : ι → AffineSubspace K V),
      Module.finrank K A.direction ≤ d →
      (A : Set V).Nonempty →
      ((A : Set V) ∩ ⋂ i ∈ F, (B i : Set V)) = ∅ →
      ∃ G ⊆ F, G.card ≤ d + 1 ∧ ((A : Set V) ∩ ⋂ i ∈ G, (B i : Set V)) = ∅ := by
  intro d
  induction d with
  | zero =>
    intro A F B hdim hne hemp
    have hnotall : ¬ (∀ i ∈ F, A ≤ B i) := by
      intro hall
      rcases hne with ⟨a, ha⟩
      have hmem : a ∈ (A : Set V) ∩ ⋂ i ∈ F, (B i : Set V) := by
        refine ⟨ha, ?_⟩
        simp only [Set.mem_iInter]
        intro i hi
        exact hall i hi ha
      rw [hemp] at hmem
      exact hmem
    push_neg at hnotall
    rcases hnotall with ⟨i0, hi0F, hnotle⟩
    refine ⟨{i0}, Finset.singleton_subset_iff.mpr hi0F, by simp, ?_⟩
    by_contra hne'
    have hne'' : ((A ⊓ B i0 : AffineSubspace K V) : Set V).Nonempty := by
      rcases Set.nonempty_iff_ne_empty.mpr hne' with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_singleton, SetLike.mem_coe] at hv
      exact ⟨hv.1, hv.2 i0 rfl⟩
    have hdir_le : (A ⊓ B i0).direction ≤ A.direction :=
      AffineSubspace.direction_le inf_le_left
    have hdir_eq : (A ⊓ B i0).direction = A.direction := by
      apply Submodule.eq_of_le_of_finrank_eq hdir_le
      have h1 := Submodule.finrank_mono hdir_le
      omega
    have heq : A ⊓ B i0 = A := eq_of_le_of_direction_eq hne'' inf_le_left hdir_eq
    exact hnotle (inf_eq_left.mp heq)
  | succ d ih =>
    intro A F B hdim hne hemp
    have hnotall : ¬ (∀ i ∈ F, A ≤ B i) := by
      intro hall
      rcases hne with ⟨a, ha⟩
      have hmem : a ∈ (A : Set V) ∩ ⋂ i ∈ F, (B i : Set V) := by
        refine ⟨ha, ?_⟩
        simp only [Set.mem_iInter]
        intro i hi
        exact hall i hi ha
      rw [hemp] at hmem
      exact hmem
    push_neg at hnotall
    rcases hnotall with ⟨i0, hi0F, hnotle⟩
    set A' : AffineSubspace K V := A ⊓ B i0
    by_cases hA' : (A' : Set V).Nonempty
    · have hdir_le : A'.direction ≤ A.direction := AffineSubspace.direction_le inf_le_left
      have hdir_lt : A'.direction < A.direction := by
        refine lt_of_le_of_ne hdir_le fun hdir_eq => ?_
        have heq : A' = A := eq_of_le_of_direction_eq hA' inf_le_left hdir_eq
        exact hnotle (inf_eq_left.mp heq)
      have hfin_lt : Module.finrank K A'.direction < Module.finrank K A.direction :=
        Submodule.finrank_lt_finrank_of_lt hdir_lt
      have hfin_le : Module.finrank K A'.direction ≤ d := by omega
      have hemp' : ((A' : Set V) ∩ ⋂ i ∈ F.erase i0, (B i : Set V)) = ∅ := by
        ext v
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
        intro hv
        have hvA : v ∈ (A : Set V) := hv.1.1
        have hvBi0 : v ∈ (B i0 : Set V) := hv.1.2
        have hmem : v ∈ (A : Set V) ∩ ⋂ i ∈ F, (B i : Set V) := by
          refine ⟨hvA, ?_⟩
          simp only [Set.mem_iInter]
          intro i hi
          by_cases hieq : i = i0
          · subst hieq; exact hvBi0
          · exact hv.2 i (Finset.mem_erase.mpr ⟨hieq, hi⟩)
        rw [hemp] at hmem
        exact hmem
      obtain ⟨G', hG'sub, hG'card, hG'emp⟩ := ih A' (F.erase i0) B hfin_le hA' hemp'
      refine ⟨insert i0 G', Finset.insert_subset hi0F (hG'sub.trans (Finset.erase_subset i0 F)), ?_, ?_⟩
      · calc (insert i0 G').card ≤ G'.card + 1 := Finset.card_insert_le i0 G'
          _ ≤ d + 1 + 1 := by omega
      · ext v
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
        intro hv
        have hvA' : v ∈ (A' : Set V) := ⟨hv.1, hv.2 i0 (Finset.mem_insert_self i0 G')⟩
        have hmem : v ∈ (A' : Set V) ∩ ⋂ i ∈ G', (B i : Set V) := by
          refine ⟨hvA', ?_⟩
          simp only [Set.mem_iInter]
          intro i hi
          exact hv.2 i (Finset.mem_insert_of_mem hi)
        rw [hG'emp] at hmem
        exact hmem
    · refine ⟨{i0}, Finset.singleton_subset_iff.mpr hi0F, by simp, ?_⟩
      ext v
      simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_singleton,
        Set.mem_empty_iff_false, iff_false]
      intro hv
      apply hA'
      exact ⟨v, hv.1, hv.2 i0 rfl⟩

def obsAff {K : Type*} [Field K] {n w : ℕ}
    (ask : List (Fin w → K) → (Fin n → K) →ₗ[K] (Fin w → K))
    (off : List (Fin w → K) → (Fin w → K))
    (h : List (Fin w → K)) : (Fin n → K) →ᵃ[K] (Fin w → K) where
  toFun x := ask h x + off h
  linear := ask h
  map_vadd' x v := by
    simp only [vadd_eq_add, map_add]
    abel

def cellSub {K : Type*} [Field K] {n w : ℕ}
    (P : AffineSubspace K (Fin n → K))
    (ask : List (Fin w → K) → (Fin n → K) →ₗ[K] (Fin w → K))
    (off : List (Fin w → K) → (Fin w → K))
    (h : List (Fin w → K)) : AffineSubspace K (Fin n → K) :=
  P ⊓ ⨅ i : Fin h.length,
    (AffineSubspace.mk' (h.get i) ⊥).comap (obsAff ask off (h.take i.val))

lemma mem_iInf_aff {K V : Type*} {ι : Sort*} [Field K] [AddCommGroup V] [Module K V]
    (S : ι → AffineSubspace K V) (x : V) :
    x ∈ (⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  constructor
  · intro hx i
    exact iInf_le S i hx
  · intro hx
    have hle : AffineSubspace.mk' x ⊥ ≤ ⨅ i, S i := by
      refine le_iInf fun i => ?_
      intro v hv
      have hveq : v = x := sub_eq_zero.mp (by simpa [AffineSubspace.mem_mk', Submodule.mem_bot] using hv)
      exact hveq ▸ hx i
    exact hle (AffineSubspace.self_mem_mk' x ⊥)

lemma mem_cellSub_iff {K : Type*} [Field K] {n w : ℕ}
    (P : AffineSubspace K (Fin n → K))
    (ask : List (Fin w → K) → (Fin n → K) →ₗ[K] (Fin w → K))
    (off : List (Fin w → K) → (Fin w → K))
    (h : List (Fin w → K)) (x : Fin n → K) :
    x ∈ cellSub P ask off h ↔
      x ∈ P ∧ ∀ i : Fin h.length, h.get i = ask (h.take i.val) x + off (h.take i.val) := by
  simp only [cellSub, AffineSubspace.mem_inf_iff, mem_iInf_aff,
    AffineSubspace.mem_comap, AffineSubspace.mem_mk', Submodule.mem_bot, vsub_eq_zero_iff_eq,
    obsAff, AffineMap.coe_mk]
  simp only [eq_comm]

lemma cellSub_coe {K : Type*} [Field K] {n w : ℕ}
    (P : AffineSubspace K (Fin n → K))
    (ask : List (Fin w → K) → (Fin n → K) →ₗ[K] (Fin w → K))
    (off : List (Fin w → K) → (Fin w → K))
    (h : List (Fin w → K)) :
    (cellSub P ask off h : Set (Fin n → K)) =
      {x | x ∈ P ∧ ∀ i : Fin h.length, h.get i = ask (h.take i.val) x + off (h.take i.val)} := by
  ext x
  exact mem_cellSub_iff P ask off h x

lemma prefix_of_mem_both {K : Type*} [Field K] {n w : ℕ}
    (P : AffineSubspace K (Fin n → K))
    (ask : List (Fin w → K) → (Fin n → K) →ₗ[K] (Fin w → K))
    (off : List (Fin w → K) → (Fin w → K))
    {h p : List (Fin w → K)} {x : Fin n → K}
    (hx_h : x ∈ cellSub P ask off h) (hx_p : x ∈ cellSub P ask off p) :
    List.IsPrefix h p ∨ List.IsPrefix p h := by
  have h1 := (mem_cellSub_iff P ask off h x).mp hx_h
  have h2 := (mem_cellSub_iff P ask off p x).mp hx_p
  have htake : ∀ t : ℕ, t ≤ h.length → t ≤ p.length → h.take t = p.take t := by
    intro t
    induction t with
    | zero => intro _ _; simp
    | succ t ih =>
      intro hth htp
      have hprev := ih (Nat.le_of_succ_le hth) (Nat.le_of_succ_le htp)
      have hget : h.get ⟨t, hth⟩ = p.get ⟨t, htp⟩ := by
        rw [h1.2 ⟨t, hth⟩, h2.2 ⟨t, htp⟩, hprev]
      rw [List.take_add_one, List.take_add_one, hprev,
        List.getElem?_eq_getElem hth, List.getElem?_eq_getElem htp]
      have hget' : h[t]'hth = p[t]'htp := hget
      rw [hget']
  rcases le_total h.length p.length with hle | hle
  · left
    have ht := htake h.length le_rfl hle
    rw [List.take_length] at ht
    rw [ht]
    exact List.take_prefix h.length p
  · right
    have ht := htake p.length hle le_rfl
    rw [List.take_length] at ht
    rw [← ht]
    exact List.take_prefix p.length h

lemma mem_cellSub_append_singleton {K : Type*} [Field K] {n w : ℕ}
    (P : AffineSubspace K (Fin n → K))
    (ask : List (Fin w → K) → (Fin n → K) →ₗ[K] (Fin w → K))
    (off : List (Fin w → K) → (Fin w → K))
    (h : List (Fin w → K)) (y : Fin w → K) (x : Fin n → K) :
    x ∈ cellSub P ask off (h ++ [y]) ↔
      x ∈ cellSub P ask off h ∧ y = ask h x + off h := by
  rw [mem_cellSub_iff, mem_cellSub_iff]
  constructor
  · rintro ⟨hxP, hall⟩
    refine ⟨⟨hxP, fun i => ?_⟩, ?_⟩
    · have hi : i.val < (h ++ [y]).length := by simp only [List.length_append, List.length_singleton]; omega
      have hget := hall ⟨i.val, hi⟩
      have hg1 : (h ++ [y]).get ⟨i.val, hi⟩ = h.get i := by
        simp [List.getElem_append_left i.isLt]
      have ht1 : (h ++ [y]).take i.val = h.take i.val := by
        rw [List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
      rw [hg1, ht1] at hget
      exact hget
    · have hi : h.length < (h ++ [y]).length := by simp
      have hget := hall ⟨h.length, hi⟩
      have hg1 : (h ++ [y]).get ⟨h.length, hi⟩ = y := by simp
      have ht1 : (h ++ [y]).take h.length = h := by simp
      rw [hg1, ht1] at hget
      exact hget
  · rintro ⟨⟨hxP, hall⟩, hy⟩
    refine ⟨hxP, fun i => ?_⟩
    by_cases hlt : i.val < h.length
    · have hg1 : (h ++ [y]).get i = h.get ⟨i.val, hlt⟩ := by
        simp [List.getElem_append_left hlt]
      have ht1 : (h ++ [y]).take i.val = h.take i.val := by
        rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      rw [hg1, ht1]
      exact hall ⟨i.val, hlt⟩
    · have heq : i.val = h.length := by
        have hlen := i.isLt
        simp at hlen
        omega
      have hg1 : (h ++ [y]).get i = y := by
        simp [List.get_eq_getElem, heq]
      have ht1 : (h ++ [y]).take i.val = h := by
        simp [heq]
      rw [hg1, ht1]
      exact hy

lemma cellSub_anti_of_prefix {K : Type*} [Field K] {n w : ℕ}
    (P : AffineSubspace K (Fin n → K))
    (ask : List (Fin w → K) → (Fin n → K) →ₗ[K] (Fin w → K))
    (off : List (Fin w → K) → (Fin w → K))
    {h p : List (Fin w → K)} (hpre : List.IsPrefix h p) :
    cellSub P ask off p ≤ cellSub P ask off h := by
  intro x hx
  rw [mem_cellSub_iff] at hx ⊢
  rcases hpre with ⟨r, rfl⟩
  refine ⟨hx.1, fun i => ?_⟩
  have hi : i.val < (h ++ r).length := by simp; omega
  have hget := hx.2 ⟨i.val, hi⟩
  have hg1 : (h ++ r).get ⟨i.val, hi⟩ = h.get i := by
    simp [List.getElem_append_left i.isLt]
  have ht1 : (h ++ r).take i.val = h.take i.val := by
    rw [List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
  rw [hg1, ht1] at hget
  exact hget

lemma prefix_cons_unique {α : Type*} {h p : List α} {y1 y2 : α}
    (h1 : List.IsPrefix (h ++ [y1]) p) (h2 : List.IsPrefix (h ++ [y2]) p) : y1 = y2 := by
  rcases h1 with ⟨r1, hr1⟩
  rcases h2 with ⟨r2, hr2⟩
  have heq : h ++ (y1 :: r1) = h ++ (y2 :: r2) := by
    simpa [List.append_assoc] using hr1.trans hr2.symm
  have := List.append_cancel_left heq
  exact (List.cons.inj this).1

lemma prefix_split {α : Type*} {h p : List α} (hpre : List.IsPrefix h p) (hne : h ≠ p) :
    ∃ y : α, List.IsPrefix (h ++ [y]) p := by
  rcases hpre with ⟨r, rfl⟩
  cases r with
  | nil => exact absurd (by simp) hne
  | cons y rs =>
    refine ⟨y, ⟨rs, ?_⟩⟩
    simp [List.append_assoc]

end PEqualNP.Outside.L_pcx_418_aux

theorem PEqualNP.Outside.L_pcx_418 :
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (n w m : ℕ),
  let X := Fin n → K
  let Y := Fin w → K
  ∀ (P : AffineSubspace K X) (bad : Fin m → AffineSubspace K X)
    (leaves : Finset (List Y)) (ask : List Y → X →ₗ[K] Y) (off : List Y → Y)
    (out : List Y → Fin m),
    let obs := fun (h : List Y) (x : X) => ask h x + off h
    let cell := fun h : List Y => {x : X | x ∈ P ∧
      ∀ i : Fin h.length, h.get i = obs (h.take i.val) x}
    (∃ x : X, x ∈ P) →
    (∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q) →
    (∀ x ∈ P, ∃ p ∈ leaves, x ∈ cell p) →
    (∀ p ∈ leaves, (cell p).Nonempty ∧ ∀ x ∈ cell p, x ∉ bad (out p)) →
    ∃ chosen : Finset (List Y), chosen ⊆ leaves ∧ chosen.Nonempty ∧
      ∀ h : List Y,
        let next := Finset.univ.filter (fun y : Y =>
          @decide (∃ p ∈ chosen, List.IsPrefix (h ++ [y]) p) (Classical.propDecidable _))
        let rank := Module.finrank K (affineSpan K (Set.image (obs h) (cell h))).direction
        next.card ≤ rank+1 ∧
        ((∃ p ∈ chosen, List.IsPrefix h p) →
          ∀ x ∈ cell h, ∃ p ∈ chosen, List.IsPrefix h p ∧ x ∉ bad (out p)) := by
  intro K _ _ _ n w m X Y P bad leaves ask off out obs cell hPne hpre_free hcov hleaves
  open PEqualNP.Outside.L_pcx_418_aux in
  let D : ℕ := leaves.sup List.length
  have hD_le : ∀ p ∈ leaves, p.length ≤ D := fun p hp => Finset.le_sup (f := List.length) hp
  have hmain : ∀ (k : ℕ) (h : List Y),
      D - h.length ≤ k →
      (∃ p ∈ leaves, List.IsPrefix h p) →
      ∃ C : Finset (List Y),
        C ⊆ leaves ∧ C.Nonempty ∧
        (∀ p ∈ C, List.IsPrefix h p) ∧
        (∀ x ∈ cell h, ∃ p ∈ C, x ∉ bad (out p)) ∧
        (∀ h' : List Y, List.IsPrefix h h' →
          let next := Finset.univ.filter (fun y : Y =>
            @decide (∃ p ∈ C, List.IsPrefix (h' ++ [y]) p) (Classical.propDecidable _))
          let rank := Module.finrank K (affineSpan K (Set.image (obs h') (cell h'))).direction
          next.card ≤ rank + 1 ∧
          ((∃ p ∈ C, List.IsPrefix h' p) →
            ∀ x ∈ cell h', ∃ p ∈ C, List.IsPrefix h' p ∧ x ∉ bad (out p))) := by
    intro k
    induction k with
    | zero =>
      intro h hk hex
      rcases hex with ⟨p0, hp0L, hpre0⟩
      have hlen_le : h.length ≤ p0.length := hpre0.length_le
      have hp0_le : p0.length ≤ D := hD_le p0 hp0L
      have hlen_eq : h.length = p0.length := by omega
      have h_eq_p0 : h = p0 := by
        rcases hpre0 with ⟨r, rfl⟩
        have hr : r = [] := by
          have : h.length + r.length = h.length := by simpa using hlen_eq.symm
          exact List.eq_nil_of_length_eq_zero (by omega)
        simp [hr]
      subst h_eq_p0
      refine ⟨{h}, Finset.singleton_subset_iff.mpr hp0L, Finset.singleton_nonempty h,
        fun p hp => by rw [Finset.mem_singleton.mp hp],
        fun x hx => ⟨h, Finset.mem_singleton_self h, (hleaves h hp0L).2 x hx⟩, ?_⟩
      intro h' hhh'
      constructor
      · have hemp : Finset.univ.filter (fun y : Y =>
            @decide (∃ p ∈ ({h} : Finset (List Y)), List.IsPrefix (h' ++ [y]) p)
              (Classical.propDecidable _)) = ∅ := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
            Finset.notMem_empty, iff_false, not_exists, not_and]
          intro p hp hpre
          rw [Finset.mem_singleton.mp hp] at hpre
          have h1 := hhh'.length_le
          have h2 := hpre.length_le
          simp at h2
          omega
        rw [hemp, Finset.card_empty]
        omega
      · rintro ⟨p, hp, hpre⟩ x hx
        rw [Finset.mem_singleton.mp hp] at hpre
        have heq : h' = h := by
          rcases hhh' with ⟨r, rfl⟩
          have hlen := hpre.length_le
          have hr : r = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_append] at hlen; omega)
          simp [hr]
        subst heq
        exact ⟨h', Finset.mem_singleton_self h', List.prefix_refl h', (hleaves h' hp0L).2 x hx⟩
    | succ k ih =>
      intro h hk hex
      by_cases hhL : h ∈ leaves
      · refine ⟨{h}, Finset.singleton_subset_iff.mpr hhL, Finset.singleton_nonempty h,
          fun p hp => by rw [Finset.mem_singleton.mp hp],
          fun x hx => ⟨h, Finset.mem_singleton_self h, (hleaves h hhL).2 x hx⟩, ?_⟩
        intro h' hhh'
        constructor
        · have hemp : Finset.univ.filter (fun y : Y =>
              @decide (∃ p ∈ ({h} : Finset (List Y)), List.IsPrefix (h' ++ [y]) p)
                (Classical.propDecidable _)) = ∅ := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
              Finset.notMem_empty, iff_false, not_exists, not_and]
            intro p hp hpre
            rw [Finset.mem_singleton.mp hp] at hpre
            have h1 := hhh'.length_le
            have h2 := hpre.length_le
            simp at h2
            omega
          rw [hemp, Finset.card_empty]
          omega
        · rintro ⟨p, hp, hpre⟩ x hx
          rw [Finset.mem_singleton.mp hp] at hpre
          have heq : h' = h := by
            rcases hhh' with ⟨r, rfl⟩
            have hlen := hpre.length_le
            have hr : r = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_append] at hlen; omega)
            simp [hr]
          subst heq
          exact ⟨h', Finset.mem_singleton_self h', List.prefix_refl h', (hleaves h' hhL).2 x hx⟩
      · let R : Finset Y := Finset.univ.filter (fun y : Y => ∃ p ∈ leaves, List.IsPrefix (h ++ [y]) p)
        have hchild : ∀ y : Y, y ∈ R →
            ∃ C : Finset (List Y),
              C ⊆ leaves ∧ C.Nonempty ∧
              (∀ p ∈ C, List.IsPrefix (h ++ [y]) p) ∧
              (∀ x ∈ cell (h ++ [y]), ∃ p ∈ C, x ∉ bad (out p)) ∧
              (∀ h' : List Y, List.IsPrefix (h ++ [y]) h' →
                let next := Finset.univ.filter (fun z : Y =>
                  @decide (∃ p ∈ C, List.IsPrefix (h' ++ [z]) p) (Classical.propDecidable _))
                let rank := Module.finrank K (affineSpan K (Set.image (obs h') (cell h'))).direction
                next.card ≤ rank + 1 ∧
                ((∃ p ∈ C, List.IsPrefix h' p) →
                  ∀ x ∈ cell h', ∃ p ∈ C, List.IsPrefix h' p ∧ x ∉ bad (out p))) := by
          intro y hyR
          have hy_ex : ∃ p ∈ leaves, List.IsPrefix (h ++ [y]) p := (Finset.mem_filter.mp hyR).2
          have hlen_lt : D - (h ++ [y]).length ≤ k := by
            rcases hy_ex with ⟨p, hpL, hpre⟩
            have h1 := hpre.length_le
            have h2 := hD_le p hpL
            simp only [List.length_append, List.length_singleton] at h1 ⊢
            omega
          exact ih (h ++ [y]) hlen_lt hy_ex
        choose Cy hCy using hchild
        let f_h : X →ᵃ[K] Y := obsAff ask off h
        let A : AffineSubspace K Y := (cellSub P ask off h).map f_h
        have hA_coe : (A : Set Y) = Set.image (obs h) (cell h) := by
          change (f_h '' (cellSub P ask off h : Set X)) = Set.image (obs h) (cell h)
          rw [cellSub_coe]
          rfl
        have hA_span : affineSpan K (Set.image (obs h) (cell h)) = A := by
          rw [← hA_coe]
          exact A.affineSpan_coe
        have hA_ne : (A : Set Y).Nonempty := by
          rcases hex with ⟨p0, hp0L, hpre0⟩
          rcases (hleaves p0 hp0L).1 with ⟨x0, hx0⟩
          have hx0_sub : x0 ∈ cellSub P ask off p0 := (mem_cellSub_iff P ask off p0 x0).mpr hx0
          have hx0_h : x0 ∈ cellSub P ask off h := cellSub_anti_of_prefix P ask off hpre0 hx0_sub
          exact ⟨f_h x0, ⟨x0, hx0_h, rfl⟩⟩
        let BadY : Y → AffineSubspace K X := fun y =>
          if hy : y ∈ R then cellSub P ask off h ⊓ ⨅ p ∈ Cy y hy, bad (out p) else ⊤
        let ImgY : Y → AffineSubspace K Y := fun y => (BadY y).map f_h
        have hemp : ((A : Set Y) ∩ ⋂ y ∈ R, (ImgY y : Set Y)) = ∅ := by
          ext y0
          simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hy0A, hy0All⟩
          rw [hA_coe] at hy0A
          rcases hy0A with ⟨x0, hx0cell, hx0obs⟩
          have hx0P : x0 ∈ P := hx0cell.1
          rcases hcov x0 hx0P with ⟨p, hpL, hx0p⟩
          have hx0_hsub : x0 ∈ cellSub P ask off h := (mem_cellSub_iff P ask off h x0).mpr hx0cell
          have hx0_psub : x0 ∈ cellSub P ask off p := (mem_cellSub_iff P ask off p x0).mpr hx0p
          have hpre_hp : List.IsPrefix h p := by
            rcases prefix_of_mem_both P ask off hx0_hsub hx0_psub with h1 | h2
            · exact h1
            · rcases hex with ⟨q, hqL, hhq⟩
              have hpq : p = q := hpre_free p hpL q hqL (h2.trans hhq)
              subst hpq
              exact hhq
          have hne_hp : h ≠ p := fun heq => hhL (heq ▸ hpL)
          rcases prefix_split hpre_hp hne_hp with ⟨y1, hpre1⟩
          have hx0_hy1 : x0 ∈ cellSub P ask off (h ++ [y1]) :=
            cellSub_anti_of_prefix P ask off hpre1 hx0_psub
          have hy1_eq : y1 = y0 := by
            have := ((mem_cellSub_append_singleton P ask off h y1 x0).mp hx0_hy1).2
            exact this.trans hx0obs
          rw [hy1_eq] at hpre1
          have hy0R : y0 ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hpL, hpre1⟩⟩
          have hy0Img := hy0All y0 hy0R
          change y0 ∈ f_h '' (BadY y0 : Set X) at hy0Img
          rcases hy0Img with ⟨x1, hx1Bad, hx1obs⟩
          simp only [BadY, dif_pos hy0R, SetLike.mem_coe, AffineSubspace.mem_inf_iff,
            mem_iInf_aff] at hx1Bad
          have hx1_hy0 : x1 ∈ cell (h ++ [y0]) :=
            (mem_cellSub_iff P ask off (h ++ [y0]) x1).mp
              ((mem_cellSub_append_singleton P ask off h y0 x1).mpr ⟨hx1Bad.1, hx1obs.symm⟩)
          rcases (hCy y0 hy0R).2.2.2.1 x1 hx1_hy0 with ⟨p1, hp1C, hx1notbad⟩
          exact hx1notbad (hx1Bad.2 p1 hp1C)
        obtain ⟨G, hGR, hGcard, hGemp⟩ :=
          exists_sub_empty_inter (Module.finrank K A.direction) A R ImgY le_rfl hA_ne hemp
        have hGne : G.Nonempty := by
          by_contra hGe
          rw [Finset.not_nonempty_iff_eq_empty] at hGe
          subst hGe
          rcases hA_ne with ⟨a, ha⟩
          have : a ∈ (A : Set Y) ∩ ⋂ y ∈ (∅ : Finset Y), (ImgY y : Set Y) := by simp [ha]
          rw [hGemp] at this
          exact this
        let C : Finset (List Y) := G.biUnion (fun y => if hy : y ∈ R then Cy y hy else ∅)
        have hmemC : ∀ p, p ∈ C ↔ ∃ y ∈ G, ∃ hy : y ∈ R, p ∈ Cy y hy := by
          intro p
          simp only [C, Finset.mem_biUnion]
          constructor
          · rintro ⟨y, hyG, hp⟩
            have hyR : y ∈ R := hGR hyG
            rw [dif_pos hyR] at hp
            exact ⟨y, hyG, hyR, hp⟩
          · rintro ⟨y, hyG, hyR, hp⟩
            exact ⟨y, hyG, by rw [dif_pos hyR]; exact hp⟩
        have hC_sub : C ⊆ leaves := by
          intro p hp
          rcases (hmemC p).mp hp with ⟨y, _, hyR, hpCy⟩
          exact (hCy y hyR).1 hpCy
        have hC_ne : C.Nonempty := by
          rcases hGne with ⟨y, hyG⟩
          have hyR : y ∈ R := hGR hyG
          rcases (hCy y hyR).2.1 with ⟨p, hpCy⟩
          exact ⟨p, (hmemC p).mpr ⟨y, hyG, hyR, hpCy⟩⟩
        have hC_pre : ∀ p ∈ C, List.IsPrefix h p := by
          intro p hp
          rcases (hmemC p).mp hp with ⟨y, _, hyR, hpCy⟩
          exact (List.prefix_append h [y]).trans ((hCy y hyR).2.2.1 p hpCy)
        have hC_cov : ∀ x ∈ cell h, ∃ p ∈ C, x ∉ bad (out p) := by
          intro x hx
          by_contra hall
          push_neg at hall
          have hxh : x ∈ cellSub P ask off h := (mem_cellSub_iff P ask off h x).mpr hx
          have hmemA : f_h x ∈ (A : Set Y) := ⟨x, hxh, rfl⟩
          have hmemG : f_h x ∈ (A : Set Y) ∩ ⋂ y ∈ G, (ImgY y : Set Y) := by
            refine ⟨hmemA, ?_⟩
            simp only [Set.mem_iInter]
            intro y hyG
            have hyR : y ∈ R := hGR hyG
            refine ⟨x, ?_, rfl⟩
            simp only [BadY, dif_pos hyR, SetLike.mem_coe, AffineSubspace.mem_inf_iff,
              mem_iInf_aff]
            exact ⟨hxh, fun p hpCy => hall p ((hmemC p).mpr ⟨y, hyG, hyR, hpCy⟩)⟩
          rw [hGemp] at hmemG
          exact hmemG
        refine ⟨C, hC_sub, hC_ne, hC_pre, hC_cov, ?_⟩
        intro h' hhh'
        by_cases heqh : h = h'
        · subst heqh
          constructor
          · have hsubG : Finset.univ.filter (fun y : Y =>
                @decide (∃ p ∈ C, List.IsPrefix (h ++ [y]) p) (Classical.propDecidable _)) ⊆ G := by
              intro y hy
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hy
              rcases hy with ⟨p, hpC, hpre_y⟩
              rcases (hmemC p).mp hpC with ⟨y1, hy1G, hy1R, hpCy⟩
              have hpre_y1 := (hCy y1 hy1R).2.2.1 p hpCy
              have hy_eq : y = y1 := prefix_cons_unique hpre_y hpre_y1
              exact hy_eq ▸ hy1G
            have hle1 := Finset.card_le_card hsubG
            rw [hA_span]
            exact hle1.trans hGcard
          · intro _ x hx
            rcases hC_cov x hx with ⟨p, hpC, hxnb⟩
            exact ⟨p, hpC, hC_pre p hpC, hxnb⟩
        · rcases prefix_split hhh' heqh with ⟨y0, hpre_y0⟩
          by_cases hy0G : y0 ∈ G
          · have hy0R : y0 ∈ R := hGR hy0G
            have hCy0_step := (hCy y0 hy0R).2.2.2.2 h' hpre_y0
            have hiff_p : ∀ p, (p ∈ C ∧ List.IsPrefix h' p) ↔ (p ∈ Cy y0 hy0R ∧ List.IsPrefix h' p) := by
              intro p
              constructor
              · rintro ⟨hpC, hpre_p⟩
                rcases (hmemC p).mp hpC with ⟨y1, _, hy1R, hpCy1⟩
                have hpre_y1 := (hCy y1 hy1R).2.2.1 p hpCy1
                have hy_eq : y0 = y1 := prefix_cons_unique (hpre_y0.trans hpre_p) hpre_y1
                subst hy_eq
                exact ⟨hpCy1, hpre_p⟩
              · rintro ⟨hpCy0, hpre_p⟩
                exact ⟨(hmemC p).mpr ⟨y0, hy0G, hy0R, hpCy0⟩, hpre_p⟩
            constructor
            · have hfeq : Finset.univ.filter (fun y : Y =>
                  @decide (∃ p ∈ C, List.IsPrefix (h' ++ [y]) p) (Classical.propDecidable _)) =
                Finset.univ.filter (fun y : Y =>
                  @decide (∃ p ∈ Cy y0 hy0R, List.IsPrefix (h' ++ [y]) p) (Classical.propDecidable _)) := by
                ext z
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
                constructor
                · rintro ⟨p, hpC, hpre_z⟩
                  have hpre_p := (List.prefix_append h' [z]).trans hpre_z
                  exact ⟨p, ((hiff_p p).mp ⟨hpC, hpre_p⟩).1, hpre_z⟩
                · rintro ⟨p, hpCy0, hpre_z⟩
                  have hpre_p := (List.prefix_append h' [z]).trans hpre_z
                  exact ⟨p, ((hiff_p p).mpr ⟨hpCy0, hpre_p⟩).1, hpre_z⟩
              rw [hfeq]
              exact hCy0_step.1
            · rintro ⟨p, hpC, hpre_p⟩ x hx
              have hpCy0 := ((hiff_p p).mp ⟨hpC, hpre_p⟩).1
              rcases hCy0_step.2 ⟨p, hpCy0, hpre_p⟩ x hx with ⟨p', hp'Cy0, hpre_p', hxnb⟩
              exact ⟨p', ((hiff_p p').mpr ⟨hp'Cy0, hpre_p'⟩).1, hpre_p', hxnb⟩
          · constructor
            · have hemp' : Finset.univ.filter (fun y : Y =>
                  @decide (∃ p ∈ C, List.IsPrefix (h' ++ [y]) p) (Classical.propDecidable _)) = ∅ := by
                ext z
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
                  Finset.notMem_empty, iff_false, not_exists, not_and]
                intro p hpC hpre_z
                rcases (hmemC p).mp hpC with ⟨y1, hy1G, hy1R, hpCy1⟩
                have hpre_y1 := (hCy y1 hy1R).2.2.1 p hpCy1
                have hy_eq : y0 = y1 :=
                  prefix_cons_unique (hpre_y0.trans ((List.prefix_append h' [z]).trans hpre_z)) hpre_y1
                exact hy0G (hy_eq ▸ hy1G)
              rw [hemp', Finset.card_empty]
              omega
            · rintro ⟨p, hpC, hpre_p⟩
              exfalso
              rcases (hmemC p).mp hpC with ⟨y1, hy1G, hy1R, hpCy1⟩
              have hpre_y1 := (hCy y1 hy1R).2.2.1 p hpCy1
              have hy_eq : y0 = y1 := prefix_cons_unique (hpre_y0.trans hpre_p) hpre_y1
              exact hy0G (hy_eq ▸ hy1G)
  have hex_nil : ∃ p ∈ leaves, List.IsPrefix ([] : List Y) p := by
    rcases hPne with ⟨x0, hx0P⟩
    rcases hcov x0 hx0P with ⟨p0, hp0L, _⟩
    exact ⟨p0, hp0L, List.nil_prefix⟩
  obtain ⟨chosen, hsub, hne, _, _, hall⟩ := hmain D [] (by simp) hex_nil
  exact ⟨chosen, hsub, hne, fun h => hall h List.nil_prefix⟩

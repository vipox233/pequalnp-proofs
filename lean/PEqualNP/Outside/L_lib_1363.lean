import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1363_aux
section Poset
open scoped Classical
variable {d : ℕ} (R : Fin (d+1) → Fin (d+1) → Prop)

def Lt (x y : Fin (d+1)) : Prop := R x y ∧ x ≠ y
def Nx (x y : Fin (d+1)) : Prop := Lt R x y ∧ ¬ ∃ z, Lt R x z ∧ Lt R z y

noncomputable def pth (k : ℕ) : Fin (d+1) → ℕ :=
  Nat.rec (motive := fun _ => Fin (d+1) → ℕ) (fun _ => 1)
    (fun _ prev x => 1 + (Finset.univ.filter (Nx R x)).sum prev) k

theorem pth_zero (x : Fin (d+1)) : pth R 0 x = 1 := rfl
theorem pth_succ (k : ℕ) (x : Fin (d+1)) :
    pth R (k+1) x = 1 + (Finset.univ.filter (Nx R x)).sum (pth R k) := rfl

noncomputable def U (x : Fin (d+1)) : Finset (Fin (d+1)) := Finset.univ.filter (Lt R x)

def Forest {n : ℕ} (V : Finset (Finset (Fin n))) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, y ⊆ x → z ⊆ x → y ⊆ z ∨ z ⊆ y

def Fit {n : ℕ} (V : Finset (Finset (Fin n))) (ok : Finset (Fin n) → Fin (d+1) → Prop) (p : Fin (d+1)) : Prop :=
  ∃ f : Finset (Fin n) → Fin (d+1), (∀ x ∈ V, R p (f x) ∧ ok x (f x)) ∧
    ∀ x ∈ V, ∀ y ∈ V, x ⊆ y → R (f x) (f y)

variable {R}

theorem U_lt (htrans : ∀ x y z, R x y → R y z → R x z) (hanti : ∀ x y, R x y → R y x → x = y)
    {x y : Fin (d+1)} (h : Lt R x y) : (U R y).card < (U R x).card := by
  have hsub : U R y ⊆ U R x := by
    intro z hz
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, Lt] at hz ⊢
    exact ⟨htrans _ _ _ h.1 hz.1, fun e => h.2 (hanti _ _ h.1 (e ▸ hz.1))⟩
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsub]
  refine ⟨y, ?_, ?_⟩
  · simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]; exact h
  · simp [U, Lt]

theorem U_card_le (x : Fin (d+1)) : (U R x).card ≤ d := by
  have hs : U R x ⊆ Finset.univ.erase x := by
    intro z hz
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, Lt] at hz
    exact Finset.mem_erase.2 ⟨fun e => hz.2 e.symm, Finset.mem_univ _⟩
  have := Finset.card_le_card hs
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
  omega

theorem pth_stab (htrans : ∀ x y z, R x y → R y z → R x z) (hanti : ∀ x y, R x y → R y x → x = y) :
    ∀ k x, (U R x).card ≤ k → pth R k x = pth R (k+1) x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    have hU : U R x = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hx)
    have hC : Finset.univ.filter (Nx R x) = ∅ := by
      apply Finset.filter_false_of_mem
      intro y _ hy
      have hy' : y ∈ U R x := by
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]; exact hy.1
      rw [hU] at hy'
      exact absurd hy' (Finset.notMem_empty _)
    rw [pth_succ, hC, Finset.sum_empty, pth_zero, Nat.add_zero]
  | succ k ih =>
    intro x hx
    rw [pth_succ, pth_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact ih y (by have := U_lt htrans hanti hy.1; omega)

theorem P_rec (htrans : ∀ x y z, R x y → R y z → R x z) (hanti : ∀ x y, R x y → R y x → x = y)
    (x : Fin (d+1)) : pth R d x = 1 + (Finset.univ.filter (Nx R x)).sum (pth R d) := by
  rw [pth_stab htrans hanti d x (U_card_le x), pth_succ]

theorem cover_below (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hanti : ∀ x y, R x y → R y x → x = y) {p m : Fin (d+1)} (h : Lt R p m) : ∃ w, Nx R p w ∧ R w m := by
  have hB : (Finset.univ.filter (fun z => Lt R p z ∧ R z m)).Nonempty :=
    ⟨m, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h, hrefl m⟩⟩
  obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image _ (fun z => (Finset.univ.filter (fun y => Lt R y z)).card) hB
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
  refine ⟨w, ⟨hw.1, ?_⟩, hw.2⟩
  rintro ⟨z, hz1, hz2⟩
  have hzB : z ∈ Finset.univ.filter (fun z => Lt R p z ∧ R z m) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hz1, htrans _ _ _ hz2.1 hw.2⟩
  have h1 := hmin z hzB
  have hlt : (Finset.univ.filter (fun y => Lt R y z)).card < (Finset.univ.filter (fun y => Lt R y w)).card := by
    have hsub : Finset.univ.filter (fun y => Lt R y z) ⊆ Finset.univ.filter (fun y => Lt R y w) := by
      rw [Finset.subset_iff]
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, htrans _ _ _ hy.2.1 hz2.1, fun e => hz2.2 (hanti _ _ hz2.1 (e ▸ hy.2.1))⟩
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨z, ?_, ?_⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hz2⟩
    · exact fun h => (Finset.mem_filter.1 h).2.2 rfl
  omega

theorem minimal_below (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hanti : ∀ x y, R x y → R y x → x = y) (A : Finset (Fin (d+1))) {v : Fin (d+1)} (hv : v ∈ A) :
    ∃ m ∈ A, R m v ∧ ∀ v' ∈ A, R v' m → v' = m := by
  have hne : (A.filter (fun z => R z v)).Nonempty := ⟨v, Finset.mem_filter.2 ⟨hv, hrefl v⟩⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image _ (fun z => (Finset.univ.filter (fun y => Lt R y z)).card) hne
  rw [Finset.mem_filter] at hm
  refine ⟨m, hm.1, hm.2, fun v' hv' hR => ?_⟩
  by_contra hne'
  have h1 := hmin v' (Finset.mem_filter.2 ⟨hv', htrans _ _ _ hR hm.2⟩)
  have hsub : Finset.univ.filter (fun y => Lt R y v') ⊆ Finset.univ.filter (fun y => Lt R y m) := by
    rw [Finset.subset_iff]
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨Finset.mem_univ _, htrans _ _ _ hy.2.1 hR, fun e => hne' (hanti _ _ hR (e ▸ hy.2.1))⟩
  have hlt : (Finset.univ.filter (fun y => Lt R y v')).card < (Finset.univ.filter (fun y => Lt R y m)).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨v', ?_, ?_⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hR, hne'⟩
    · exact fun h => (Finset.mem_filter.1 h).2.2 rfl
  omega

theorem antichain (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hanti : ∀ x y, R x y → R y x → x = y) : ∀ n (p : Fin (d+1)), (U R p).card ≤ n →
    ∀ M : Finset (Fin (d+1)), (∀ m ∈ M, ∀ m' ∈ M, R m m' → m = m') →
    ((∀ m ∈ M, R p m) → M.sum (pth R d) ≤ pth R d p) ∧
    ((∀ m ∈ M, Lt R p m) → 1 + M.sum (pth R d) ≤ pth R d p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hp M hM
  have strict : (∀ m ∈ M, Lt R p m) → 1 + M.sum (pth R d) ≤ pth R d p := by
    intro hlt
    let c : Fin (d+1) → Fin (d+1) := fun m =>
      if h : Lt R p m then Classical.choose (cover_below hrefl htrans hanti h) else p
    have hc : ∀ m ∈ M, Nx R p (c m) ∧ R (c m) m := by
      intro m hm
      simp only [c, dif_pos (hlt m hm)]
      exact Classical.choose_spec (cover_below hrefl htrans hanti (hlt m hm))
    have hmaps : ∀ m ∈ M, c m ∈ Finset.univ.filter (Nx R p) := fun m hm =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, (hc m hm).1⟩
    have fib : ∀ w ∈ Finset.univ.filter (Nx R p), (M.filter (fun m => c m = w)).sum (pth R d) ≤ pth R d w := by
      intro w hw
      rw [Finset.mem_filter] at hw
      have hlt2 := U_lt htrans hanti hw.2.1
      refine (ih (U R w).card (by omega) w le_rfl (M.filter (fun m => c m = w)) ?_).1 ?_
      · intro m hm m' hm' h
        exact hM m (Finset.mem_filter.1 hm).1 m' (Finset.mem_filter.1 hm').1 h
      · intro m hm
        have hm2 := Finset.mem_filter.1 hm
        rw [← hm2.2]
        exact (hc m hm2.1).2
    have e1 : M.sum (pth R d) = (Finset.univ.filter (Nx R p)).sum
        (fun w => (M.filter (fun m => c m = w)).sum (pth R d)) :=
      (Finset.sum_fiberwise_of_maps_to hmaps (pth R d)).symm
    rw [e1, P_rec htrans hanti p]
    exact Nat.add_le_add_left (Finset.sum_le_sum fib) 1
  refine ⟨fun hR => ?_, strict⟩
  by_cases hpM : p ∈ M
  · have hMp : M = {p} := by
      ext m
      rw [Finset.mem_singleton]
      constructor
      · intro hm; exact (hM p hpM m hm (hR m hm)).symm
      · rintro rfl; exact hpM
    rw [hMp, Finset.sum_singleton]
  · have := strict (fun m hm => ⟨hR m hm, fun e => hpM (e ▸ hm)⟩)
    omega

theorem forest_mono {n : ℕ} {V W : Finset (Finset (Fin n))} (h : W ⊆ V) (hV : Forest V) : Forest W :=
  fun x hx y hy z hz => hV x (h hx) y (h hy) z (h hz)

theorem compact (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hanti : ∀ x y, R x y → R y x → x = y) : ∀ (N n : ℕ) (V : Finset (Finset (Fin n)))
    (ok : Finset (Fin n) → Fin (d+1) → Prop) (p : Fin (d+1)), V.card ≤ N → Forest V → ¬ Fit R V ok p →
    ∃ S ⊆ V, S.card ≤ pth R d p ∧ ¬ Fit R S ok p := by
  intro N
  induction N with
  | zero =>
    intro n V ok p hc _ hnf
    exfalso
    apply hnf
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hc)]
    exact ⟨fun _ => p, fun x hx => absurd hx (Finset.notMem_empty _), fun x hx => absurd hx (Finset.notMem_empty _)⟩
  | succ N ih =>
  intro n V ok p hc hfor hnf
  by_cases hV : V = ∅
  · exfalso
    apply hnf
    rw [hV]
    exact ⟨fun _ => p, fun x hx => absurd hx (Finset.notMem_empty _), fun x hx => absurd hx (Finset.notMem_empty _)⟩
  obtain ⟨r, hr, hrmin⟩ := Finset.exists_min_image V Finset.card (Finset.nonempty_iff_ne_empty.2 hV)
  have rmin : ∀ y ∈ V, y ⊆ r → y = r := fun y hy hyr => Finset.eq_of_subset_of_card_le hyr (hrmin y hy)
  let T := V.filter (fun x => r ⊆ x)
  let V' := V.filter (fun x => ¬ r ⊆ x)
  have hT : T ⊆ V := Finset.filter_subset _ _
  have hV' : V' ⊆ V := Finset.filter_subset _ _
  by_cases hfV' : Fit R V' ok p
  swap
  · have hlt : V'.card < V.card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hV']
      refine ⟨r, hr, ?_⟩
      simp [V']
    obtain ⟨S, hS, h1, h2⟩ := ih n V' ok p (by omega) (forest_mono hV' hfor) hfV'
    exact ⟨S, hS.trans hV', h1, h2⟩
  have hfT : ¬ Fit R T ok p := by
    rintro ⟨f1, hf1a, hf1b⟩
    obtain ⟨f2, hf2a, hf2b⟩ := hfV'
    apply hnf
    refine ⟨fun x => if r ⊆ x then f1 x else f2 x, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
    · by_cases h : r ⊆ x
      · simp only [if_pos h]; exact hf1a x (Finset.mem_filter.2 ⟨hx, h⟩)
      · simp only [if_neg h]; exact hf2a x (Finset.mem_filter.2 ⟨hx, h⟩)
    · by_cases h1 : r ⊆ x
      · have h2 : r ⊆ y := h1.trans hxy
        simp only [if_pos h1, if_pos h2]
        exact hf1b x (Finset.mem_filter.2 ⟨hx, h1⟩) y (Finset.mem_filter.2 ⟨hy, h2⟩) hxy
      · by_cases h2 : r ⊆ y
        · exfalso
          rcases hfor y hy r hr x hx h2 hxy with h3 | h3
          · exact h1 h3
          · exact h1 (by rw [rmin x hx h3])
        · simp only [if_neg h1, if_neg h2]
          exact hf2b x (Finset.mem_filter.2 ⟨hx, h1⟩) y (Finset.mem_filter.2 ⟨hy, h2⟩) hxy
  let T' := T.erase r
  have hT'T : T' ⊆ T := Finset.erase_subset _ _
  have hrT : r ∈ T := Finset.mem_filter.2 ⟨hr, subset_refl _⟩
  have hcardT' : T'.card ≤ N := by
    have : T'.card < V.card := lt_of_lt_of_le (Finset.card_erase_lt_of_mem hrT) (Finset.card_le_card hT)
    omega
  have hforT' : Forest T' := forest_mono (hT'T.trans hT) hfor
  by_cases hfT' : Fit R T' ok p
  swap
  · obtain ⟨S, hS, h1, h2⟩ := ih n T' ok p hcardT' hforT' hfT'
    exact ⟨S, hS.trans (hT'T.trans hT), h1, h2⟩
  have ext : ∀ v, R p v → ok r v → Fit R T' ok v → Fit R T ok p := by
    rintro v hpv hov ⟨g, hga, hgb⟩
    refine ⟨fun x => if x = r then v else g x, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
    · by_cases h : x = r
      · simp only [if_pos h]; rw [h]; exact ⟨hpv, hov⟩
      · simp only [if_neg h]
        have hx' : x ∈ T' := Finset.mem_erase.2 ⟨h, hx⟩
        exact ⟨htrans _ _ _ hpv (hga x hx').1, (hga x hx').2⟩
    · by_cases h1 : x = r
      · by_cases h2 : y = r
        · simp only [if_pos h1, if_pos h2]; exact hrefl v
        · simp only [if_pos h1, if_neg h2]; exact (hga y (Finset.mem_erase.2 ⟨h2, hy⟩)).1
      · by_cases h2 : y = r
        · exfalso
          have hxr : x ⊆ r := h2 ▸ hxy
          have hrx : r ⊆ x := (Finset.mem_filter.1 hx).2
          exact h1 (Finset.Subset.antisymm hxr hrx)
        · simp only [if_neg h1, if_neg h2]
          exact hgb x (Finset.mem_erase.2 ⟨h1, hx⟩) y (Finset.mem_erase.2 ⟨h2, hy⟩) hxy
  have hnok : ¬ ok r p := fun h => hfT (ext p (hrefl p) h hfT')
  let A := Finset.univ.filter (fun v => R p v ∧ ok r v)
  have hfail : ∀ v ∈ A, ¬ Fit R T' ok v := by
    intro v hv hf
    have hv' := (Finset.mem_filter.1 hv).2
    exact hfT (ext v hv'.1 hv'.2 hf)
  have wit : ∀ v ∈ A, ∃ S ⊆ T', S.card ≤ pth R d v ∧ ¬ Fit R S ok v :=
    fun v hv => ih n T' ok v hcardT' hforT' (hfail v hv)
  let Sv : Fin (d+1) → Finset (Finset (Fin n)) := fun v => if h : v ∈ A then Classical.choose (wit v h) else ∅
  have hSv : ∀ v ∈ A, Sv v ⊆ T' ∧ (Sv v).card ≤ pth R d v ∧ ¬ Fit R (Sv v) ok v := by
    intro v hv
    have hs := Classical.choose_spec (wit v hv)
    simp only [Sv, dif_pos hv]
    exact ⟨hs.1, hs.2.1, hs.2.2⟩
  let M := A.filter (fun m => ∀ v' ∈ A, R v' m → v' = m)
  have hMA : ∀ m ∈ M, m ∈ A := fun m hm => (Finset.mem_filter.1 hm).1
  let S := insert r (M.biUnion Sv)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with h | h
    · rw [h]; exact hr
    · obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.1 h
      exact hT (hT'T ((hSv m (hMA m hm)).1 hxm))
  · have hac := (antichain hrefl htrans hanti d p (U_card_le p) M
      (fun m hm m' hm' h => (Finset.mem_filter.1 hm').2 m (hMA m hm) h)).2
      (fun m hm => ⟨(Finset.mem_filter.1 (hMA m hm)).2.1, fun e => hnok (by
        have hokm := (Finset.mem_filter.1 (hMA m hm)).2.2
        rw [e]; exact hokm)⟩)
    have h1 : S.card ≤ (M.biUnion Sv).card + 1 := Finset.card_insert_le _ _
    have h2 : (M.biUnion Sv).card ≤ M.sum (fun m => (Sv m).card) := Finset.card_biUnion_le
    have h3 : M.sum (fun m => (Sv m).card) ≤ M.sum (pth R d) :=
      Finset.sum_le_sum (fun m hm => (hSv m (hMA m hm)).2.1)
    omega
  · rintro ⟨f, hfa, hfb⟩
    have hrS : r ∈ S := Finset.mem_insert_self _ _
    have hu := hfa r hrS
    have huA : f r ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hu.1, hu.2⟩
    obtain ⟨m, hmA, hmu, hmmin⟩ := minimal_below hrefl htrans hanti A huA
    have hmM : m ∈ M := Finset.mem_filter.2 ⟨hmA, hmmin⟩
    apply (hSv m hmA).2.2
    have hsub : Sv m ⊆ S := fun x hx => Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨m, hmM, hx⟩)
    refine ⟨f, fun x hx => ⟨?_, (hfa x (hsub hx)).2⟩, fun x hx y hy hxy => hfb x (hsub hx) y (hsub hy) hxy⟩
    have hxT : x ∈ T := hT'T ((hSv m hmA).1 hx)
    exact htrans _ _ _ hmu (hfb r hrS x (hsub hx) (Finset.mem_filter.1 hxT).2)

end Poset

section Paths
open scoped Classical
variable {d : ℕ} {R : Fin (d+1) → Fin (d+1) → Prop}

noncomputable def pf (R : Fin (d+1) → Fin (d+1) → Prop) : ℕ → Fin (d+1) → Finset (List (Fin (d+1)))
  | 0, x => {[x]}
  | k+1, x => insert [x] ((Finset.univ.filter (Nx R x)).biUnion (fun y => (pf R k y).image (List.cons x)))

theorem mem_pf_succ {k : ℕ} {x : Fin (d+1)} {l : List (Fin (d+1))} :
    l ∈ pf R (k+1) x ↔ l = [x] ∨ ∃ y, Nx R x y ∧ ∃ t ∈ pf R k y, l = x :: t := by
  simp only [pf, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro (h | ⟨y, hy, t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, t, ht, rfl⟩
  · rintro (h | ⟨y, hy, t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, t, ht, rfl⟩

theorem pf_head : ∀ (k : ℕ) (x : Fin (d+1)), ∀ l ∈ pf R k x, ∃ t, l = x :: t := by
  intro k
  induction k with
  | zero =>
    intro x l hl
    simp only [pf, Finset.mem_singleton] at hl
    exact ⟨[], hl⟩
  | succ k ih =>
    intro x l hl
    rcases mem_pf_succ.1 hl with h | ⟨y, _, t, _, rfl⟩
    · exact ⟨[], h⟩
    · exact ⟨t, rfl⟩

theorem pf_card : ∀ (k : ℕ) (x : Fin (d+1)), (pf R k x).card = pth R k x := by
  intro k
  induction k with
  | zero => intro x; simp [pf, pth_zero]
  | succ k ih =>
    intro x
    rw [pf, Finset.card_insert_of_notMem, Finset.card_biUnion, pth_succ]
    · rw [Nat.add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.card_image_of_injective _ List.cons_injective, ih]
    · intro y _ y' _ hyy'
      rw [Function.onFun, Finset.disjoint_left]
      intro l hl hl'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hl
      obtain ⟨t', ht', e⟩ := Finset.mem_image.1 hl'
      have e2 : t' = t := List.cons_injective e
      obtain ⟨s, rfl⟩ := pf_head k y t ht
      obtain ⟨s', rfl⟩ := pf_head k y' t' ht'
      exact hyy' (List.cons.inj e2).1.symm
    · intro hm
      obtain ⟨y, _, hl⟩ := Finset.mem_biUnion.1 hm
      obtain ⟨t, ht, e⟩ := Finset.mem_image.1 hl
      obtain ⟨s, rfl⟩ := pf_head k y t ht
      have := (List.cons.inj e).2
      exact List.cons_ne_nil _ _ this

noncomputable def last0 (l : List (Fin (d+1))) : Fin (d+1) := l.getLastD 0

theorem last0_single (x : Fin (d+1)) : last0 [x] = x := by simp [last0]

theorem last0_cons (x y : Fin (d+1)) (s : List (Fin (d+1))) : last0 (x :: y :: s) = last0 (y :: s) := by
  simp only [last0, List.getLastD_cons]

theorem last_ge (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z) :
    ∀ (k : ℕ) (x : Fin (d+1)), ∀ l ∈ pf R k x, R x (last0 l) := by
  intro k
  induction k with
  | zero =>
    intro x l hl
    simp only [pf, Finset.mem_singleton] at hl
    rw [hl, last0_single]; exact hrefl x
  | succ k ih =>
    intro x l hl
    rcases mem_pf_succ.1 hl with h | ⟨y, hy, t, ht, rfl⟩
    · rw [h, last0_single]; exact hrefl x
    · obtain ⟨s, rfl⟩ := pf_head k y t ht
      rw [last0_cons]
      exact htrans _ _ _ hy.1.1 (ih y _ ht)

def LFit (R : Fin (d+1) → Fin (d+1) → Prop) (T : Finset (List (Fin (d+1)))) (u : Fin (d+1)) : Prop :=
  ∃ g : List (Fin (d+1)) → Fin (d+1), (∀ l ∈ T, R u (g l) ∧ g l ≠ last0 l) ∧
    ∀ l ∈ T, ∀ l' ∈ T, l <+: l' → R (g l) (g l')

theorem covers_incomp (hanti : ∀ x y, R x y → R y x → x = y) {x y w : Fin (d+1)}
    (hy : Nx R x y) (hw : Nx R x w) (hne : y ≠ w) : ¬ R y w := by
  intro h
  exact hw.2 ⟨y, hy.1, h, hne⟩

theorem cover_not_le (hanti : ∀ x y, R x y → R y x → x = y) {x y : Fin (d+1)} (hy : Nx R x y) : ¬ R y x :=
  fun h => hy.1.2 (hanti _ _ hy.1.1 h)

theorem sharp (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hanti : ∀ x y, R x y → R y x → x = y) : ∀ (k : ℕ) (x : Fin (d+1)), (U R x).card ≤ k →
    (∀ u, LFit R (pf R k x) u ↔ ¬ R x u) ∧ ∀ l ∈ pf R k x, LFit R ((pf R k x).erase l) x := by
  have easy : ∀ k x u, ¬ R x u → LFit R (pf R k x) u := by
    intro k x u hxu
    refine ⟨fun _ => u, fun l hl => ⟨hrefl u, fun e => hxu (by
      have h := last_ge hrefl htrans k x l hl
      rw [← show u = last0 l from e] at h
      exact h)⟩,
      fun _ _ _ _ _ => hrefl u⟩
  intro k
  induction k with
  | zero =>
    intro x hx
    have hU : U R x = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hx)
    have hmax : ∀ v, R x v → v = x := by
      intro v hv
      by_contra hne
      have hv' : v ∈ U R x := by
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hv, fun e => hne e.symm⟩
      rw [hU] at hv'
      exact Finset.notMem_empty _ hv'
    refine ⟨fun u => ⟨fun ⟨g, hg, _⟩ hxu => ?_, easy 0 x u⟩, fun l hl => ?_⟩
    · have h1 := hg [x] (by simp [pf])
      rw [last0_single] at h1
      exact h1.2 (hmax _ (htrans _ _ _ hxu h1.1))
    · simp only [pf, Finset.mem_singleton] at hl
      subst hl
      refine ⟨fun _ => x, fun l hl => ?_, fun l hl => ?_⟩
      · simp [pf] at hl
      · simp [pf] at hl
  | succ k ih =>
    intro x hx
    have ihy : ∀ y, Nx R x y → (U R y).card ≤ k := fun y hy => by
      have := U_lt htrans hanti hy.1; omega
    refine ⟨fun u => ⟨fun ⟨g, hg, hmono⟩ hxu => ?_, easy (k+1) x u⟩, fun l0 hl0 => ?_⟩
    · have hroot : [x] ∈ pf R (k+1) x := mem_pf_succ.2 (Or.inl rfl)
      have h1 := hg [x] hroot
      rw [last0_single] at h1
      obtain ⟨w, hw, hwv⟩ := cover_below hrefl htrans hanti ⟨htrans _ _ _ hxu h1.1, fun e => h1.2 e.symm⟩
      have hno := ((ih w (ihy w hw)).1 w).1
      apply hno ?_ (hrefl w)
      refine ⟨fun t => g (x :: t), fun t ht => ?_, fun t ht t' ht' htt => ?_⟩
      · have hmem : x :: t ∈ pf R (k+1) x := mem_pf_succ.2 (Or.inr ⟨w, hw, t, ht, rfl⟩)
        have h2 := hg _ hmem
        obtain ⟨s, rfl⟩ := pf_head k w t ht
        rw [last0_cons] at h2
        exact ⟨htrans _ _ _ hwv (hmono [x] hroot _ hmem ⟨w :: s, rfl⟩), h2.2⟩
      · exact hmono _ (mem_pf_succ.2 (Or.inr ⟨w, hw, t, ht, rfl⟩)) _
          (mem_pf_succ.2 (Or.inr ⟨w, hw, t', ht', rfl⟩)) (List.cons_prefix_cons.2 ⟨rfl, htt⟩)
    ·
      have fitx : ∀ y, Nx R x y → LFit R (pf R k y) x := fun y hy =>
        ((ih y (ihy y hy)).1 x).2 (cover_not_le hanti hy)
      rcases mem_pf_succ.1 hl0 with h0 | ⟨w, hw, t0, ht0, rfl⟩
      · subst h0
        let G : Fin (d+1) → List (Fin (d+1)) → Fin (d+1) := fun y =>
          if h : Nx R x y then Classical.choose (fitx y h) else fun _ => x
        have hG : ∀ y (hy : Nx R x y), G y = Classical.choose (fitx y hy) := fun y hy => by
          simp only [G, dif_pos hy]
        refine ⟨fun l => G (l.tail.headD x) l.tail, fun l hl => ?_, fun l hl l' hl' hll => ?_⟩
        · obtain ⟨hne, hl⟩ := Finset.mem_erase.1 hl
          rcases mem_pf_succ.1 hl with h | ⟨y, hy, t, ht, rfl⟩
          · exact absurd h hne
          · obtain ⟨s, rfl⟩ := pf_head k y t ht
            have hs := (Classical.choose_spec (fitx y hy)).1 _ ht
            simp only [List.tail_cons, List.headD_cons, last0_cons]
            rw [hG y hy]
            exact hs
        · obtain ⟨hne, hl⟩ := Finset.mem_erase.1 hl
          obtain ⟨hne', hl'⟩ := Finset.mem_erase.1 hl'
          rcases mem_pf_succ.1 hl with h | ⟨y, hy, t, ht, rfl⟩
          · exact absurd h hne
          rcases mem_pf_succ.1 hl' with h' | ⟨y', hy', t', ht', rfl⟩
          · exact absurd h' hne'
          obtain ⟨s, rfl⟩ := pf_head k y t ht
          obtain ⟨s', rfl⟩ := pf_head k y' t' ht'
          have htt := (List.cons_prefix_cons.1 hll).2
          have hyy : y = y' := (List.cons_prefix_cons.1 htt).1
          subst hyy
          simp only [List.tail_cons, List.headD_cons]
          rw [hG y hy]
          exact (Classical.choose_spec (fitx y hy)).2 _ ht _ ht' htt
      ·
        have fitw : LFit R ((pf R k w).erase t0) w := (ih w (ihy w hw)).2 t0 ht0
        have fitsib : ∀ y, Nx R x y → y ≠ w → LFit R (pf R k y) w := fun y hy hne =>
          ((ih y (ihy y hy)).1 w).2 (covers_incomp hanti hy hw hne)
        obtain ⟨gw, hgwa, hgwb⟩ := fitw
        let G : Fin (d+1) → List (Fin (d+1)) → Fin (d+1) := fun y =>
          if h : Nx R x y ∧ y ≠ w then Classical.choose (fitsib y h.1 h.2) else fun _ => w
        have hG : ∀ y (hy : Nx R x y) (hne : y ≠ w), G y = Classical.choose (fitsib y hy hne) := fun y hy hne => by
          simp only [G, dif_pos (And.intro hy hne)]
        let g : List (Fin (d+1)) → Fin (d+1) := fun l =>
          if l = [x] then w else if l.tail.headD x = w then gw l.tail else G (l.tail.headD x) l.tail
        have gval : ∀ y, Nx R x y → ∀ t ∈ pf R k y, x :: t ≠ x :: t0 →
            R w (g (x :: t)) ∧ g (x :: t) ≠ last0 (x :: t) := by
          intro y hy t ht hne
          obtain ⟨s, rfl⟩ := pf_head k y t ht
          have hnr : (x :: y :: s) ≠ [x] := by simp
          simp only [g, if_neg hnr, List.tail_cons, List.headD_cons, last0_cons]
          by_cases hyw : y = w
          · subst hyw
            simp only [↓reduceIte]
            have hmem : y :: s ∈ (pf R k y).erase t0 :=
              Finset.mem_erase.2 ⟨fun e => hne (by rw [e]), ht⟩
            exact hgwa _ hmem
          · simp only [hyw, ↓reduceIte]
            rw [hG y hy hyw]
            exact (Classical.choose_spec (fitsib y hy hyw)).1 _ ht
        refine ⟨g, fun l hl => ?_, fun l hl l' hl' hll => ?_⟩
        · obtain ⟨hne, hl⟩ := Finset.mem_erase.1 hl
          rcases mem_pf_succ.1 hl with h | ⟨y, hy, t, ht, rfl⟩
          · subst h
            simp only [g, if_pos rfl, last0_single]
            exact ⟨hw.1.1, fun e => hw.1.2 e.symm⟩
          · have := gval y hy t ht hne
            exact ⟨htrans _ _ _ hw.1.1 this.1, this.2⟩
        · obtain ⟨hne, hl⟩ := Finset.mem_erase.1 hl
          obtain ⟨hne', hl'⟩ := Finset.mem_erase.1 hl'
          rcases mem_pf_succ.1 hl' with h' | ⟨y', hy', t', ht', rfl⟩
          · subst h'
            rcases mem_pf_succ.1 hl with h | ⟨y, hy, t, ht, rfl⟩
            · subst h; exact hrefl _
            · exfalso
              obtain ⟨s, rfl⟩ := pf_head k y t ht
              have := hll.length_le
              simp at this
          rcases mem_pf_succ.1 hl with h | ⟨y, hy, t, ht, rfl⟩
          · subst h
            have hgx : g [x] = w := by simp only [g, if_pos rfl]
            rw [hgx]
            exact (gval y' hy' t' ht' hne').1
          · obtain ⟨s, rfl⟩ := pf_head k y t ht
            obtain ⟨s', rfl⟩ := pf_head k y' t' ht'
            have htt := (List.cons_prefix_cons.1 hll).2
            have hyy : y = y' := (List.cons_prefix_cons.1 htt).1
            subst hyy
            have hnr : (x :: y :: s) ≠ [x] := by simp
            have hnr' : (x :: y :: s') ≠ [x] := by simp
            simp only [g, if_neg hnr, if_neg hnr', List.tail_cons, List.headD_cons]
            by_cases hyw : y = w
            · subst hyw
              simp only [↓reduceIte]
              exact hgwb _ (Finset.mem_erase.2 ⟨fun e => hne (by rw [e]), ht⟩) _
                (Finset.mem_erase.2 ⟨fun e => hne' (by rw [e]), ht'⟩) htt
            · simp only [hyw, ↓reduceIte]
              rw [hG y hy hyw]
              exact (Classical.choose_spec (fitsib y hy hyw)).2 _ ht _ ht' htt

end Paths

section Final
open scoped Classical
variable {d : ℕ} {R : Fin (d+1) → Fin (d+1) → Prop}

theorem part1 (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hanti : ∀ x y, R x y → R y x → x = y) : ∀ (n : ℕ) (V : Finset (Finset (Fin n)))
    (ok : Finset (Fin n) → Fin (d+1) → Prop) (p : Fin (d+1)), Forest V →
    (Fit R V ok p ↔ ∀ S ⊆ V, S.card ≤ pth R d p → Fit R S ok p) := by
  intro n V ok p hV
  constructor
  · rintro ⟨f, hf1, hf2⟩ S hS _
    exact ⟨f, fun x hx => hf1 x (hS hx), fun x hx y hy h => hf2 x (hS hx) y (hS hy) h⟩
  · intro h
    by_contra hn
    obtain ⟨S, hS, h1, h2⟩ := compact hrefl htrans hanti V.card n V ok p le_rfl hV hn
    exact h2 (h S hS h1)

theorem prefix_antisymm {l l' : List (Fin (d+1))} (h1 : l <+: l') (h2 : l' <+: l) : l = l' :=
  h1.eq_of_length (le_antisymm h1.length_le h2.length_le)

noncomputable def anc {N : ℕ} (S : Finset (List (Fin (d+1)))) (e : S ≃ Fin N) (l : List (Fin (d+1))) :
    Finset (Fin N) :=
  Finset.univ.filter (fun i => (e.symm i).1 <+: l)

theorem mem_anc {N : ℕ} {S : Finset (List (Fin (d+1)))} (e : S ≃ Fin N) (l : List (Fin (d+1))) (i : Fin N) :
    i ∈ anc S e l ↔ (e.symm i).1 <+: l := by
  unfold anc
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem self_mem_anc {N : ℕ} {S : Finset (List (Fin (d+1)))} (e : S ≃ Fin N) {l : List (Fin (d+1))}
    (hl : l ∈ S) : e ⟨l, hl⟩ ∈ anc S e l := by
  have h : e.symm (e ⟨l, hl⟩) = ⟨l, hl⟩ := e.symm_apply_apply _
  rw [mem_anc, h]

theorem anc_sub_iff {N : ℕ} {S : Finset (List (Fin (d+1)))} (e : S ≃ Fin N) {l l' : List (Fin (d+1))}
    (hl : l ∈ S) (hl' : l' ∈ S) : anc S e l ⊆ anc S e l' ↔ l <+: l' := by
  constructor
  · intro h
    have h1 := h (self_mem_anc e hl)
    rw [mem_anc, e.symm_apply_apply] at h1
    exact h1
  · intro h i hi
    rw [mem_anc] at hi ⊢
    exact hi.trans h

theorem anc_inj {N : ℕ} {S : Finset (List (Fin (d+1)))} (e : S ≃ Fin N) {l l' : List (Fin (d+1))}
    (h : anc S e l = anc S e l') (hl : l ∈ S) (hl' : l' ∈ S) : l = l' :=
  prefix_antisymm ((anc_sub_iff e hl hl').1 (fun i hi => h ▸ hi))
    ((anc_sub_iff e hl' hl).1 (fun i hi => h.symm ▸ hi))

noncomputable def dec {N : ℕ} {S : Finset (List (Fin (d+1)))} (e : S ≃ Fin N) (X : Finset (Fin N)) :
    List (Fin (d+1)) :=
  if h : ∃ l ∈ S, anc S e l = X then Classical.choose h else []

theorem dec_anc {N : ℕ} {S : Finset (List (Fin (d+1)))} (e : S ≃ Fin N) {l : List (Fin (d+1))}
    (hl : l ∈ S) : dec e (anc S e l) = l := by
  have h : ∃ l' ∈ S, anc S e l' = anc S e l := ⟨l, hl, rfl⟩
  rw [dec, dif_pos h]
  have hs := Classical.choose_spec h
  exact anc_inj e hs.2 hs.1 hl

theorem fit_iff {N : ℕ} {S : Finset (List (Fin (d+1)))} (e : S ≃ Fin N) [DecidableEq (Finset (Fin N))]
    {T : Finset (List (Fin (d+1)))} (hT : T ⊆ S) (u : Fin (d+1)) :
    Fit R (T.image (anc S e)) (fun x z => z ≠ last0 (dec e x)) u ↔ LFit R T u := by
  constructor
  · rintro ⟨f, hf1, hf2⟩
    refine ⟨fun l => f (anc S e l), fun l hl => ?_, fun l hl l' hl' h => ?_⟩
    · have h1 := hf1 _ (Finset.mem_image_of_mem _ hl)
      simp only [dec_anc e (hT hl)] at h1
      exact h1
    · exact hf2 _ (Finset.mem_image_of_mem _ hl) _ (Finset.mem_image_of_mem _ hl')
        ((anc_sub_iff e (hT hl) (hT hl')).2 h)
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨fun X => g (dec e X), fun X hX => ?_, fun X hX Y hY h => ?_⟩
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hX
      simp only [dec_anc e (hT hl)]
      exact hg1 l hl
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hX
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 hY
      simp only [dec_anc e (hT hl), dec_anc e (hT hl')]
      exact hg2 l hl l' hl' ((anc_sub_iff e (hT hl) (hT hl')).1 h)

theorem erase_image {N : ℕ} {S : Finset (List (Fin (d+1)))} (e : S ≃ Fin N) [DecidableEq (Finset (Fin N))]
    {l : List (Fin (d+1))} (hl : l ∈ S) :
    (S.image (anc S e)).erase (anc S e l) = (S.erase l).image (anc S e) := by
  ext Y
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hne, m, hm, rfl⟩
    exact ⟨m, ⟨fun h => hne (by rw [h]), hm⟩, rfl⟩
  · rintro ⟨m, ⟨hne, hm⟩, rfl⟩
    exact ⟨fun h => hne (anc_inj e h hm hl), m, hm, rfl⟩

theorem forest_image {N : ℕ} {S : Finset (List (Fin (d+1)))} (e : S ≃ Fin N) [DecidableEq (Finset (Fin N))] :
    Forest (S.image (anc S e)) := by
  intro X hX Y hY Z hZ hYX hZX
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hX
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hY
  obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hZ
  rw [anc_sub_iff e hm hl] at hYX
  rw [anc_sub_iff e hm' hl] at hZX
  rcases List.prefix_or_prefix_of_prefix hYX hZX with h | h
  · exact Or.inl ((anc_sub_iff e hm hm').2 h)
  · exact Or.inr ((anc_sub_iff e hm' hm).2 h)

theorem part2 (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hanti : ∀ x y, R x y → R y x → x = y) (p : Fin (d+1)) [DecidableEq (Finset (Fin (pth R d p)))] :
    ∃ (V : Finset (Finset (Fin (pth R d p)))) (ban : Finset (Fin (pth R d p)) → Fin (d+1)),
      Forest V ∧ V.card = pth R d p ∧ (∀ u, Fit R V (fun x z => z ≠ ban x) u ↔ ¬ R p u) ∧
      ∀ x ∈ V, Fit R (V.erase x) (fun x z => z ≠ ban x) p := by
  let S := pf R d p
  have hcard : S.card = pth R d p := pf_card d p
  let e : S ≃ Fin (pth R d p) := S.equivFin.trans (finCongr hcard)
  have hsh := sharp hrefl htrans hanti d p (U_card_le p)
  refine ⟨S.image (anc S e), fun X => last0 (dec e X), forest_image e, ?_, fun u => ?_, fun X hX => ?_⟩
  · rw [Finset.card_image_of_injOn (fun a ha b hb h => anc_inj e h (Finset.mem_coe.1 ha) (Finset.mem_coe.1 hb))]
    exact hcard
  · exact (fit_iff e (Finset.Subset.refl _) u).trans (hsh.1 u)
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hX
    rw [erase_image e hl]
    exact (fit_iff e (Finset.erase_subset _ _) p).2 (hsh.2 l hl)

end Final

end PEqualNP.Outside.L_lib_1363_aux

theorem PEqualNP.Outside.L_lib_1363 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (d : Nat) (R : Fin (d+1) → Fin (d+1) → Prop),
  (∀ x, R x x) → (∀ x y z, R x y → R y z → R x z) →
  (∀ x y, R x y → R y x → x = y) →
  let lt := fun x y => R x y ∧ x ≠ y
  let next := fun x y => lt x y ∧ ¬ ∃ z, lt x z ∧ lt z y
  let paths := Nat.rec (motive := fun _ => Fin (d+1) → Nat) (fun _ => 1)
    (fun _ prev x => 1 + (Finset.univ.filter (next x)).sum prev) d
  let forest := fun (n : Nat) (V : Finset (Finset (Fin n))) =>
    ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, y ⊆ x → z ⊆ x → y ⊆ z ∨ z ⊆ y
  let fit := fun (n : Nat) (V : Finset (Finset (Fin n)))
      (ok : Finset (Fin n) → Fin (d+1) → Prop) (p : Fin (d+1)) =>
    ∃ f : Finset (Fin n) → Fin (d+1),
      (∀ x ∈ V, R p (f x) ∧ ok x (f x)) ∧
      ∀ x ∈ V, ∀ y ∈ V, x ⊆ y → R (f x) (f y)
  (∀ (n : Nat) (V : Finset (Finset (Fin n))) (ok : Finset (Fin n) → Fin (d+1) → Prop)
      (p : Fin (d+1)), forest n V →
    (fit n V ok p ↔ ∀ S ⊆ V, S.card ≤ paths p → fit n S ok p)) ∧
  ∀ p : Fin (d+1), ∃ (V : Finset (Finset (Fin (paths p)))) (ban : Finset (Fin (paths p)) → Fin (d+1)),
    let ok := fun x z => z ≠ ban x
    forest (paths p) V ∧ V.card = paths p ∧
    (∀ u, fit (paths p) V ok u ↔ ¬ R p u) ∧
    ∀ x ∈ V, fit (paths p) (V.erase x) ok p) := by
  intro d R hrefl htrans hanti lt next paths forest fit
  refine ⟨fun n V ok p hV => ?_, fun p => ?_⟩
  · exact PEqualNP.Outside.L_lib_1363_aux.part1 hrefl htrans hanti n V ok p hV
  · obtain ⟨V, ban, h1, h2, h3, h4⟩ := @PEqualNP.Outside.L_lib_1363_aux.part2 d R hrefl htrans hanti p
      (fun a b => Classical.propDecidable (a = b))
    exact ⟨V, ban, h1, h2, h3, h4⟩

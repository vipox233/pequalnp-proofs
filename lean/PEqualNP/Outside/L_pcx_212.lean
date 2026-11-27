import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_212_aux

open PEqualNP.ProofComplexity

private def cl {m n : ℕ} (left right : Fin m → Fin n) (e : Fin m) (b : Bool) : Clause (Fin n) :=
  {(left e, b), (right e, b)}

private def form {m n : ℕ} (left right : Fin m → Fin n) : Set (Clause (Fin n)) :=
  {C | ∃ e b, C = cl left right e b}

private def IsWalk {m n : ℕ} (left right : Fin m → Fin n) (P : Fin m → Prop)
    (g : ℕ) (edges : Fin g → Fin m) (x : Fin (g + 1) → Fin n) : Prop :=
  x 0 = x (Fin.last g) ∧
  (∀ j : Fin g, P (edges j)) ∧
  (∀ j : Fin g,
    (x j.castSucc = left (edges j) ∧ x j.succ = right (edges j)) ∨
    (x j.castSucc = right (edges j) ∧ x j.succ = left (edges j)))

private theorem cl_eq_of_edge {m n : ℕ} (left right : Fin m → Fin n)
    {e : Fin m} {u v : Fin n} (b : Bool)
    (h : (u = left e ∧ v = right e) ∨ (u = right e ∧ v = left e)) :
    cl left right e b = {(u, b), (v, b)} := by
  unfold cl
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · ext z; simp [or_comm]

private theorem isWalk_sub_slice {m n : ℕ} {left right : Fin m → Fin n} {P : Fin m → Prop}
    {g : ℕ} {edges : Fin g → Fin m} {x : Fin (g + 1) → Fin n}
    (hw : IsWalk left right P g edges x)
    {a b : ℕ} (hab : a < b) (hbg : b < g)
    (hxe : x ⟨a, by omega⟩ = x ⟨b, by omega⟩) :
    (∃ edges' : Fin (b - a) → Fin m, ∃ x' : Fin (b - a + 1) → Fin n,
      IsWalk left right P (b - a) edges' x') ∧
    (∃ edges' : Fin (g - (b - a)) → Fin m, ∃ x' : Fin (g - (b - a) + 1) → Fin n,
      IsWalk left right P (g - (b - a)) edges' x') := by
  obtain ⟨hclose, hP, hedge⟩ := hw
  constructor
  · refine ⟨fun j => edges ⟨a + j.val, by omega⟩, fun k => x ⟨a + k.val, by omega⟩, ?_, ?_, ?_⟩
    · simp only [Fin.val_zero, add_zero, Fin.val_last]
      convert hxe using 2
      ext; dsimp; omega
    · intro j; exact hP ⟨a + j.val, by omega⟩
    · intro j
      dsimp only
      have h := hedge ⟨a + j.val, by omega⟩
      have hc : (⟨a + j.castSucc.val, by omega⟩ : Fin (g + 1)) = (⟨a + j.val, by omega⟩ : Fin g).castSucc := by
        ext; simp
      have hs : (⟨a + j.succ.val, by omega⟩ : Fin (g + 1)) = (⟨a + j.val, by omega⟩ : Fin g).succ := by
        ext; simp; omega
      rw [hc, hs]; exact h
  · let d := b - a
    let t := g - d
    let idxE : Fin t → Fin g := fun j =>
      if h : j.val < a then ⟨j.val, by omega⟩ else ⟨j.val + d, by omega⟩
    let idxV : Fin (t + 1) → Fin (g + 1) := fun k =>
      if h : k.val < a then ⟨k.val, by omega⟩ else ⟨k.val + d, by omega⟩
    have hVlast : idxV (Fin.last t) = Fin.last g := by
      dsimp only [idxV]
      have h1 : ¬ (Fin.last t).val < a := by simp only [Fin.val_last]; omega
      simp only [h1, ↓reduceDIte]
      ext; simp only [Fin.val_last]; dsimp [t, d]; omega
    refine ⟨fun j => edges (idxE j), fun k => x (idxV k), ?_, ?_, ?_⟩
    · dsimp only
      rw [hVlast]
      by_cases ha0 : 0 < a
      · have hV0 : idxV 0 = 0 := by
          dsimp only [idxV]; simp only [Fin.val_zero, ha0, ↓reduceDIte]; rfl
        rw [hV0]; exact hclose
      · have ha : a = 0 := by omega
        have hV0 : idxV 0 = ⟨b, by omega⟩ := by
          dsimp only [idxV]
          have h0 : ¬ (0 : ℕ) < a := by omega
          simp only [Fin.val_zero, h0, ↓reduceDIte]
          ext; dsimp [d]; omega
        have h0a : (0 : Fin (g + 1)) = ⟨a, by omega⟩ := by ext; simp [ha]
        rw [hV0, ← hclose, h0a, hxe]
    · intro j; exact hP (idxE j)
    · intro j
      dsimp only
      have h := hedge (idxE j)
      by_cases hj : j.val < a
      · have hE : idxE j = ⟨j.val, by omega⟩ := by simp [idxE, hj]
        have hV1 : idxV j.castSucc = (⟨j.val, by omega⟩ : Fin g).castSucc := by
          ext; simp [idxV, hj]
        by_cases hj1 : j.val + 1 < a
        · have hV2 : idxV j.succ = (⟨j.val, by omega⟩ : Fin g).succ := by
            ext; simp [idxV, hj1]
          rw [hE] at h; rw [hE, hV1, hV2]; exact h
        · have hja : j.val + 1 = a := by omega
          have hV2 : idxV j.succ = ⟨b, by omega⟩ := by
            ext; simp [idxV, hj1]; dsimp [d]; omega
          have hVs : (⟨j.val, by omega⟩ : Fin g).succ = ⟨a, by omega⟩ := by ext; simp [hja]
          rw [hE] at h; rw [hE, hV1, hV2, ← hxe, ← hVs]; exact h
      · have hE : idxE j = ⟨j.val + d, by omega⟩ := by simp [idxE, hj]
        have hj1 : ¬ j.val + 1 < a := by omega
        have hV1 : idxV j.castSucc = (⟨j.val + d, by omega⟩ : Fin g).castSucc := by
          ext; simp [idxV, hj]
        have hV2 : idxV j.succ = (⟨j.val + d, by omega⟩ : Fin g).succ := by
          ext; simp [idxV, hj1]; omega
        rw [hE] at h; rw [hE, hV1, hV2]; exact h

private theorem minimal_odd_walk {m n : ℕ} {left right : Fin m → Fin n} {P : Fin m → Prop}
    {g : ℕ} {edges : Fin g → Fin m} {x : Fin (g + 1) → Fin n}
    (hg : Odd g) (hw : IsWalk left right P g edges x) :
    ∃ (t : ℕ) (edges' : Fin t → Fin m) (x' : Fin (t + 1) → Fin n),
      t ≤ g ∧ Odd t ∧ IsWalk left right P t edges' x' ∧
      Function.Injective (fun j : Fin t => x' j.castSucc) := by
  classical
  let Q : ℕ → Prop := fun t => Odd t ∧ ∃ (e : Fin t → Fin m) (y : Fin (t + 1) → Fin n),
    IsWalk left right P t e y
  have hex : ∃ t, Q t := ⟨g, hg, edges, x, hw⟩
  let t := Nat.find hex
  have htQ : Q t := Nat.find_spec hex
  have htg : t ≤ g := Nat.find_min' hex ⟨hg, edges, x, hw⟩
  obtain ⟨ht_odd, edges', x', hw'⟩ := htQ
  refine ⟨t, edges', x', htg, ht_odd, hw', ?_⟩
  intro a b hab
  by_contra hne
  have hlt_or : a.val < b.val ∨ b.val < a.val := Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h))
  have hcontra : ∀ (u v : Fin t), u.val < v.val → x' u.castSucc = x' v.castSucc → False := by
    intro u v huv hxuv
    have hxuv' : x' ⟨u.val, by omega⟩ = x' ⟨v.val, by omega⟩ := hxuv
    obtain ⟨hsub1, hsub2⟩ := isWalk_sub_slice hw' huv v.isLt hxuv'
    by_cases hodd : Odd (v.val - u.val)
    · exact Nat.find_min hex (show v.val - u.val < t by omega) ⟨hodd, hsub1⟩
    · have heven : Even (v.val - u.val) := Nat.not_odd_iff_even.mp hodd
      have hodd2 : Odd (t - (v.val - u.val)) := by
        obtain ⟨k1, hk1⟩ := ht_odd
        obtain ⟨k2, hk2⟩ := heven
        refine ⟨k1 - k2, ?_⟩; omega
      exact Nat.find_min hex (show t - (v.val - u.val) < t by omega) ⟨hodd2, hsub2⟩
  rcases hlt_or with h | h
  · exact hcontra a b h hab
  · exact hcontra b a h hab.symm

private theorem isResolvent_pair {V : Type} [DecidableEq V]
    {a b c : V} {sa sb : Bool} (hab : a ≠ b) (hbc : b ≠ c) :
    IsResolvent ({(a, sa), (b, sb)} : Clause V) ({(b, !sb), (c, !sb)} : Clause V)
      ({(a, sa), (c, !sb)} : Clause V) ∨
    IsResolvent ({(b, !sb), (c, !sb)} : Clause V) ({(a, sa), (b, sb)} : Clause V)
      ({(a, sa), (c, !sb)} : Clause V) := by
  have he1 : ({(a, sa), (b, sb)} : Clause V).erase (b, sb) = {(a, sa)} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hne, rfl | rfl⟩
      · rfl
      · exact False.elim (hne rfl)
    · rintro rfl
      refine ⟨fun h => hab (Prod.mk.inj h).1, Or.inl rfl⟩
  have he2 : ({(b, !sb), (c, !sb)} : Clause V).erase (b, !sb) = {(c, !sb)} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hne, rfl | rfl⟩
      · exact False.elim (hne rfl)
      · rfl
    · rintro rfl
      refine ⟨fun h => hbc (Prod.mk.inj h).1.symm, Or.inr rfl⟩
  cases sb with
  | true =>
    left
    refine ⟨b, by simp, by simp, ?_⟩
    simp only [Bool.not_true] at he2 ⊢
    rw [he1, he2]; ext z; simp
  | false =>
    right
    refine ⟨b, by simp, by simp, ?_⟩
    simp only [Bool.not_false] at he2 ⊢
    rw [he2, he1]; ext z; simp [or_comm]

private theorem derive_chain {m n : ℕ} {left right : Fin m → Fin n}
    {t : ℕ} {edges : Fin t → Fin m} {x : Fin (t + 1) → Fin n}
    (ht : 2 ≤ t) (hw : IsWalk left right (fun _ => True) t edges x)
    (hinj : Function.Injective (fun j : Fin t => x j.castSucc))
    (s : Bool) (π0 : List (Clause (Fin n)))
    (hπ0 : IsDerivation (form left right) π0) (hw0 : ∀ C ∈ π0, C.card ≤ 2) :
    ∀ (k : ℕ) (hk : k < t),
      let sgn : ℕ → Bool := fun j => if j % 2 = 0 then s else !s
      ∃ π : List (Clause (Fin n)),
        IsDerivation (form left right) π ∧
        (∀ C ∈ π, C.card ≤ 2) ∧
        (∀ C ∈ π0, C ∈ π) ∧
        {(x 0, s), (x ⟨k + 1, by omega⟩, sgn k)} ∈ π ∧
        π.length = π0.length + (2 * k + 1) := by
  intro k
  induction k with
  | zero =>
    intro hk sgn
    have he0 : cl left right (edges ⟨0, hk⟩) s = {(x 0, s), (x ⟨1, by omega⟩, s)} :=
      cl_eq_of_edge left right s (hw.2.2 ⟨0, hk⟩)
    refine ⟨cl left right (edges ⟨0, hk⟩) s :: π0, ?_, ?_, ?_, ?_, ?_⟩
    · exact IsDerivation.ax hπ0 ⟨edges ⟨0, hk⟩, s, rfl⟩
    · intro C hC
      simp only [List.mem_cons] at hC
      rcases hC with rfl | hC
      · rw [he0]; exact Finset.card_le_two
      · exact hw0 C hC
    · intro C hC; exact List.mem_cons_of_mem _ hC
    · simp only [sgn, Nat.zero_mod, ↓reduceIte, ← he0]; exact List.mem_cons_self ..
    · simp
  | succ k ih =>
    intro hk sgn
    obtain ⟨π1, hπ1, hw1, hsub1, hmem1, hlen1⟩ := ih (by omega)
    let j : Fin t := ⟨k + 1, hk⟩
    let sb : Bool := sgn k
    have hsb_next : (!sb) = sgn (k + 1) := by
      dsimp only [sb, sgn]
      by_cases hpar : k % 2 = 0
      · have hpar1 : (k + 1) % 2 ≠ 0 := by omega
        simp [hpar, hpar1]
      · have hpar1 : (k + 1) % 2 = 0 := by omega
        simp [hpar, hpar1]
    have hAx : cl left right (edges j) (!sb) =
        {(x ⟨k + 1, by omega⟩, !sb), (x ⟨k + 2, by omega⟩, !sb)} :=
      cl_eq_of_edge left right (!sb) (hw.2.2 j)
    let A := cl left right (edges j) (!sb)
    let R : Clause (Fin n) := {(x 0, s), (x ⟨k + 2, by omega⟩, !sb)}
    have hne1 : x 0 ≠ x ⟨k + 1, by omega⟩ := by
      intro heq
      have := hinj (show x (⟨0, by omega⟩ : Fin t).castSucc = x j.castSucc from heq)
      have hv := congrArg Fin.val this
      dsimp [j] at hv; omega
    have hne2 : x ⟨k + 1, by omega⟩ ≠ x ⟨k + 2, by omega⟩ := by
      intro heq
      by_cases hk2 : k + 2 < t
      · have := hinj (show x j.castSucc = x (⟨k + 2, hk2⟩ : Fin t).castSucc from heq)
        have hv := congrArg Fin.val this
        dsimp [j] at hv; omega
      · have hlast : (⟨k + 2, by omega⟩ : Fin (t + 1)) = Fin.last t := by ext; dsimp; omega
        rw [hlast, ← hw.1] at heq
        exact hne1 heq.symm
    have hres := isResolvent_pair (sa := s) (sb := sb) hne1 hne2
    have hπ2 : IsDerivation (form left right) (A :: π1) :=
      IsDerivation.ax hπ1 ⟨edges j, !sb, rfl⟩
    have hπ3 : IsDerivation (form left right) (R :: A :: π1) := by
      rcases hres with hres | hres
      · rw [← hAx] at hres
        exact IsDerivation.res hπ2 (List.mem_cons_of_mem _ hmem1) (List.mem_cons_self ..) hres
      · rw [← hAx] at hres
        exact IsDerivation.res hπ2 (List.mem_cons_self ..) (List.mem_cons_of_mem _ hmem1) hres
    refine ⟨R :: A :: π1, hπ3, ?_, ?_, ?_, ?_⟩
    · intro C hC
      simp only [List.mem_cons] at hC
      rcases hC with rfl | rfl | hC
      · exact Finset.card_le_two
      · dsimp only [A]; rw [hAx]; exact Finset.card_le_two
      · exact hw1 C hC
    · intro C hC; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub1 C hC))
    · have hReq : ({(x 0, s), (x ⟨k + 1 + 1, by omega⟩, sgn (k + 1))} : Clause (Fin n)) = R := by
        dsimp only [R]; rw [hsb_next]
      rw [hReq]; exact List.mem_cons_self ..
    · simp only [List.length_cons, hlen1]; omega

private theorem part1 {m n : ℕ} (left right : Fin m → Fin n)
    (g : ℕ) (edges : Fin g → Fin m)
    (hg : Odd g) (x : Fin (g + 1) → Fin n)
    (hclose : x 0 = x (Fin.last g))
    (hedge : ∀ j : Fin g,
      (x j.castSucc = left (edges j) ∧ x j.succ = right (edges j)) ∨
      (x j.castSucc = right (edges j) ∧ x j.succ = left (edges j))) :
    ∃ π : List (Clause (Fin n)),
      IsRefutation (form left right) π ∧ (∀ C ∈ π, C.card ≤ 2) ∧ π.length + 1 ≤ 4 * g := by
  obtain ⟨t, edges', x', htg, ht_odd, hw', hinj⟩ :=
    minimal_odd_walk (P := fun _ => True) hg ⟨hclose, fun _ => trivial, hedge⟩
  have ht_pos : 1 ≤ t := by obtain ⟨k, rfl⟩ := ht_odd; omega
  by_cases ht1 : t = 1
  · subst ht1
    have h01 : x' 0 = x' 1 := hw'.1
    have hloop : left (edges' 0) = x' 0 ∧ right (edges' 0) = x' 0 := by
      have h := hw'.2.2 0
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1.symm, h2.symm.trans h01.symm⟩
      · exact ⟨h2.symm.trans h01.symm, h1.symm⟩
    have hcT : cl left right (edges' 0) true = {(x' 0, true)} := by
      unfold cl; rw [hloop.1, hloop.2]; ext z; simp
    have hcF : cl left right (edges' 0) false = {(x' 0, false)} := by
      unfold cl; rw [hloop.1, hloop.2]; ext z; simp
    let π : List (Clause (Fin n)) := [∅, {(x' 0, false)}, {(x' 0, true)}]
    have hd1 : IsDerivation (form left right) [{(x' 0, true)}] :=
      IsDerivation.ax IsDerivation.nil ⟨edges' 0, true, hcT.symm⟩
    have hd2 : IsDerivation (form left right) [{(x' 0, false)}, {(x' 0, true)}] :=
      IsDerivation.ax hd1 ⟨edges' 0, false, hcF.symm⟩
    have hres : IsResolvent ({(x' 0, true)} : Clause (Fin n)) {(x' 0, false)} ∅ :=
      ⟨x' 0, by simp, by simp, by ext z; simp⟩
    have hd3 : IsDerivation (form left right) π :=
      IsDerivation.res hd2 (by simp) (by simp) hres
    refine ⟨π, ⟨hd3, by simp [π]⟩, ?_, ?_⟩
    · intro C hC
      simp only [π, List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl <;> simp
    · simp only [π, List.length_cons, List.length_nil]; omega
  · have ht2 : 2 ≤ t := by omega
    have htm1_even : (t - 1) % 2 = 0 := by obtain ⟨k, rfl⟩ := ht_odd; omega
    have hlast_eq : (⟨t - 1 + 1, by omega⟩ : Fin (t + 1)) = Fin.last t := by ext; dsimp; omega
    obtain ⟨π1, hπ1, hw1, _, hmemT, hlen1⟩ :=
      derive_chain ht2 hw' hinj true [] IsDerivation.nil (by simp) (t - 1) (by omega)
    simp only [htm1_even, ↓reduceIte, hlast_eq, ← hw'.1, Finset.pair_eq_singleton] at hmemT
    obtain ⟨π2, hπ2, hw2, hsub2, hmemF, hlen2⟩ :=
      derive_chain ht2 hw' hinj false π1 hπ1 hw1 (t - 1) (by omega)
    simp only [htm1_even, ↓reduceIte, hlast_eq, ← hw'.1, Finset.pair_eq_singleton] at hmemF
    have hmemT2 : ({(x' 0, true)} : Clause (Fin n)) ∈ π2 := hsub2 _ hmemT
    have hres : IsResolvent ({(x' 0, true)} : Clause (Fin n)) {(x' 0, false)} ∅ :=
      ⟨x' 0, by simp, by simp, by ext z; simp⟩
    refine ⟨∅ :: π2, ⟨IsDerivation.res hπ2 hmemT2 hmemF hres, List.mem_cons_self ..⟩, ?_, ?_⟩
    · intro C hC
      simp only [List.mem_cons] at hC
      rcases hC with rfl | hC
      · simp
      · exact hw2 C hC
    · simp only [List.length_cons, hlen2, hlen1, List.length_nil]; omega

private theorem derivation_witness {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (hπ : IsDerivation F π) :
    ∃ step : Fin π.length → Option (Fin π.length × Fin π.length),
      ∀ i : Fin π.length,
        match step i with
        | none => π[i] ∈ F
        | some (j, k) => i.val < j.val ∧ i.val < k.val ∧ IsResolvent π[j] π[k] π[i] := by
  induction hπ with
  | nil =>
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | @ax π C _ hCF ih =>
    obtain ⟨step, hstep⟩ := ih
    refine ⟨fun i => Fin.cases none (fun i' => (step i').map (fun p => (p.1.succ, p.2.succ))) i, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using hCF
    · intro i'
      have hi' := hstep i'
      cases hsi : step i' with
      | none =>
        rw [hsi] at hi'
        simpa [hsi] using hi'
      | some p =>
        rw [hsi] at hi'
        simpa [hsi] using hi'
  | @res π C D R _ hC hD hres ih =>
    obtain ⟨step, hstep⟩ := ih
    obtain ⟨j0, hj0⟩ := List.getElem_of_mem hC
    obtain ⟨k0, hk0⟩ := List.getElem_of_mem hD
    let j : Fin π.length := ⟨j0, hj0.1⟩
    let k : Fin π.length := ⟨k0, hk0.1⟩
    refine ⟨fun i => Fin.cases (some (j.succ, k.succ))
      (fun i' => (step i').map (fun p => (p.1.succ, p.2.succ))) i, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cases_zero, Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, true_and]
      change IsResolvent π[j] π[k] R
      have h1 : π[j] = C := hj0.2
      have h2 : π[k] = D := hk0.2
      rw [h1, h2]
      exact hres
    · intro i'
      have hi' := hstep i'
      cases hsi : step i' with
      | none =>
        rw [hsi] at hi'
        simpa [hsi] using hi'
      | some p =>
        rw [hsi] at hi'
        simpa [hsi] using hi'

private theorem resolvent_sound {V : Type} [DecidableEq V] {a : V → Bool}
    {C D R : Clause V} (hR : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) :
    ClauseSat a R := by
  obtain ⟨v, _, _, rfl⟩ := hR
  cases hav : a v with
  | false =>
    obtain ⟨l, hlC, hla⟩ := hC
    refine ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hlC⟩), hla⟩
    intro heq; rw [heq] at hla; simp [hav] at hla
  | true =>
    obtain ⟨l, hlD, hla⟩ := hD
    refine ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hlD⟩), hla⟩
    intro heq; rw [heq] at hla; simp [hav] at hla

private theorem unsat_core_of_refutation {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (href : IsRefutation F π) :
    ∃ S : Finset (Clause V),
      (∀ C ∈ S, C ∈ F ∧ C ∈ π) ∧
      (∀ a : V → Bool, ¬ ∀ C ∈ S, ClauseSat a C) ∧
      2 * S.card ≤ π.length + 1 := by
  classical
  obtain ⟨hπ, hempty⟩ := href
  obtain ⟨step, hstep⟩ := derivation_witness hπ
  obtain ⟨r0, hr0_lt, hr0_eq⟩ := List.getElem_of_mem hempty
  let r : Fin π.length := ⟨r0, hr0_lt⟩
  let Closed : Finset (Fin π.length) → Prop := fun U =>
    r ∈ U ∧ ∀ i ∈ U, ∀ j k, step i = some (j, k) → j ∈ U ∧ k ∈ U
  have hexU : ∃ n, ∃ U : Finset (Fin π.length), Closed U ∧ U.card = n :=
    ⟨Finset.univ.card, Finset.univ, ⟨Finset.mem_univ r, fun _ _ _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩, rfl⟩
  let minCard := Nat.find hexU
  obtain ⟨U, hU_closed, hU_card⟩ := Nat.find_spec hexU
  let Uax := U.filter (fun i => (step i).isNone)
  let Ures := U.filter (fun i => (step i).isSome)
  have hpart : Uax.card + Ures.card = U.card := by
    have hdisj : Disjoint Uax Ures := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      have ha := (Finset.mem_filter.mp h1).2
      have hr := (Finset.mem_filter.mp h2).2
      cases h : step i <;> simp [h] at ha hr
    have hunion : Uax ∪ Ures = U := by
      ext i
      simp only [Uax, Ures, Finset.mem_union, Finset.mem_filter]
      cases step i <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hcover : U.erase r ⊆ Ures.biUnion (fun i =>
      match step i with | none => ∅ | some (j, k) => ({j, k} : Finset (Fin π.length))) := by
    intro u hu
    obtain ⟨hne, huU⟩ := Finset.mem_erase.mp hu
    by_contra hnot
    have hclosed_erase : Closed (U.erase u) := by
      refine ⟨Finset.mem_erase.mpr ⟨Ne.symm hne, hU_closed.1⟩, ?_⟩
      intro i hi j k hsi
      have hiU : i ∈ U := Finset.mem_of_mem_erase hi
      obtain ⟨hjU, hkU⟩ := hU_closed.2 i hiU j k hsi
      have hiRes : i ∈ Ures := Finset.mem_filter.mpr ⟨hiU, by simp [hsi]⟩
      have hju : j ≠ u := by
        intro heq; subst heq
        exact hnot (Finset.mem_biUnion.mpr ⟨i, hiRes, by simp [hsi]⟩)
      have hku : k ≠ u := by
        intro heq; subst heq
        exact hnot (Finset.mem_biUnion.mpr ⟨i, hiRes, by simp [hsi]⟩)
      exact ⟨Finset.mem_erase.mpr ⟨hju, hjU⟩, Finset.mem_erase.mpr ⟨hku, hkU⟩⟩
    have hlt : (U.erase u).card < minCard := by
      dsimp only [minCard]
      rw [← hU_card]; exact Finset.card_erase_lt_of_mem huU
    exact Nat.find_min hexU hlt ⟨U.erase u, hclosed_erase, rfl⟩
  have hbound_erase : (U.erase r).card ≤ 2 * Ures.card := by
    calc (U.erase r).card
        ≤ (Ures.biUnion (fun i => match step i with | none => ∅ | some (j, k) => {j, k})).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ i ∈ Ures, (match step i with | none => (∅ : Finset (Fin π.length)) | some (j, k) => {j, k}).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ Ures, 2 := by
          apply Finset.sum_le_sum
          intro i _
          cases step i with
          | none => simp
          | some p => exact Finset.card_le_two
      _ = 2 * Ures.card := by simp [mul_comm]
  have hr_card : (U.erase r).card = U.card - 1 := Finset.card_erase_of_mem hU_closed.1
  have hU_pos : 1 ≤ U.card := Finset.one_le_card.mpr ⟨r, hU_closed.1⟩
  have hU_le : U.card ≤ π.length := by
    calc U.card ≤ (Finset.univ : Finset (Fin π.length)).card := Finset.card_le_univ U
      _ = π.length := Fintype.card_fin π.length
  have h2ax : 2 * Uax.card ≤ π.length + 1 := by omega
  let S : Finset (Clause V) := Uax.image (fun i => π[i])
  refine ⟨S, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
    have hi_none : (step i).isNone = true := (Finset.mem_filter.mp hi).2
    have hsi := hstep i
    cases h : step i with
    | none =>
      rw [h] at hsi
      exact ⟨hsi, List.getElem_mem i.isLt⟩
    | some _ => simp [h] at hi_none
  · intro a ha
    have hsat : ∀ d : ℕ, ∀ i : Fin π.length, π.length - 1 - i.val ≤ d → i ∈ U → ClauseSat a π[i] := by
      intro d
      induction d with
      | zero =>
        intro i hd hiU
        have hsi := hstep i
        cases h : step i with
        | none =>
          have hiAx : i ∈ Uax := Finset.mem_filter.mpr ⟨hiU, by simp [h]⟩
          exact ha π[i] (Finset.mem_image.mpr ⟨i, hiAx, rfl⟩)
        | some p =>
          rw [h] at hsi
          omega
      | succ d ih =>
        intro i hd hiU
        have hsi := hstep i
        cases h : step i with
        | none =>
          have hiAx : i ∈ Uax := Finset.mem_filter.mpr ⟨hiU, by simp [h]⟩
          exact ha π[i] (Finset.mem_image.mpr ⟨i, hiAx, rfl⟩)
        | some p =>
          rw [h] at hsi
          obtain ⟨hij, hik, hres⟩ := hsi
          obtain ⟨hjU, hkU⟩ := hU_closed.2 i hiU p.1 p.2 h
          exact resolvent_sound hres (ih p.1 (by omega) hjU) (ih p.2 (by omega) hkU)
    have hrempty : ClauseSat a π[r] := hsat π.length r (by omega) hU_closed.1
    have hrval : π[r] = ∅ := hr0_eq
    rw [hrval] at hrempty
    obtain ⟨l, hl, _⟩ := hrempty
    exact Finset.notMem_empty l hl
  · have hScard : S.card ≤ Uax.card := Finset.card_image_le
    omega

private def IsPath {m n : ℕ} (left right : Fin m → Fin n) (P : Fin m → Prop)
    (k : ℕ) (u v : Fin n) (edges : Fin k → Fin m) (x : Fin (k + 1) → Fin n) : Prop :=
  x 0 = u ∧ x (Fin.last k) = v ∧
  (∀ j : Fin k, P (edges j)) ∧
  (∀ j : Fin k,
    (x j.castSucc = left (edges j) ∧ x j.succ = right (edges j)) ∨
    (x j.castSucc = right (edges j) ∧ x j.succ = left (edges j)))

private def HasPath {m n : ℕ} (left right : Fin m → Fin n) (P : Fin m → Prop)
    (k : ℕ) (u v : Fin n) : Prop :=
  ∃ edges x, IsPath left right P k u v edges x

private theorem hasPath_zero {m n : ℕ} {left right : Fin m → Fin n} {P : Fin m → Prop} (u : Fin n) :
    HasPath left right P 0 u u :=
  ⟨Fin.elim0, fun _ => u, rfl, rfl, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩

private theorem hasPath_one {m n : ℕ} {left right : Fin m → Fin n} {P : Fin m → Prop}
    {e : Fin m} (hP : P e) :
    HasPath left right P 1 (left e) (right e) := by
  refine ⟨fun _ => e, fun k => if k.val = 0 then left e else right e, rfl, rfl, fun _ => hP, ?_⟩
  intro j
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj; left; exact ⟨rfl, rfl⟩

private theorem hasPath_symm {m n : ℕ} {left right : Fin m → Fin n} {P : Fin m → Prop}
    {k : ℕ} {u v : Fin n} (h : HasPath left right P k u v) :
    HasPath left right P k v u := by
  obtain ⟨edges, x, h0, hlast, hP, hedge⟩ := h
  refine ⟨fun j => edges ⟨k - 1 - j.val, by omega⟩, fun i => x ⟨k - i.val, by omega⟩, ?_, ?_, ?_, ?_⟩
  · dsimp only
    have : (⟨k - (0 : Fin (k + 1)).val, by omega⟩ : Fin (k + 1)) = Fin.last k := by ext; simp
    rw [this]; exact hlast
  · dsimp only
    have : (⟨k - (Fin.last k).val, by omega⟩ : Fin (k + 1)) = 0 := by ext; simp
    rw [this]; exact h0
  · intro j; exact hP _
  · intro j
    dsimp only
    have he := hedge ⟨k - 1 - j.val, by omega⟩
    have h1 : (⟨k - j.castSucc.val, by omega⟩ : Fin (k + 1)) = (⟨k - 1 - j.val, by omega⟩ : Fin k).succ := by
      ext; simp; omega
    have h2 : (⟨k - j.succ.val, by omega⟩ : Fin (k + 1)) = (⟨k - 1 - j.val, by omega⟩ : Fin k).castSucc := by
      ext; simp; omega
    rw [h1, h2]
    rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr ⟨hb, ha⟩
    · exact Or.inl ⟨hb, ha⟩

private theorem hasPath_trans {m n : ℕ} {left right : Fin m → Fin n} {P : Fin m → Prop}
    {k1 k2 : ℕ} {u v w : Fin n}
    (h1 : HasPath left right P k1 u v) (h2 : HasPath left right P k2 v w) :
    HasPath left right P (k1 + k2) u w := by
  obtain ⟨e1, x1, h10, h1l, hP1, hedge1⟩ := h1
  obtain ⟨e2, x2, h20, h2l, hP2, hedge2⟩ := h2
  let e : Fin (k1 + k2) → Fin m := fun j =>
    if hj : j.val < k1 then e1 ⟨j.val, hj⟩ else e2 ⟨j.val - k1, by omega⟩
  let x : Fin (k1 + k2 + 1) → Fin n := fun i =>
    if hi : i.val < k1 then x1 ⟨i.val, by omega⟩ else x2 ⟨i.val - k1, by omega⟩
  refine ⟨e, x, ?_, ?_, ?_, ?_⟩
  · dsimp only [x]
    by_cases hk1 : 0 < k1
    · simp only [Fin.val_zero, hk1, ↓reduceDIte]
      exact h10
    · simp only [Fin.val_zero, hk1, ↓reduceDIte]
      have h0 : (⟨0 - k1, by omega⟩ : Fin (k2 + 1)) = 0 := by ext; simp
      have h0l : (0 : Fin (k1 + 1)) = Fin.last k1 := by ext; simp; omega
      rw [h0, h20, ← h1l, ← h0l, h10]
  · dsimp only [x]
    have hnot : ¬ (k1 + k2 < k1) := by omega
    simp only [Fin.val_last, hnot, ↓reduceDIte]
    have hl : (⟨k1 + k2 - k1, by omega⟩ : Fin (k2 + 1)) = Fin.last k2 := by ext; simp
    rw [hl]; exact h2l
  · intro j
    dsimp only [e]
    split_ifs with hj
    · exact hP1 _
    · exact hP2 _
  · intro j
    by_cases hj : j.val < k1
    · have hEj : e j = e1 ⟨j.val, hj⟩ := by simp [e, hj]
      have hX1 : x j.castSucc = x1 (⟨j.val, hj⟩ : Fin k1).castSucc := by
        simp [x, hj]
      by_cases hj1 : j.val + 1 < k1
      · have hX2 : x j.succ = x1 (⟨j.val, hj⟩ : Fin k1).succ := by
          simp [x, hj1]
        rw [hEj, hX1, hX2]; exact hedge1 ⟨j.val, hj⟩
      · have hjeq : j.val + 1 = k1 := by omega
        have hX2 : x j.succ = x2 0 := by
          simp only [x, Fin.val_succ, hj1, ↓reduceDIte]
          congr 1; ext; simp [hjeq]
        have hX1s : (⟨j.val, hj⟩ : Fin k1).succ = Fin.last k1 := by ext; simp [hjeq]
        rw [hEj, hX1, hX2, h20, ← h1l, ← hX1s]; exact hedge1 ⟨j.val, hj⟩
    · have hEj : e j = e2 ⟨j.val - k1, by omega⟩ := by simp [e, hj]
      have hj1 : ¬ j.val + 1 < k1 := by omega
      have hX1 : x j.castSucc = x2 (⟨j.val - k1, by omega⟩ : Fin k2).castSucc := by
        simp [x, hj]
      have hX2 : x j.succ = x2 (⟨j.val - k1, by omega⟩ : Fin k2).succ := by
        simp only [x, Fin.val_succ, hj1, ↓reduceDIte]
        congr 1; ext; simp; omega
      rw [hEj, hX1, hX2]; exact hedge2 ⟨j.val - k1, by omega⟩

private theorem exists_odd_walk_of_unsat {m n : ℕ} (left right : Fin m → Fin n)
    (P : Fin m → Prop)
    (hunsat : ∀ col : Fin n → Bool, ∃ e, P e ∧ col (left e) = col (right e)) :
    ∃ (g : ℕ) (edges : Fin g → Fin m) (x : Fin (g + 1) → Fin n),
      Odd g ∧ IsWalk left right P g edges x := by
  classical
  by_contra hno
  let Reach : Fin n → Fin n → Prop := fun u v => ∃ k, HasPath left right P k u v
  let ReachEven : Fin n → Fin n → Prop := fun u v => ∃ k, Even k ∧ HasPath left right P k u v
  have hR_refl : ∀ u, Reach u u := fun u => ⟨0, hasPath_zero u⟩
  have hR_symm : ∀ {u v}, Reach u v → Reach v u := fun ⟨k, h⟩ => ⟨k, hasPath_symm h⟩
  have hR_trans : ∀ {u v w}, Reach u v → Reach v w → Reach u w :=
    fun ⟨k1, h1⟩ ⟨k2, h2⟩ => ⟨k1 + k2, hasPath_trans h1 h2⟩
  let comp (v : Fin n) : Finset (Fin n) := Finset.univ.filter (fun w => Reach v w)
  have hcomp_ne : ∀ v, (comp v).Nonempty := fun v =>
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hR_refl v⟩⟩
  let rep (v : Fin n) : Fin n := (comp v).min' (hcomp_ne v)
  have hrep_eq : ∀ {u v}, Reach u v → rep u = rep v := by
    intro u v huv
    have hcomp_eq : comp u = comp v := by
      ext w; simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => hR_trans (hR_symm huv) h, fun h => hR_trans huv h⟩
    simp only [rep, hcomp_eq]
  have hrep_reach : ∀ v, Reach (rep v) v := by
    intro v
    have hmem : rep v ∈ comp v := Finset.min'_mem (comp v) (hcomp_ne v)
    exact hR_symm (Finset.mem_filter.mp hmem).2
  let col : Fin n → Bool := fun v => decide (ReachEven (rep v) v)
  obtain ⟨e, hPe, hcol_eq⟩ := hunsat col
  have hedge_path : HasPath left right P 1 (left e) (right e) := hasPath_one hPe
  have hru_v : Reach (left e) (right e) := ⟨1, hedge_path⟩
  have hrep : rep (left e) = rep (right e) := hrep_eq hru_v
  let r0 := rep (left e)
  have hr_left : Reach r0 (left e) := hrep_reach (left e)
  have hr_right : Reach r0 (right e) := by dsimp only [r0]; rw [hrep]; exact hrep_reach (right e)
  have hsame : ReachEven r0 (left e) ↔ ReachEven r0 (right e) := by
    have h1 : decide (ReachEven r0 (left e)) = decide (ReachEven r0 (right e)) := by
      dsimp only [col, r0] at hcol_eq ⊢
      rwa [← hrep] at hcol_eq
    exact decide_eq_decide.mp h1
  have hodd_loop : ∃ k, Odd k ∧ HasPath left right P k r0 r0 := by
    by_cases hev : ReachEven r0 (left e)
    · obtain ⟨k1, hk1, hp1⟩ := hev
      obtain ⟨k2, hk2, hp2⟩ := hsame.mp ⟨k1, hk1, hp1⟩
      refine ⟨k1 + 1 + k2, ?_, hasPath_trans (hasPath_trans hp1 hedge_path) (hasPath_symm hp2)⟩
      obtain ⟨a, ha⟩ := hk1; obtain ⟨b, hb⟩ := hk2
      exact ⟨a + b, by omega⟩
    · have hnotR : ¬ ReachEven r0 (right e) := fun h => hev (hsame.mpr h)
      obtain ⟨k1, hp1⟩ := hr_left
      obtain ⟨k2, hp2⟩ := hr_right
      have hk1 : Odd k1 := Nat.not_even_iff_odd.mp (fun h => hev ⟨k1, h, hp1⟩)
      have hk2 : Odd k2 := Nat.not_even_iff_odd.mp (fun h => hnotR ⟨k2, h, hp2⟩)
      refine ⟨k1 + 1 + k2, ?_, hasPath_trans (hasPath_trans hp1 hedge_path) (hasPath_symm hp2)⟩
      obtain ⟨a, ha⟩ := hk1; obtain ⟨b, hb⟩ := hk2
      exact ⟨a + b + 1, by omega⟩
  obtain ⟨k, hk_odd, edges, x, h0, hlast, hP, hedge⟩ := hodd_loop
  exact hno ⟨k, edges, x, hk_odd, h0.trans hlast.symm, hP, hedge⟩

private theorem part2 {m n : ℕ} (left right : Fin m → Fin n)
    (π : List (Clause (Fin n))) (href : IsRefutation (form left right) π) :
    ∃ (g : ℕ) (edges : Fin g → Fin m) (sign : Fin g → Bool),
      (Odd g ∧ ∃ x : Fin (g + 1) → Fin n,
        x 0 = x (Fin.last g) ∧ ∀ j : Fin g,
          (x j.castSucc = left (edges j) ∧ x j.succ = right (edges j)) ∨
          (x j.castSucc = right (edges j) ∧ x j.succ = left (edges j))) ∧
      Function.Injective edges ∧
      Function.Injective (fun pos => cl left right (edges pos) (sign pos)) ∧
      (∀ idx, cl left right (edges idx) (sign idx) ∈ π) ∧
      2 * g ≤ π.length + 1 := by
  classical
  obtain ⟨S, hS_mem, hS_unsat, hS_card⟩ := unsat_core_of_refutation href
  let P : Fin m → Prop := fun e => ∃ b : Bool, cl left right e b ∈ S
  have hP_unsat : ∀ col : Fin n → Bool, ∃ e, P e ∧ col (left e) = col (right e) := by
    intro col
    by_contra hcol
    push Not at hcol
    apply hS_unsat col
    intro C hCS
    obtain ⟨⟨e, b, rfl⟩, _⟩ := hS_mem C hCS
    have hPe : P e := ⟨b, hCS⟩
    have hne : col (left e) ≠ col (right e) := hcol e hPe
    by_cases h1 : col (left e) = b
    · exact ⟨(left e, b), by simp [cl], h1⟩
    · have h2 : col (right e) = b := by
        cases hc1 : col (left e) <;> cases hc2 : col (right e) <;> cases b <;> simp_all
      exact ⟨(right e, b), by simp [cl], h2⟩
  obtain ⟨g0, edges0, x0, hg0_odd, hw0⟩ := exists_odd_walk_of_unsat left right P hP_unsat
  obtain ⟨g, edges, x, _, hg_odd, hw, hinj⟩ := minimal_odd_walk hg0_odd hw0
  choose sign hsign using hw.2.1
  have hpair_eq : ∀ j : Fin g,
      ({left (edges j), right (edges j)} : Finset (Fin n)) = {x j.castSucc, x j.succ} := by
    intro j
    rcases hw.2.2 j with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; ext v; simp [or_comm]
  have hpair_inj : ∀ a b : Fin g,
      ({left (edges a), right (edges a)} : Finset (Fin n)) = {left (edges b), right (edges b)} →
      a = b := by
    intro a b hab
    by_cases hg1 : g = 1
    · ext; omega
    · have hg3 : 3 ≤ g := by obtain ⟨k, rfl⟩ := hg_odd; omega
      rw [hpair_eq a, hpair_eq b] at hab
      let nxt : Fin g → Fin g := fun j => ⟨(j.val + 1) % g, Nat.mod_lt _ (by omega)⟩
      have hxnxt : ∀ j : Fin g, x j.succ = x (nxt j).castSucc := by
        intro j
        by_cases hj : j.val + 1 < g
        · congr 1; ext; simp [nxt, Nat.mod_eq_of_lt hj]
        · have hjl : j.succ = Fin.last g := by ext; simp; omega
          have hnj : nxt j = ⟨0, by omega⟩ := by ext; simp [nxt, show j.val + 1 = g by omega]
          have h0c : (⟨0, by omega⟩ : Fin g).castSucc = 0 := by ext; simp
          rw [hjl, hnj, h0c, ← hw.1]
      rw [hxnxt a, hxnxt b] at hab
      have ha_mem : x a.castSucc ∈ ({x b.castSucc, x (nxt b).castSucc} : Finset (Fin n)) := by
        rw [← hab]; simp
      have ha1_mem : x (nxt a).castSucc ∈ ({x b.castSucc, x (nxt b).castSucc} : Finset (Fin n)) := by
        rw [← hab]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem ha1_mem
      rcases ha_mem with h1 | h1
      · exact hinj h1
      · have hab1 : a = nxt b := hinj h1
        rcases ha1_mem with h2 | h2
        · have hba1 : nxt a = b := hinj h2
          have hv1 : a.val = (b.val + 1) % g := congrArg Fin.val hab1
          have hv2 : (a.val + 1) % g = b.val := congrArg Fin.val hba1
          have h12 : (b.val + 2) % g = b.val := by
            have : (b.val + 2) % g = ((b.val + 1) % g + 1) % g := by
              rw [show b.val + 2 = (b.val + 1) + 1 by omega, Nat.add_mod,
                Nat.mod_eq_of_lt (by omega : 1 < g)]
            rw [this, ← hv1, hv2]
          by_cases hlt : b.val + 2 < g
          · rw [Nat.mod_eq_of_lt hlt] at h12; omega
          · rw [Nat.mod_eq_sub_mod (by omega : g ≤ b.val + 2), Nat.mod_eq_of_lt (by omega)] at h12
            omega
        · have heq : nxt a = nxt b := hinj h2
          have h1v : (a.val + 1) % g = (b.val + 1) % g := congrArg Fin.val heq
          ext
          by_cases ha_lt : a.val + 1 < g <;> by_cases hb_lt : b.val + 1 < g
          · rw [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at h1v; omega
          · have hb_eq : b.val + 1 = g := by omega
            rw [Nat.mod_eq_of_lt ha_lt, hb_eq, Nat.mod_self] at h1v; omega
          · have ha_eq : a.val + 1 = g := by omega
            rw [ha_eq, Nat.mod_self, Nat.mod_eq_of_lt hb_lt] at h1v; omega
          · omega
  have hedges_inj : Function.Injective edges := by
    intro a b hab
    exact hpair_inj a b (by rw [hab])
  have hcl_inj : Function.Injective (fun pos => cl left right (edges pos) (sign pos)) := by
    intro a b hab
    have himg : (cl left right (edges a) (sign a)).image Prod.fst =
        (cl left right (edges b) (sign b)).image Prod.fst := congrArg (Finset.image Prod.fst) hab
    have hf : ∀ e s, (cl left right e s).image Prod.fst = {left e, right e} := by
      intro e s; ext v; simp [cl]
    rw [hf, hf] at himg
    exact hpair_inj a b himg
  have hg_le : g ≤ S.card := by
    calc g = (Finset.univ : Finset (Fin g)).card := (Fintype.card_fin g).symm
      _ = ((Finset.univ : Finset (Fin g)).image (fun pos => cl left right (edges pos) (sign pos))).card :=
          (Finset.card_image_of_injective _ hcl_inj).symm
      _ ≤ S.card := Finset.card_le_card (fun C hC => by
          obtain ⟨pos, _, rfl⟩ := Finset.mem_image.mp hC
          exact hsign pos)
  refine ⟨g, edges, sign, ⟨hg_odd, x, hw.1, hw.2.2⟩, hedges_inj, hcl_inj, ?_, by omega⟩
  intro idx
  exact (hS_mem _ (hsign idx)).2

private theorem main_aux : ∀ (m n : ℕ) (left right : Fin m → Fin n),
  let clause := fun (e : Fin m) (b : Bool) =>
    ({(left e, b), (right e, b)} : PEqualNP.ProofComplexity.Clause (Fin n))
  let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) :=
    {C | ∃ e b, C = clause e b}
  let walk := fun (g : ℕ) (edges : Fin g → Fin m) =>
    Odd g ∧ ∃ x : Fin (g + 1) → Fin n,
      x 0 = x (Fin.last g) ∧ ∀ j : Fin g,
        (x j.castSucc = left (edges j) ∧ x j.succ = right (edges j)) ∨
        (x j.castSucc = right (edges j) ∧ x j.succ = left (edges j))
  (∀ (g : ℕ) (edges : Fin g → Fin m), walk g edges →
    ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin n)),
      PEqualNP.ProofComplexity.IsRefutation F π ∧ (∀ C ∈ π, C.card ≤ 2) ∧
      π.length + 1 ≤ 4 * g) ∧
  (∀ π : List (PEqualNP.ProofComplexity.Clause (Fin n)),
    PEqualNP.ProofComplexity.IsRefutation F π →
    ∃ (g : ℕ) (edges : Fin g → Fin m) (sign : Fin g → Bool),
      walk g edges ∧ Function.Injective edges ∧
      Function.Injective (fun pos => clause (edges pos) (sign pos)) ∧
      (∀ idx, clause (edges idx) (sign idx) ∈ π) ∧ 2 * g ≤ π.length + 1) := by
  intro m n left right clause F walk
  constructor
  · intro g edges ⟨hg, x, hclose, hedge⟩
    exact part1 left right g edges hg x hclose hedge
  · intro π href
    exact part2 left right π href

end PEqualNP.Outside.L_pcx_212_aux

theorem PEqualNP.Outside.L_pcx_212 : (∀ (m n : ℕ) (left right : Fin m → Fin n),
  let clause := fun (e : Fin m) (b : Bool) =>
    ({(left e, b), (right e, b)} : PEqualNP.ProofComplexity.Clause (Fin n))
  let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) :=
    {C | ∃ e b, C = clause e b}
  let walk := fun (g : ℕ) (edges : Fin g → Fin m) =>
    Odd g ∧ ∃ x : Fin (g + 1) → Fin n,
      x 0 = x (Fin.last g) ∧ ∀ j : Fin g,
        (x j.castSucc = left (edges j) ∧ x j.succ = right (edges j)) ∨
        (x j.castSucc = right (edges j) ∧ x j.succ = left (edges j))
  (∀ (g : ℕ) (edges : Fin g → Fin m), walk g edges →
    ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin n)),
      PEqualNP.ProofComplexity.IsRefutation F π ∧ (∀ C ∈ π, C.card ≤ 2) ∧
      π.length + 1 ≤ 4 * g) ∧
  (∀ π : List (PEqualNP.ProofComplexity.Clause (Fin n)),
    PEqualNP.ProofComplexity.IsRefutation F π →
    ∃ (g : ℕ) (edges : Fin g → Fin m) (sign : Fin g → Bool),
      walk g edges ∧ Function.Injective edges ∧
      Function.Injective (fun pos => clause (edges pos) (sign pos)) ∧
      (∀ idx, clause (edges idx) (sign idx) ∈ π) ∧ 2 * g ≤ π.length + 1)) :=
  PEqualNP.Outside.L_pcx_212_aux.main_aux

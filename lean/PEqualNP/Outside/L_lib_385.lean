import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PEqualNP.Outside.L_lib_385

private def Step {f n : ℕ} (left right : (Fin f → ZMod 2) → Fin n)
    (S : Set (Fin f → ZMod 2)) (u v : Fin n) : Prop :=
  ∃ z ∈ S, (u = left z ∧ v = right z) ∨ (u = right z ∧ v = left z)

private lemma step_symm {f n : ℕ} {left right : (Fin f → ZMod 2) → Fin n}
    {S : Set (Fin f → ZMod 2)} {u v : Fin n}
    (h : Step left right S u v) : Step left right S v u := by
  rcases h with ⟨z, hz, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩
  · exact ⟨z, hz, Or.inr ⟨hv, hu⟩⟩
  · exact ⟨z, hz, Or.inl ⟨hv, hu⟩⟩

private def WalkN {f n : ℕ} (left right : (Fin f → ZMod 2) → Fin n)
    (S : Set (Fin f → ZMod 2)) : ℕ → Fin n → Fin n → Prop
  | 0, u, v => u = v
  | k + 1, u, v => ∃ w, Step left right S u w ∧ WalkN left right S k w v

private lemma walkN_one {f n : ℕ} {left right : (Fin f → ZMod 2) → Fin n}
    {S : Set (Fin f → ZMod 2)} {u v : Fin n}
    (h : Step left right S u v) : WalkN left right S 1 u v :=
  ⟨v, h, rfl⟩

private lemma walkN_trans {f n : ℕ} {left right : (Fin f → ZMod 2) → Fin n}
    {S : Set (Fin f → ZMod 2)} :
    ∀ {k₁ k₂ : ℕ} {u v w : Fin n},
      WalkN left right S k₁ u v → WalkN left right S k₂ v w → WalkN left right S (k₁ + k₂) u w
  | 0, _, _, _, _, h₁, h₂ => by
      subst h₁
      simpa only [Nat.zero_add] using h₂
  | k₁ + 1, k₂, u, v, w, ⟨x, hux, hxv⟩, h₂ => by
      rw [Nat.succ_add]
      exact ⟨x, hux, walkN_trans hxv h₂⟩

private lemma walkN_symm {f n : ℕ} {left right : (Fin f → ZMod 2) → Fin n}
    {S : Set (Fin f → ZMod 2)} :
    ∀ {k : ℕ} {u v : Fin n}, WalkN left right S k u v → WalkN left right S k v u
  | 0, _, _, h => h.symm
  | _ + 1, _, _, ⟨_, hux, hxv⟩ =>
      walkN_trans (walkN_symm hxv) (walkN_one (step_symm hux))

private lemma finset_min'_eq {α : Type*} [LinearOrder α] {s₁ s₂ : Finset α}
    (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) (heq : s₁ = s₂) :
    s₁.min' h₁ = s₂.min' h₂ := by
  subst heq
  rfl

private lemma two_color_of_no_odd_closed_walk {f n : ℕ}
    (left right : (Fin f → ZMod 2) → Fin n) (S : Set (Fin f → ZMod 2))
    (hno : ∀ u k, Odd k → ¬ WalkN left right S k u u) :
    ∃ c : Fin n → Bool, ∀ z ∈ S, c (left z) ≠ c (right z) := by
  classical
  let Reach : Fin n → Fin n → Prop := fun u v => ∃ k, WalkN left right S k u v
  have hrefl : ∀ u, Reach u u := fun u => ⟨0, rfl⟩
  have hsymm : ∀ {u v}, Reach u v → Reach v u := fun ⟨k, hk⟩ => ⟨k, walkN_symm hk⟩
  have htrans : ∀ {u v w}, Reach u v → Reach v w → Reach u w :=
    fun ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ => ⟨k₁ + k₂, walkN_trans h₁ h₂⟩
  let comp : Fin n → Finset (Fin n) := fun u => Finset.univ.filter (Reach u)
  have hcomp_ne : ∀ u, (comp u).Nonempty := fun u =>
    ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hrefl u⟩⟩
  let rep : Fin n → Fin n := fun u => (comp u).min' (hcomp_ne u)
  have hrep_reach : ∀ u, Reach (rep u) u := fun u =>
    hsymm (Finset.mem_filter.mp (Finset.min'_mem (comp u) (hcomp_ne u))).2
  have hrep_eq : ∀ {u v}, Reach u v → rep u = rep v := by
    intro u v huv
    apply finset_min'_eq
    ext w
    simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun huw => htrans (hsymm huv) huw, fun hvw => htrans huv hvw⟩
  let c : Fin n → Bool := fun u => decide (∃ k, Odd k ∧ WalkN left right S k (rep u) u)
  refine ⟨c, fun z hz => ?_⟩
  have hstep : Step left right S (left z) (right z) := ⟨z, hz, Or.inl ⟨rfl, rfl⟩⟩
  have hrep : rep (left z) = rep (right z) := hrep_eq ⟨1, walkN_one hstep⟩
  intro heq
  simp only [c, hrep, decide_eq_decide] at heq
  by_cases hodd : ∃ k, Odd k ∧ WalkN left right S k (rep (right z)) (left z)
  · rcases hodd with ⟨k₁, hk₁, hw₁⟩
    rcases heq.mp ⟨k₁, hk₁, hw₁⟩ with ⟨k₂, hk₂, hw₂⟩
    have hloop : WalkN left right S (k₁ + 1 + k₂) (rep (right z)) (rep (right z)) :=
      walkN_trans (walkN_trans hw₁ (walkN_one hstep)) (walkN_symm hw₂)
    have hodd_sum : Odd (k₁ + 1 + k₂) := by
      rcases hk₁ with ⟨a, rfl⟩
      rcases hk₂ with ⟨b, rfl⟩
      exact ⟨a + b + 1, by omega⟩
    exact hno (rep (right z)) (k₁ + 1 + k₂) hodd_sum hloop
  · rcases hrep_reach (left z) with ⟨k, hwk⟩
    rw [hrep] at hwk
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ho
    · have hodd' : Odd (m + m + 1) := ⟨m, by omega⟩
      have hwr : WalkN left right S (m + m + 1) (rep (right z)) (right z) :=
        walkN_trans hwk (walkN_one hstep)
      exact hodd (heq.mpr ⟨m + m + 1, hodd', hwr⟩)
    · exact hodd ⟨k, ho, hwk⟩

private lemma walkN_to_arrays {f n : ℕ} {left right : (Fin f → ZMod 2) → Fin n}
    {S : Set (Fin f → ZMod 2)} :
    ∀ {k : ℕ} {u v : Fin n}, WalkN left right S k u v →
      ∃ (edge : Fin k → Fin f → ZMod 2) (vertex : Fin (k + 1) → Fin n),
        (∀ j, edge j ∈ S) ∧ vertex 0 = u ∧ vertex (Fin.last k) = v ∧
        ∀ j : Fin k,
          (vertex j.castSucc = left (edge j) ∧ vertex j.succ = right (edge j)) ∨
          (vertex j.castSucc = right (edge j) ∧ vertex j.succ = left (edge j))
  | 0, u, _, h => by
      subst h
      exact ⟨Fin.elim0, fun _ => u, fun j => j.elim0, rfl, rfl, fun j => j.elim0⟩
  | k + 1, u, v, ⟨w, ⟨z, hz, hstep⟩, hrest⟩ => by
      rcases walkN_to_arrays hrest with ⟨edge', vertex', hedges', hv0', hvlast', hsteps'⟩
      refine ⟨Fin.cons z edge', Fin.cons u vertex', ?_, ?_, ?_, ?_⟩
      · intro j
        exact Fin.cases hz hedges' j
      · simp only [Fin.cons_zero]
      · have hlast : Fin.last (k + 1) = (Fin.last k).succ := Fin.ext rfl
        rw [hlast, Fin.cons_succ]
        exact hvlast'
      · intro j
        refine Fin.cases ?_ ?_ j
        · have h0c : (0 : Fin (k + 1)).castSucc = 0 := Fin.ext rfl
          rw [h0c, Fin.cons_zero, Fin.cons_zero, Fin.cons_succ, hv0']
          exact hstep
        · intro j'
          have hsc : j'.succ.castSucc = j'.castSucc.succ := Fin.ext rfl
          rw [hsc, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]
          exact hsteps' j'

private lemma walkN_of_segment {f n g : ℕ} {left right : (Fin f → ZMod 2) → Fin n}
    {S : Set (Fin f → ZMod 2)}
    (edge : Fin g → Fin f → ZMod 2) (vertex : Fin (g + 1) → Fin n)
    (hedges : ∀ j, edge j ∈ S)
    (hsteps : ∀ j : Fin g,
      (vertex j.castSucc = left (edge j) ∧ vertex j.succ = right (edge j)) ∨
      (vertex j.castSucc = right (edge j) ∧ vertex j.succ = left (edge j))) :
    ∀ (d a : ℕ) (ha : a + d ≤ g),
      WalkN left right S d (vertex ⟨a, by omega⟩) (vertex ⟨a + d, by omega⟩)
  | 0, a, _ => congrArg vertex (Fin.ext (Nat.add_zero a).symm)
  | d + 1, a, ha => by
      let j : Fin g := ⟨a, by omega⟩
      have hstep : Step left right S (vertex ⟨a, by omega⟩) (vertex ⟨a + 1, by omega⟩) :=
        ⟨edge j, hedges j, hsteps j⟩
      have hrest := walkN_of_segment edge vertex hedges hsteps d (a + 1) (by omega)
      have heq : (⟨a + 1 + d, by omega⟩ : Fin (g + 1)) = ⟨a + (d + 1), by omega⟩ :=
        Fin.ext (by dsimp only; omega)
      rw [heq] at hrest
      exact ⟨vertex ⟨a + 1, by omega⟩, hstep, hrest⟩

private lemma odd_cycle_of_odd_closed_walk {f n : ℕ}
    (left right : (Fin f → ZMod 2) → Fin n) (S : Set (Fin f → ZMod 2))
    (h : ∃ u k, Odd k ∧ WalkN left right S k u u) :
    ∃ (C : Finset (Fin f → ZMod 2)) (g : ℕ) (edge : Fin g → Fin f → ZMod 2)
      (vertex : Fin (g + 1) → Fin n),
      (∀ z ∈ C, z ∈ S) ∧
      Odd g ∧ Function.Injective edge ∧
      Function.Injective (fun pos : Fin g => vertex pos.castSucc) ∧
      C = Finset.univ.image edge ∧ vertex 0 = vertex (Fin.last g) ∧
      ∀ j : Fin g,
        (vertex j.castSucc = left (edge j) ∧ vertex j.succ = right (edge j)) ∨
        (vertex j.castSucc = right (edge j) ∧ vertex j.succ = left (edge j)) := by
  classical
  have hex : ∃ k, Odd k ∧ ∃ u, WalkN left right S k u u := by
    rcases h with ⟨u, k, hk, hw⟩
    exact ⟨k, hk, u, hw⟩
  let g := Nat.find hex
  have hg_spec : Odd g ∧ ∃ u, WalkN left right S g u u := Nat.find_spec hex
  have hg_odd : Odd g := hg_spec.1
  rcases hg_spec.2 with ⟨u, hwalk⟩
  have hmin : ∀ k < g, Odd k → ∀ v, ¬ WalkN left right S k v v :=
    fun k hk ho v hw => Nat.find_min hex hk ⟨ho, v, hw⟩
  rcases walkN_to_arrays hwalk with ⟨edge, vertex, hedges, hv0, hvlast, hsteps⟩
  have hv_eq : vertex 0 = vertex (Fin.last g) := hv0.trans hvlast.symm
  have hv_ne_lt : ∀ a b : Fin g, a.1 < b.1 → vertex a.castSucc ≠ vertex b.castSucc := by
    intro a b hab heqv
    have hseg1 : WalkN left right S (b.1 - a.1) (vertex a.castSucc) (vertex a.castSucc) := by
      have hw := walkN_of_segment edge vertex hedges hsteps (b.1 - a.1) a.1 (by omega)
      have hae : (⟨a.1, by omega⟩ : Fin (g + 1)) = a.castSucc := Fin.ext rfl
      have hbe : (⟨a.1 + (b.1 - a.1), by omega⟩ : Fin (g + 1)) = b.castSucc :=
        Fin.ext (by simp only [Fin.val_castSucc]; omega)
      rw [hae, hbe, ← heqv] at hw
      exact hw
    have hseg2 : WalkN left right S (g - b.1 + a.1) (vertex b.castSucc) (vertex b.castSucc) := by
      have hw1 := walkN_of_segment edge vertex hedges hsteps (g - b.1) b.1 (by omega)
      have hbe : (⟨b.1, by omega⟩ : Fin (g + 1)) = b.castSucc := Fin.ext rfl
      have hge : (⟨b.1 + (g - b.1), by omega⟩ : Fin (g + 1)) = Fin.last g :=
        Fin.ext (by simp only [Fin.val_last]; omega)
      rw [hbe, hge, ← hv_eq] at hw1
      have hw2 := walkN_of_segment edge vertex hedges hsteps a.1 0 (by omega)
      have h0e : (⟨0, by omega⟩ : Fin (g + 1)) = 0 := Fin.ext rfl
      have hae : (⟨0 + a.1, by omega⟩ : Fin (g + 1)) = a.castSucc :=
        Fin.ext (by simp only [Fin.val_castSucc]; omega)
      rw [h0e, hae, heqv] at hw2
      exact walkN_trans hw1 hw2
    rcases Nat.even_or_odd (b.1 - a.1) with ⟨r₁, hr₁⟩ | ho₁
    · rcases Nat.even_or_odd (g - b.1 + a.1) with ⟨r₂, hr₂⟩ | ho₂
      · rcases hg_odd with ⟨m, hm⟩
        omega
      · exact hmin (g - b.1 + a.1) (by omega) ho₂ (vertex b.castSucc) hseg2
    · exact hmin (b.1 - a.1) (by omega) ho₁ (vertex a.castSucc) hseg1
  have hv_inj : Function.Injective (fun pos : Fin g => vertex pos.castSucc) := by
    intro a b hab
    rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
    · exact absurd hab (hv_ne_lt a b hlt)
    · exact Fin.ext heq
    · exact absurd hab.symm (hv_ne_lt b a hgt)
  have hedge_inj : Function.Injective edge := by
    intro i j hij
    by_cases hg1 : g = 1
    · exact Fin.ext (by omega)
    · have hg3 : 3 ≤ g := by
        rcases hg_odd with ⟨m, hm⟩
        omega
      let next : Fin g → Fin g := fun x =>
        if hx : x.1 + 1 < g then ⟨x.1 + 1, hx⟩ else ⟨0, by omega⟩
      have hnext : ∀ x : Fin g, vertex x.succ = vertex (next x).castSucc := by
        intro x
        by_cases hx : x.1 + 1 < g
        · simp only [next, hx, ↓reduceDIte]
          exact congrArg vertex (Fin.ext rfl)
        · simp only [next, hx, ↓reduceDIte]
          have hxl : x.succ = Fin.last g :=
            Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
          have h0c : (⟨0, by omega⟩ : Fin g).castSucc = 0 := Fin.ext rfl
          rw [hxl, h0c, hv_eq]
      have hnext2 : ∀ x : Fin g, next (next x) ≠ x := by
        intro x hxx
        have hv := congrArg Fin.val hxx
        by_cases hx1 : x.1 + 1 < g
        · simp only [next, hx1, ↓reduceDIte] at hv
          by_cases hx2 : x.1 + 1 + 1 < g
          · simp only [hx2, ↓reduceDIte] at hv
            omega
          · simp only [hx2, ↓reduceDIte] at hv
            omega
        · simp only [next, hx1, ↓reduceDIte] at hv
          have h01 : 0 + 1 < g := by omega
          simp only [h01, ↓reduceDIte] at hv
          omega
      have hi := hsteps i
      have hj := hsteps j
      rw [hij] at hi
      rcases hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;> rcases hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
      · exact hv_inj (hi1.trans hj1.symm)
      · have h1 : i = next j := hv_inj (hi1.trans (hj2.symm.trans (hnext j)))
        have h2 : next i = j := hv_inj ((hnext i).symm.trans (hi2.trans hj1.symm))
        exact absurd (h2.symm ▸ h1.symm) (hnext2 i)
      · have h1 : i = next j := hv_inj (hi1.trans (hj2.symm.trans (hnext j)))
        have h2 : next i = j := hv_inj ((hnext i).symm.trans (hi2.trans hj1.symm))
        exact absurd (h2.symm ▸ h1.symm) (hnext2 i)
      · exact hv_inj (hi1.trans hj1.symm)
  refine ⟨Finset.univ.image edge, g, edge, vertex, ?_, hg_odd, hedge_inj, hv_inj, rfl, hv_eq, hsteps⟩
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩
  exact hedges j

private lemma no_two_color_of_cycle {f n g : ℕ}
    {left right : (Fin f → ZMod 2) → Fin n}
    (edge : Fin g → Fin f → ZMod 2) (vertex : Fin (g + 1) → Fin n)
    (hg : Odd g) (hv_eq : vertex 0 = vertex (Fin.last g))
    (hsteps : ∀ j : Fin g,
      (vertex j.castSucc = left (edge j) ∧ vertex j.succ = right (edge j)) ∨
      (vertex j.castSucc = right (edge j) ∧ vertex j.succ = left (edge j)))
    (c : Fin n → Bool) (hc : ∀ j : Fin g, c (left (edge j)) ≠ c (right (edge j))) : False := by
  classical
  have hflip : ∀ j : Fin g, c (vertex j.succ) = !c (vertex j.castSucc) := by
    intro j
    have hne : c (vertex j.castSucc) ≠ c (vertex j.succ) := by
      rcases hsteps j with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
        exact hc j
      · rw [h1, h2]
        exact (hc j).symm
    cases ha : c (vertex j.castSucc) <;> cases hb : c (vertex j.succ)
    · rw [ha, hb] at hne
      exact absurd rfl hne
    · rfl
    · rfl
    · rw [ha, hb] at hne
      exact absurd rfl hne
  have hpar : ∀ k (hk : k ≤ g),
      c (vertex ⟨k, Nat.lt_succ_of_le hk⟩) = if Even k then c (vertex 0) else !c (vertex 0) := by
    intro k
    induction k with
    | zero =>
        intro _
        have h0 : Even 0 := ⟨0, rfl⟩
        simp only [h0, ↓reduceIte]
        rfl
    | succ k ih =>
        intro hk
        have hk' : k ≤ g := Nat.le_of_succ_le hk
        have h1 : c (vertex ⟨k + 1, Nat.lt_succ_of_le hk⟩) = !c (vertex ⟨k, Nat.lt_succ_of_le hk'⟩) :=
          hflip ⟨k, hk⟩
        rw [h1, ih hk']
        by_cases he : Even k
        · have hnot : ¬ Even (k + 1) := by
            rcases he with ⟨r, rfl⟩
            rintro ⟨s, hs⟩
            omega
          simp only [he, hnot, ↓reduceIte]
        · have he' : Even (k + 1) := by
            rcases Nat.even_or_odd k with h | ⟨r, rfl⟩
            · exact absurd h he
            · exact ⟨r + 1, by omega⟩
          simp only [he, he', ↓reduceIte, Bool.not_not]
  have hfinal := hpar g le_rfl
  have hnotg : ¬ Even g := by
    rcases hg with ⟨m, rfl⟩
    rintro ⟨r, hr⟩
    omega
  simp only [hnotg, ↓reduceIte] at hfinal
  have hlast : (⟨g, Nat.lt_succ_self g⟩ : Fin (g + 1)) = Fin.last g := Fin.ext rfl
  rw [hlast, ← hv_eq] at hfinal
  cases hv : c (vertex 0) <;> rw [hv] at hfinal <;> exact absurd hfinal (by decide)

private lemma query_apply_snd_zero {f q : ℕ}
    (Q : ((Fin f → ZMod 2) × ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2))
    (h01 : Q (0, 1) = 0) (z : Fin f → ZMod 2) (t : ZMod 2) :
    Q (z, t) = Q (z, 0) := by
  have hsplit : (z, t) = (z, 0) + t • (0, 1) := by
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one, zero_add]
  rw [hsplit, map_add, map_smul, h01, smul_zero, add_zero]

private lemma zmod2_eq_zero_or_one (t : ZMod 2) : t = 0 ∨ t = 1 := by
  fin_cases t
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma card_ker_ge (f q : ℕ) (W : Submodule (ZMod 2) (Fin f → ZMod 2)) :
    Nat.card {L : (Fin f → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2) // W ≤ LinearMap.ker L} =
      2 ^ (q * (f - Module.finrank (ZMod 2) W)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := Fin f → ZMod 2
  let R := Fin q → ZMod 2
  let e₁ : {L : V →ₗ[ZMod 2] R // W ≤ LinearMap.ker L} ≃ ((V ⧸ W) →ₗ[ZMod 2] R) :=
    { toFun := fun L => W.liftQ L.1 L.2
      invFun := fun M => ⟨M.comp W.mkQ, fun v hv => by
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero W).mpr hv, map_zero]⟩
      left_inv := fun L => Subtype.ext (LinearMap.ext fun v => W.liftQ_apply L.1 (h := L.2) v)
      right_inv := fun M => LinearMap.ext fun x =>
        Submodule.Quotient.induction_on W x fun v =>
          W.liftQ_apply (M.comp W.mkQ) (h := _) v }
  let b := Module.finBasis (ZMod 2) (V ⧸ W)
  let e₂ : ((V ⧸ W) →ₗ[ZMod 2] R) ≃ (Fin (Module.finrank (ZMod 2) (V ⧸ W)) → R) :=
    (b.constr (ZMod 2)).toEquiv.symm
  rw [Nat.card_congr (e₁.trans e₂), Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  have hr : Module.finrank (ZMod 2) (V ⧸ W) + Module.finrank (ZMod 2) W = f := by
    have h0 := Submodule.finrank_quotient_add_finrank W
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h0
    exact h0
  have hd : Module.finrank (ZMod 2) (V ⧸ W) = f - Module.finrank (ZMod 2) W := by omega
  rw [hd]

private lemma card_avoid_all {α β : Type*} [Fintype α] [DecidableEq β]
    (cores : Finset β) (bad : α → β → Prop) :
    (Nat.card {a : α // ∀ C ∈ cores, ¬ bad a C} : ℤ) =
      ∑ T ∈ cores.powerset, (-1 : ℤ) ^ T.card *
        (Nat.card {a : α // ∀ C ∈ T, bad a C} : ℤ) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  have hpoint : ∀ a : α,
      ((if ∀ C ∈ cores, ¬ bad a C then (1 : ℕ) else 0 : ℕ) : ℤ) =
        ∑ T ∈ cores.powerset, if ∀ C ∈ T, bad a C then (-1 : ℤ) ^ T.card else 0 := by
    intro a
    let B := cores.filter (bad a)
    have hB_empty : (B = ∅) ↔ (∀ C ∈ cores, ¬ bad a C) := Finset.filter_eq_empty_iff
    have hpow : B.powerset = cores.powerset.filter (fun T => ∀ C ∈ T, bad a C) := by
      ext T
      simp only [Finset.mem_powerset, Finset.mem_filter, B, Finset.subset_iff]
      constructor
      · intro h
        exact ⟨fun C hCT => (h hCT).1, fun C hCT => (h hCT).2⟩
      · rintro ⟨h1, h2⟩ C hCT
        exact ⟨h1 hCT, h2 C hCT⟩
    rw [← Finset.sum_filter, ← hpow, Finset.sum_powerset_neg_one_pow_card]
    by_cases h : ∀ C ∈ cores, ¬ bad a C
    · have hBe : B = ∅ := hB_empty.mpr h
      simp only [hBe, ↓reduceIte]
      split_ifs
      exact Nat.cast_one
    · have hBne : B ≠ ∅ := fun hBe => h (hB_empty.mp hBe)
      simp only [hBne, ↓reduceIte]
      split_ifs
      exact Nat.cast_zero
  rw [Finset.sum_congr rfl (fun a _ => hpoint a), Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

end PEqualNP.Outside.L_lib_385

theorem PEqualNP.Outside.L_lib_385 : ∀ (f n : ℕ) (Y : ((Fin f → ZMod 2) × ZMod 2) → Fin n),
  let V := Fin f → ZMod 2
  let left := fun z : V => Y (z, 0)
  let right := fun ctx : V => Y (ctx, 1)
  let cycle := fun (C : Finset V) =>
    ∃ (g : ℕ) (edge : Fin g → V) (vertex : Fin (g + 1) → Fin n),
      Odd g ∧ Function.Injective edge ∧
      Function.Injective (fun pos : Fin g => vertex pos.castSucc) ∧
      C = Finset.univ.image edge ∧ vertex 0 = vertex (Fin.last g) ∧
      ∀ j : Fin g,
        (vertex j.castSucc = left (edge j) ∧ vertex j.succ = right (edge j)) ∨
        (vertex j.castSucc = right (edge j) ∧ vertex j.succ = left (edge j))
  let spanOf := fun (T : Finset (Finset V)) => Submodule.span (ZMod 2)
    {v : V | ∃ C ∈ T, ∃ a ∈ C, ∃ b ∈ C, v = a - b}
  ∃ cores : Finset (Finset V), (∀ E, E ∈ cores ↔ cycle E) ∧
    ∀ q : ℕ,
      let Query := (V × ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2)
      let works := fun (Q : Query) =>
        Q (0, 1) = 0 ∧ ∃ label : (Fin q → ZMod 2) → Fin n → Bool,
          ∀ w, label (Q w) (Y w) ≠ label (Q (w + (0, 1))) (Y (w + (0, 1)))
      (∀ Q : Query, works Q ↔
        Q (0, 1) = 0 ∧ ∀ C ∈ cores, ∃ a ∈ C, ∃ b ∈ C, Q (a, 0) ≠ Q (b, 0)) ∧
      (Nat.card {Q : Query // works Q} : ℤ) =
        ∑ T ∈ cores.powerset, (-1 : ℤ) ^ T.card *
          2 ^ (q * (f - Module.finrank (ZMod 2) (spanOf T))) := by
  classical
  intro f n Y V left right cycle spanOf
  let cores : Finset (Finset V) := Finset.univ.filter cycle
  have hcores : ∀ E, E ∈ cores ↔ cycle E := by
    intro E
    simp only [cores, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨cores, hcores, fun q => ?_⟩
  intro Query works
  have hchar : ∀ Q : Query, works Q ↔
      Q (0, 1) = 0 ∧ ∀ C ∈ cores, ∃ a ∈ C, ∃ b ∈ C, Q (a, 0) ≠ Q (b, 0) := by
    intro Q
    constructor
    · rintro ⟨h01, label, hlabel⟩
      refine ⟨h01, fun C hC => ?_⟩
      by_contra hno
      have hsame : ∀ a ∈ C, ∀ b ∈ C, Q (a, 0) = Q (b, 0) := by
        intro a ha b hb
        by_contra hne
        exact hno ⟨a, ha, b, hb, hne⟩
      rcases (hcores C).mp hC with ⟨g, edge, vertex, hg, _, _, rfl, hv_eq, hsteps⟩
      have hgpos : 0 < g := by
        rcases hg with ⟨m, rfl⟩
        omega
      let j0 : Fin g := ⟨0, hgpos⟩
      let r := Q (edge j0, 0)
      refine PEqualNP.Outside.L_lib_385.no_two_color_of_cycle edge vertex hg hv_eq hsteps
        (label r) (fun j => ?_)
      have hjr : Q (edge j, 0) = r :=
        hsame (edge j) (Finset.mem_image_of_mem edge (Finset.mem_univ j))
          (edge j0) (Finset.mem_image_of_mem edge (Finset.mem_univ j0))
      have hw := hlabel (edge j, 0)
      have hsum : (edge j, (0 : ZMod 2)) + (0, 1) = (edge j, 1) := by
        ext <;> simp
      rw [hsum, PEqualNP.Outside.L_lib_385.query_apply_snd_zero Q h01 (edge j) 1, hjr] at hw
      exact hw
    · rintro ⟨h01, hall⟩
      refine ⟨h01, ?_⟩
      have hfiber : ∀ r : Fin q → ZMod 2,
          ∃ c : Fin n → Bool, ∀ z : V, Q (z, 0) = r → c (left z) ≠ c (right z) := by
        intro r
        refine PEqualNP.Outside.L_lib_385.two_color_of_no_odd_closed_walk
          left right {z : V | Q (z, 0) = r} ?_
        intro u k hk hwalk
        rcases PEqualNP.Outside.L_lib_385.odd_cycle_of_odd_closed_walk
            left right {z : V | Q (z, 0) = r} ⟨u, k, hk, hwalk⟩ with
          ⟨C, g, edge, vertex, hCS, hg, hinjE, hinjV, hCeq, hv_eq, hsteps⟩
        have hCmem : C ∈ cores :=
          (hcores C).mpr ⟨g, edge, vertex, hg, hinjE, hinjV, hCeq, hv_eq, hsteps⟩
        rcases hall C hCmem with ⟨a, ha, b, hb, hne⟩
        exact hne ((hCS a ha).trans (hCS b hb).symm)
      refine ⟨fun r => Classical.choose (hfiber r), fun w => ?_⟩
      rcases w with ⟨z, t⟩
      have hQ1 : Q (z, t) = Q (z, 0) := PEqualNP.Outside.L_lib_385.query_apply_snd_zero Q h01 z t
      have hQ2 : Q ((z, t) + (0, 1)) = Q (z, 0) := by
        rw [map_add, h01, add_zero, hQ1]
      rw [hQ1, hQ2]
      have hc := Classical.choose_spec (hfiber (Q (z, 0))) z rfl
      rcases PEqualNP.Outside.L_lib_385.zmod2_eq_zero_or_one t with rfl | rfl
      · have hsum : (z, (0 : ZMod 2)) + (0, 1) = (z, 1) := by
          ext <;> simp
        rw [hsum]
        exact hc
      · have hsum : (z, (1 : ZMod 2)) + (0, 1) = (z, 0) := by
          ext
          · simp
          · change (1 : ZMod 2) + 1 = 0
            decide
        rw [hsum]
        exact hc.symm
  refine ⟨hchar, ?_⟩
  let CtxMap := V →ₗ[ZMod 2] (Fin q → ZMod 2)
  have hfin : Finite CtxMap := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let bad : CtxMap → Finset V → Prop := fun L C => ∀ a ∈ C, ∀ b ∈ C, L a = L b
  let eQ : {Q : Query // works Q} ≃ {L : CtxMap // ∀ C ∈ cores, ¬ bad L C} :=
    { toFun := fun Q =>
        ⟨Q.1.comp (LinearMap.inl (ZMod 2) V (ZMod 2)), fun C hC hbad => by
          rcases ((hchar Q.1).mp Q.2).2 C hC with ⟨a, ha, b, hb, hne⟩
          exact hne (hbad a ha b hb)⟩
      invFun := fun L =>
        ⟨L.1.comp (LinearMap.fst (ZMod 2) V (ZMod 2)), (hchar _).mpr
          ⟨by change L.1 0 = 0; exact map_zero L.1, fun C hC => by
            by_contra hno
            refine L.2 C hC (fun a ha b hb => ?_)
            by_contra hne
            exact hno ⟨a, ha, b, hb, hne⟩⟩⟩
      left_inv := fun Q => Subtype.ext (LinearMap.ext fun w => by
        rcases w with ⟨z, t⟩
        exact (PEqualNP.Outside.L_lib_385.query_apply_snd_zero Q.1 ((hchar Q.1).mp Q.2).1 z t).symm)
      right_inv := fun L => Subtype.ext (LinearMap.ext fun z => rfl) }
  rw [Nat.card_congr eQ,
    @PEqualNP.Outside.L_lib_385.card_avoid_all CtxMap (Finset V) (Fintype.ofFinite CtxMap) _ cores bad]
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  have hpred : ∀ L : CtxMap, (∀ C ∈ T, bad L C) ↔ spanOf T ≤ LinearMap.ker L := by
    intro L
    rw [Submodule.span_le]
    constructor
    · intro h v hv
      rcases hv with ⟨C, hCT, a, haC, b, hbC, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact h C hCT a haC b hbC
    · intro h C hCT a haC b hbC
      have hv : a - b ∈ LinearMap.ker L := h ⟨C, hCT, a, haC, b, hbC, rfl⟩
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hv
      exact hv
  rw [Nat.card_congr (Equiv.subtypeEquivRight hpred),
    PEqualNP.Outside.L_lib_385.card_ker_ge f q (spanOf T), Nat.cast_pow, Nat.cast_ofNat]

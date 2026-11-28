import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_455_aux

abbrev F2 := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F2

lemma f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma f2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

lemma f2_sub_eq_add {n : ℕ} (x y : Vec n) : x - y = x + y := by
  funext i
  rcases f2_cases (x i) with hx | hx <;> rcases f2_cases (y i) with hy | hy <;>
    (simp only [Pi.sub_apply, Pi.add_apply, hx, hy]; decide)

def sgn (a : F2) : ℤ := if a = 0 then 1 else -1

lemma sgn_add (a b : F2) : sgn (a + b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b <;> decide

lemma sgn_mul_self (a : F2) : sgn a * sgn a = 1 := by
  fin_cases a <;> decide

lemma abs_sgn (a : F2) : |sgn a| = 1 := by
  fin_cases a <;> decide

lemma sgn_mul_ne (a b : F2) (h : a ≠ b) : sgn a * sgn b = -1 := by
  rcases f2_cases a with rfl | rfl <;> rcases f2_cases b with rfl | rfl
  · exact absurd rfl h
  · decide
  · decide
  · exact absurd rfl h

lemma card_sub_eq_pow {n : ℕ} (U : Submodule F2 (Vec n)) :
    Nat.card U = 2 ^ Module.finrank F2 U := by
  classical
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F2), ZMod.card 2]

lemma card_coset_eq_sub {n : ℕ} (a : Vec n) (U : Submodule F2 (Vec n)) :
    Nat.card {x : Vec n // x - a ∈ U} = Nat.card U := by
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1 - a, x.2⟩
      invFun := fun u => ⟨a + u.1, by simp [add_sub_cancel_left, u.2]⟩
      left_inv := fun x => by apply Subtype.ext; simp
      right_inv := fun u => by apply Subtype.ext; simp }

lemma sum_sgn_linear_of_zero {n : ℕ} (U : Submodule F2 (Vec n)) [Fintype U] (L : Vec n → F2)
    (hall : ∀ u ∈ U, L u = 0) :
    (∑ u : U, sgn (L u.val)) = (Nat.card U : ℤ) := by
  have h1 : ∀ u : U, sgn (L u.val) = 1 := fun u => by rw [hall u.val u.2]; rfl
  rw [Finset.sum_congr rfl (fun u _ => h1 u)]
  simp [Nat.card_eq_fintype_card]

lemma sum_sgn_linear_of_ne {n : ℕ} (U : Submodule F2 (Vec n)) [Fintype U] (L : Vec n → F2)
    (hL : ∀ u ∈ U, ∀ v ∈ U, L (u + v) = L u + L v)
    (hne : ¬ ∀ u ∈ U, L u = 0) :
    (∑ u : U, sgn (L u.val)) = 0 := by
  push Not at hne
  rcases hne with ⟨u0, hu0, hne0⟩
  have hu01 : L u0 = 1 := (f2_cases (L u0)).resolve_left hne0
  have hshift : (∑ u : U, sgn (L (u.val + u0))) = ∑ u : U, sgn (L u.val) := by
    refine Finset.sum_bij (fun (u : U) _ => (⟨u.val + u0, U.add_mem u.2 hu0⟩ : U))
      (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · intro a _ b _ h
      apply Subtype.ext
      have h1 := congrArg (Subtype.val : U → Vec n) h
      simpa using add_right_cancel h1
    · intro b _
      refine ⟨⟨b.val - u0, U.sub_mem b.2 hu0⟩, Finset.mem_univ _, ?_⟩
      apply Subtype.ext; simp
  have hneg : (∑ u : U, sgn (L (u.val + u0))) = -(∑ u : U, sgn (L u.val)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [hL u.val u.2 u0 hu0, hu01, sgn_add]
    change sgn (L u.val) * (-1) = -sgn (L u.val)
    ring
  linarith

structure QuadForm (n : ℕ) where
  f : Vec n → F2
  B : Vec n → Vec n → F2
  hB : ∀ u v, B u v = f (u + v) + f u + f v + f 0
  hquad : ∀ p u v, f (p + u + v) + f (p + u) + f (p + v) + f p = B u v

namespace QuadForm

variable {n : ℕ} (Q : QuadForm n)

lemma B_symm (u v : Vec n) : Q.B u v = Q.B v u := by
  rw [Q.hB, Q.hB, add_comm u v]; ring

lemma B_self (u : Vec n) : Q.B u u = 0 := by
  rw [Q.hB]
  have h0 : u + u = 0 := by funext i; exact f2_add_self (u i)
  rw [h0]
  have h1 := f2_add_self (Q.f 0)
  have h2 := f2_add_self (Q.f u)
  calc Q.f 0 + Q.f u + Q.f u + Q.f 0
      = (Q.f 0 + Q.f 0) + (Q.f u + Q.f u) := by ring
    _ = 0 := by rw [h1, h2, add_zero]

lemma B_zero_left (v : Vec n) : Q.B 0 v = 0 := by
  rw [Q.hB, zero_add]
  have h1 := f2_add_self (Q.f v)
  have h2 := f2_add_self (Q.f 0)
  calc Q.f v + Q.f 0 + Q.f v + Q.f 0
      = (Q.f v + Q.f v) + (Q.f 0 + Q.f 0) := by ring
    _ = 0 := by rw [h1, h2, add_zero]

lemma B_add_left (u w v : Vec n) : Q.B (u + w) v = Q.B u v + Q.B w v := by
  have h1 := Q.hquad u w v
  have h2 := Q.hB u v
  have h3 := Q.hB (u + w) v
  have hz : ∀ a : F2, a + a = 0 := f2_add_self
  have hsum : Q.B u v + Q.B w v =
      (Q.f (u + v) + Q.f u + Q.f v + Q.f 0) +
      (Q.f (u + w + v) + Q.f (u + w) + Q.f (u + v) + Q.f u) := by
    rw [← h1, ← h2]
  rw [h3, hsum]
  calc Q.f (u + w + v) + Q.f (u + w) + Q.f v + Q.f 0
      = Q.f (u + w + v) + Q.f (u + w) + Q.f v + Q.f 0 +
        (Q.f (u + v) + Q.f (u + v)) + (Q.f u + Q.f u) := by rw [hz, hz, add_zero, add_zero]
    _ = Q.f (u + v) + Q.f u + Q.f v + Q.f 0 +
        (Q.f (u + w + v) + Q.f (u + w) + Q.f (u + v) + Q.f u) := by ring

lemma B_add_right (u v w : Vec n) : Q.B u (v + w) = Q.B u v + Q.B u w := by
  rw [Q.B_symm, Q.B_add_left, Q.B_symm, Q.B_symm w u]

lemma B_smul_left (c : F2) (u v : Vec n) : Q.B (c • u) v = c * Q.B u v := by
  rcases f2_cases c with rfl | rfl
  · simp [Q.B_zero_left]
  · simp

lemma B_smul_right (c : F2) (u v : Vec n) : Q.B u (c • v) = c * Q.B u v := by
  rw [Q.B_symm, Q.B_smul_left, Q.B_symm]

def orth (U : Submodule F2 (Vec n)) : Submodule F2 (Vec n) :=
  { carrier := {x : Vec n | ∀ u ∈ U, Q.B x u = 0},
    zero_mem' := fun _ _ => Q.B_zero_left _,
    smul_mem' := fun c _ hx u hu => by rw [Q.B_smul_left, hx u hu, mul_zero], add_mem' := fun hx hy u hu => by rw [Q.B_add_left, hx u hu, hy u hu, add_zero] }

def rad : Submodule F2 (Vec n) := Q.orth ⊤

lemma mem_rad_iff (u : Vec n) : u ∈ Q.rad ↔ ∀ v : Vec n, Q.B u v = 0 := by
  constructor
  · intro h v; exact h v trivial
  · intro h v _; exact h v

lemma rad_le_orth (U : Submodule F2 (Vec n)) : Q.rad ≤ Q.orth U :=
  fun _ hx u _ => hx u trivial

lemma finrank_orth_add_of_rad_le (U : Submodule F2 (Vec n)) (hRU : Q.rad ≤ U) :
    Module.finrank F2 (Q.orth U) + Module.finrank F2 U = n + Module.finrank F2 Q.rad := by
  classical
  let eU := Module.finBasis F2 U
  let dU := Module.finrank F2 U
  let M : Matrix (Fin n) (Fin dU) F2 := fun i j => Q.B (Pi.single i 1) (eU j).val
  let phi : Vec n →ₗ[F2] (Fin dU → F2) :=
    { toFun := fun x j => Q.B x (eU j).val
      map_add' := fun x y => by funext j; exact Q.B_add_left x y (eU j).val
      map_smul' := fun c x => by funext j; exact Q.B_smul_left c x (eU j).val }
  let psi : (Fin dU → F2) →ₗ[F2] Vec n :=
    { toFun := fun y i => Q.B (Pi.single i 1) (∑ j : Fin dU, y j • (eU j).val)
      map_add' := fun y1 y2 => by
        funext i
        have hsum : (∑ j : Fin dU, (y1 + y2) j • (eU j).val) =
            (∑ j : Fin dU, y1 j • (eU j).val) + (∑ j : Fin dU, y2 j • (eU j).val) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => by simp [add_smul])
        rw [hsum, Q.B_add_right]
        rfl
      map_smul' := fun c y => by
        funext i
        have hsum : (∑ j : Fin dU, (c • y) j • (eU j).val) =
            c • (∑ j : Fin dU, y j • (eU j).val) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun j _ => by simp [mul_smul])
        rw [hsum, Q.B_smul_right]
        rfl }
  have hphi_eq : phi = M.transpose.mulVecLin := by
    apply LinearMap.ext
    intro x
    funext j
    dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, Matrix.transpose_apply]
    have hx : x = ∑ i : Fin n, x i • Pi.single i (1 : F2) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp
      · intro i _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro h; exact (h (Finset.mem_univ k)).elim
    conv_lhs => rw [hx]
    have hlin : ∀ (s : Finset (Fin n)) (v : Fin n → Vec n) (w : Vec n),
        Q.B (∑ i ∈ s, v i) w = ∑ i ∈ s, Q.B (v i) w := by
      intro s v w
      induction s using Finset.induction_on with
      | empty => simp [Q.B_zero_left]
      | insert a s ha ih => rw [Finset.sum_insert ha, Q.B_add_left, ih, Finset.sum_insert ha]
    rw [hlin]
    refine Finset.sum_congr rfl (fun i _ => by
      dsimp only [M]
      rw [Q.B_smul_left, mul_comm])
  have hpsi_eq : psi = M.mulVecLin := by
    apply LinearMap.ext
    intro y
    funext i
    dsimp only [psi, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, M]
    have hlin : ∀ (s : Finset (Fin dU)) (v : Fin dU → Vec n) (w : Vec n),
        Q.B w (∑ j ∈ s, v j) = ∑ j ∈ s, Q.B w (v j) := by
      intro s v w
      induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Q.B_symm, Q.B_zero_left, Finset.sum_empty]
      | insert a s ha ih => rw [Finset.sum_insert ha, Q.B_add_right, ih, Finset.sum_insert ha]
    rw [hlin]
    refine Finset.sum_congr rfl (fun j _ => by rw [Q.B_smul_right, mul_comm])
  have hcoe_sum : ∀ (f : Fin dU → U), (∑ j : Fin dU, f j : U).val = ∑ j : Fin dU, (f j).val := by
    intro f
    exact Submodule.coe_sum U f Finset.univ
  have hker_phi : LinearMap.ker phi = Q.orth U := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx u hu
      have hrep : (⟨u, hu⟩ : U) = ∑ j : Fin dU, eU.repr ⟨u, hu⟩ j • eU j := (eU.sum_repr ⟨u, hu⟩).symm
      have hu_eq : u = ∑ j : Fin dU, eU.repr ⟨u, hu⟩ j • (eU j).val := by
        have h1 := congrArg (Subtype.val : U → Vec n) hrep
        rw [hcoe_sum] at h1
        exact h1
      rw [hu_eq]
      have hlin : ∀ (s : Finset (Fin dU)) (v : Fin dU → Vec n),
          Q.B x (∑ j ∈ s, v j) = ∑ j ∈ s, Q.B x (v j) := by
        intro s v
        induction s using Finset.induction_on with
        | empty => rw [Finset.sum_empty, Q.B_symm, Q.B_zero_left, Finset.sum_empty]
        | insert a s ha ih => rw [Finset.sum_insert ha, Q.B_add_right, ih, Finset.sum_insert ha]
      rw [hlin]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [Q.B_smul_right]
      have hj := congrFun hx j
      dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hj
      rw [hj, mul_zero]
    · intro hx
      funext j
      exact hx (eU j).val (eU j).2
  have hker_psi_rk : Module.finrank F2 (LinearMap.ker psi) = Module.finrank F2 Q.rad := by
    let iso : LinearMap.ker psi ≃ₗ[F2] Q.rad :=
      { toFun := fun y =>
          ⟨∑ j : Fin dU, y.1 j • (eU j).val, by
            rw [Q.mem_rad_iff]
            intro v
            have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : F2) := by
              funext k
              rw [Finset.sum_apply, Finset.sum_eq_single k]
              · simp
              · intro i _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
              · intro h; exact (h (Finset.mem_univ k)).elim
            rw [Q.B_symm, hv]
            have hlin : ∀ (s : Finset (Fin n)) (g : Fin n → Vec n) (w : Vec n),
                Q.B (∑ i ∈ s, g i) w = ∑ i ∈ s, Q.B (g i) w := by
              intro s g w
              induction s using Finset.induction_on with
              | empty => simp [Q.B_zero_left]
              | insert a s ha ih => rw [Finset.sum_insert ha, Q.B_add_left, ih, Finset.sum_insert ha]
            rw [hlin]
            refine Finset.sum_eq_zero (fun i _ => ?_)
            rw [Q.B_smul_left]
            have hi := congrFun (LinearMap.mem_ker.mp y.2) i
            dsimp only [psi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hi
            rw [hi, mul_zero]⟩
        invFun := fun r =>
          ⟨fun j => eU.repr ⟨r.1, hRU r.2⟩ j, by
            rw [LinearMap.mem_ker]
            funext i
            dsimp only [psi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
            have hrep : (⟨r.1, hRU r.2⟩ : U) = ∑ j : Fin dU, eU.repr ⟨r.1, hRU r.2⟩ j • eU j :=
              (eU.sum_repr ⟨r.1, hRU r.2⟩).symm
            have hr_eq : r.1 = ∑ j : Fin dU, eU.repr ⟨r.1, hRU r.2⟩ j • (eU j).val := by
              have h1 := congrArg (Subtype.val : U → Vec n) hrep
              rw [hcoe_sum] at h1
              exact h1
            rw [← hr_eq, Q.B_symm]
            exact (Q.mem_rad_iff r.1).mp r.2 _⟩
        left_inv := fun y => by
          apply Subtype.ext
          funext j
          have heq : (⟨∑ k : Fin dU, y.1 k • (eU k).val, hRU (by
              rw [Q.mem_rad_iff]
              intro v
              have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : F2) := by
                funext k
                rw [Finset.sum_apply, Finset.sum_eq_single k]
                · simp
                · intro i _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
                · intro h; exact (h (Finset.mem_univ k)).elim
              rw [Q.B_symm, hv]
              have hlin : ∀ (s : Finset (Fin n)) (g : Fin n → Vec n) (w : Vec n),
                  Q.B (∑ i ∈ s, g i) w = ∑ i ∈ s, Q.B (g i) w := by
                intro s g w
                induction s using Finset.induction_on with
                | empty => simp [Q.B_zero_left]
                | insert a s ha ih => rw [Finset.sum_insert ha, Q.B_add_left, ih, Finset.sum_insert ha]
              rw [hlin]
              refine Finset.sum_eq_zero (fun i _ => ?_)
              rw [Q.B_smul_left]
              have hi := congrFun (LinearMap.mem_ker.mp y.2) i
              dsimp only [psi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hi
              rw [hi, mul_zero])⟩ : U) = ∑ k : Fin dU, y.1 k • eU k := by
            apply Subtype.ext
            rw [hcoe_sum]
            rfl
          have hfsum : ∀ (s : Finset (Fin dU)) (g : Fin dU → (Fin dU →₀ F2)),
              (∑ c ∈ s, g c) j = ∑ c ∈ s, g c j := by
            intro s g
            induction s using Finset.induction_on with
            | empty => simp
            | insert a s ha ih => rw [Finset.sum_insert ha, Finsupp.add_apply, ih, Finset.sum_insert ha]
          dsimp only
          rw [heq, map_sum, hfsum, Finset.sum_eq_single j]
          · simp
          · intro c _ hne
            simp [Finsupp.single_apply, hne]
          · intro h; exact (h (Finset.mem_univ j)).elim
        right_inv := fun r => by
          apply Subtype.ext
          dsimp only
          have hrep : (⟨r.1, hRU r.2⟩ : U) = ∑ j : Fin dU, eU.repr ⟨r.1, hRU r.2⟩ j • eU j :=
            (eU.sum_repr ⟨r.1, hRU r.2⟩).symm
          have h1 := congrArg (Subtype.val : U → Vec n) hrep
          rw [hcoe_sum] at h1
          exact h1.symm
        map_add' := fun y1 y2 => by
          apply Subtype.ext
          dsimp only [Submodule.coe_add, Pi.add_apply]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => by simp [add_smul])
        map_smul' := fun c y => by
          apply Subtype.ext
          dsimp only [Submodule.coe_smul_of_tower, Pi.smul_apply, RingHom.id_apply]
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun j _ => by simp [mul_smul]) }
    exact iso.finrank_eq
  have hrk_eq : Module.finrank F2 (LinearMap.range phi) = Module.finrank F2 (LinearMap.range psi) := by
    rw [hphi_eq, hpsi_eq]
    simpa [Matrix.rank] using Matrix.rank_transpose M
  have hrn1 := LinearMap.finrank_range_add_finrank_ker phi
  have hrn2 := LinearMap.finrank_range_add_finrank_ker psi
  rw [hker_phi] at hrn1
  rw [hker_psi_rk] at hrn2
  have hn1 : Module.finrank F2 (Vec n) = n := by simp [Vec]
  have hd1 : Module.finrank F2 (Fin dU → F2) = dU := by simp
  rw [hn1] at hrn1
  rw [hd1] at hrn2
  omega

lemma orth_inf_eq_sup_orth (A B : Submodule F2 (Vec n)) (hRA : Q.rad ≤ A) (hRB : Q.rad ≤ B) :
    Q.orth (A ⊓ B) = Q.orth A ⊔ Q.orth B := by
  have hle : Q.orth A ⊔ Q.orth B ≤ Q.orth (A ⊓ B) := by
    refine sup_le ?_ ?_
    · intro x hx u hu; exact hx u hu.1
    · intro x hx u hu; exact hx u hu.2
  have hinf_eq : Q.orth A ⊓ Q.orth B = Q.orth (A ⊔ B) := by
    ext x
    constructor
    · intro hx u hu
      rcases Submodule.mem_sup.mp hu with ⟨a, ha, b, hb, rfl⟩
      rw [Q.B_add_right, hx.1 a ha, hx.2 b hb, add_zero]
    · intro hx
      exact ⟨fun a ha => hx a (Submodule.mem_sup_left ha),
        fun b hb => hx b (Submodule.mem_sup_right hb)⟩
  have hrA := Q.finrank_orth_add_of_rad_le A hRA
  have hrB := Q.finrank_orth_add_of_rad_le B hRB
  have hrInf := Q.finrank_orth_add_of_rad_le (A ⊓ B) (le_inf hRA hRB)
  have hrSup := Q.finrank_orth_add_of_rad_le (A ⊔ B) (le_sup_of_le_left hRA)
  have hmod1 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hmod2 := Submodule.finrank_sup_add_finrank_inf_eq (Q.orth A) (Q.orth B)
  rw [hinf_eq] at hmod2
  have hrk : Module.finrank F2 ↥(Q.orth A ⊔ Q.orth B) = Module.finrank F2 ↥(Q.orth (A ⊓ B)) := by
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hrk).symm

lemma finrank_sub_rad_even_aux : ∀ (k : ℕ) (W : Submodule F2 (Vec n)),
    Module.finrank F2 W = k →
    Even (Module.finrank F2 W - Module.finrank F2 ↥(W ⊓ Q.orth W)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro W hWk
    by_cases heq : W ≤ Q.orth W
    · have hinf : W ⊓ Q.orth W = W := inf_eq_left.mpr heq
      rw [hinf, Nat.sub_self]
      exact ⟨0, rfl⟩
    · have hex : ∃ e1 ∈ W, ∃ e2 ∈ W, Q.B e1 e2 = 1 := by
        have hnot : ¬ ∀ x ∈ W, ∀ y ∈ W, Q.B x y = 0 := fun h => heq h
        push Not at hnot
        rcases hnot with ⟨e1, he1, e2, he2, hne⟩
        exact ⟨e1, he1, e2, he2, (f2_cases (Q.B e1 e2)).resolve_left hne⟩
      rcases hex with ⟨e1, he1, e2, he2, hB12⟩
      let W' : Submodule F2 (Vec n) :=
        W ⊓ { carrier := {w : Vec n | Q.B e1 w = 0 ∧ Q.B e2 w = 0},
              zero_mem' := ⟨by rw [Q.B_symm, Q.B_zero_left], by rw [Q.B_symm, Q.B_zero_left]⟩,
              smul_mem' := fun c _ hx => ⟨by rw [Q.B_smul_right, hx.1, mul_zero],
                by rw [Q.B_smul_right, hx.2, mul_zero]⟩, add_mem' := fun hx hy => ⟨by rw [Q.B_add_right, hx.1, hy.1, add_zero],
                by rw [Q.B_add_right, hx.2, hy.2, add_zero]⟩ }
      let phi : W →ₗ[F2] (Fin 2 → F2) :=
        { toFun := fun w i => if i = 0 then Q.B e1 w.val else Q.B e2 w.val
          map_add' := fun x y => by
            funext i
            dsimp only [Pi.add_apply]
            split_ifs
            · exact Q.B_add_right e1 x.1 y.1
            · exact Q.B_add_right e2 x.1 y.1
          map_smul' := fun c x => by
            funext i
            dsimp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
            split_ifs
            · exact Q.B_smul_right c e1 x.1
            · exact Q.B_smul_right c e2 x.1 }
      have hsurj : Function.Surjective phi := by
        intro t
        refine ⟨⟨t 1 • e1 + t 0 • e2, W.add_mem (W.smul_mem _ he1) (W.smul_mem _ he2)⟩, ?_⟩
        funext i
        fin_cases i
        · simp [phi, Q.B_add_right, Q.B_smul_right, Q.B_self, hB12]
        · simp [phi, Q.B_add_right, Q.B_smul_right, Q.B_self, Q.B_symm e2 e1, hB12]
      have hrng : Module.finrank F2 (LinearMap.range phi) = 2 := by
        rw [LinearMap.range_eq_top.mpr hsurj]
        simp
      have hker_eq : Module.finrank F2 (LinearMap.ker phi) = Module.finrank F2 W' := by
        let e : LinearMap.ker phi ≃ₗ[F2] W' :=
          { toFun := fun w => ⟨w.1.1, w.1.2,
              by have h0 := congrFun (LinearMap.mem_ker.mp w.2) 0
                 dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
                 exact h0,
              by have h1 := congrFun (LinearMap.mem_ker.mp w.2) 1
                 dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h1
                 exact h1⟩
            invFun := fun w => ⟨⟨w.1, w.2.1⟩, LinearMap.mem_ker.mpr (by
              funext i; fin_cases i <;> [exact w.2.2.1; exact w.2.2.2])⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        exact e.finrank_eq
      have hrn := LinearMap.finrank_range_add_finrank_ker phi
      rw [hrng, hker_eq, hWk] at hrn
      have hrad_eq : W' ⊓ Q.orth W' = W ⊓ Q.orth W := by
        ext x
        constructor
        · rintro ⟨⟨hxW, hx1, hx2⟩, hxorth⟩
          refine ⟨hxW, fun w hw => ?_⟩
          let w' := w + Q.B e2 w • e1 + Q.B e1 w • e2
          have hw'W' : w' ∈ W' := by
            refine ⟨W.add_mem (W.add_mem hw (W.smul_mem _ he1)) (W.smul_mem _ he2), ?_, ?_⟩
            · simp only [w', Q.B_add_right, Q.B_smul_right, Q.B_self, mul_zero, add_zero, hB12, mul_one]
              exact f2_add_self _
            · simp only [w', Q.B_add_right, Q.B_smul_right, Q.B_self, mul_zero, add_zero,
                Q.B_symm e2 e1, hB12, mul_one]
              exact f2_add_self _
          have h0 := hxorth w' hw'W'
          simp only [w', Q.B_add_right, Q.B_smul_right, Q.B_symm x e1, hx1, Q.B_symm x e2, hx2,
            mul_zero, add_zero] at h0
          exact h0
        · rintro ⟨hxW, hxorth⟩
          exact ⟨⟨hxW, Q.B_symm x e1 ▸ hxorth e1 he1, Q.B_symm x e2 ▸ hxorth e2 he2⟩,
            fun w hw => hxorth w hw.1⟩
      have hW'lt : Module.finrank F2 W' < k := by omega
      have hih := ih (Module.finrank F2 W') hW'lt W' rfl
      rw [hrad_eq] at hih
      have hle : Module.finrank F2 ↥(W ⊓ Q.orth W) ≤ Module.finrank F2 W' := by
        rw [← hrad_eq]
        exact Submodule.finrank_mono inf_le_left
      rcases hih with ⟨m', hm'⟩
      refine ⟨m' + 1, ?_⟩
      omega

lemma finrank_sub_rad_even : Even (n - Module.finrank F2 Q.rad) := by
  have h := Q.finrank_sub_rad_even_aux n ⊤ (by simp [Vec])
  have htop : (⊤ : Submodule F2 (Vec n)) ⊓ Q.orth ⊤ = Q.rad := by
    simp [rad]
  have hn : Module.finrank F2 (⊤ : Submodule F2 (Vec n)) = n := by simp [Vec]
  rwa [htop, hn] at h

noncomputable def Wsum (a : Vec n) (U : Submodule F2 (Vec n)) : ℤ :=
  @Finset.sum U ℤ _ (@Finset.univ U (Fintype.ofFinite _)) (fun u => sgn (Q.f (a + u.val)))

lemma Wsum_eq_sum (a : Vec n) (U : Submodule F2 (Vec n)) [Fintype U] :
    Q.Wsum a U = ∑ u : U, sgn (Q.f (a + u.val)) := by
  dsimp only [Wsum]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x; simp

lemma Wsum_sq_cases (a : Vec n) (U : Submodule F2 (Vec n)) :
    ((∀ w ∈ U ⊓ Q.orth U, Q.f (a + w) = Q.f a) →
      (Q.Wsum a U) ^ 2 = (Nat.card U : ℤ) * (Nat.card ↥(U ⊓ Q.orth U) : ℤ)) ∧
    ((¬ ∀ w ∈ U ⊓ Q.orth U, Q.f (a + w) = Q.f a) → (Q.Wsum a U) ^ 2 = 0) := by
  classical
  have hsq : (Q.Wsum a U) ^ 2 =
      ∑ w : U, sgn (Q.f (a + w.val) + Q.f a) * (∑ u : U, sgn (Q.B u.val w.val)) := by
    rw [Q.Wsum_eq_sum, sq, Finset.sum_mul_sum]
    have hbij : (∑ p : U × U, sgn (Q.f (a + p.1.val)) * sgn (Q.f (a + p.2.val))) =
        ∑ p : U × U, sgn (Q.f (a + p.1.val)) * sgn (Q.f (a + p.1.val + p.2.val)) := by
      refine Finset.sum_bij (fun (p : U × U) _ => (p.1, ⟨p.2.val - p.1.val, U.sub_mem p.2.2 p.1.2⟩))
        (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · rintro ⟨u1, v1⟩ _ ⟨u2, v2⟩ _ h
        rcases Prod.mk.inj h with ⟨rfl, hv⟩
        congr 1
        apply Subtype.ext
        have hv' := congrArg (Subtype.val : U → Vec n) hv
        simpa using sub_left_inj.mp hv'
      · rintro ⟨u, w⟩ _
        refine ⟨(u, ⟨u.val + w.val, U.add_mem u.2 w.2⟩), Finset.mem_univ _, ?_⟩
        ext
        · rfl
        · simp
      · rintro ⟨u, v⟩ _
        congr 2
        rw [add_assoc, add_sub_cancel]
    rw [← Fintype.sum_prod_type', hbij, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    have hq := Q.hquad a u.val w.val
    have heq : Q.f (a + u.val) + Q.f (a + u.val + w.val) =
        Q.f (a + w.val) + Q.f a + Q.B u.val w.val := by
      have hz := f2_add_self (Q.f (a + w.val))
      have hz2 := f2_add_self (Q.f a)
      rw [← hq]
      calc Q.f (a + u.val) + Q.f (a + u.val + w.val)
          = Q.f (a + u.val) + Q.f (a + u.val + w.val) +
            (Q.f (a + w.val) + Q.f (a + w.val)) + (Q.f a + Q.f a) := by
            rw [hz, hz2, add_zero, add_zero]
        _ = _ := by ring
    rw [← sgn_add, heq, sgn_add]
  have hinner : ∀ w : U, (∑ u : U, sgn (Q.B u.val w.val)) =
      if w.val ∈ Q.orth U then (Nat.card U : ℤ) else 0 := by
    intro w
    by_cases hw : w.val ∈ Q.orth U
    · simp only [hw, ↓reduceIte]
      exact sum_sgn_linear_of_zero U (fun u => Q.B u w.val) (fun u hu => by rw [Q.B_symm]; exact hw u hu)
    · simp only [hw, ↓reduceIte]
      refine sum_sgn_linear_of_ne U (fun u => Q.B u w.val) (fun u1 _ u2 _ => Q.B_add_left u1 u2 w.val) ?_
      intro hall
      exact hw (fun u hu => by rw [Q.B_symm]; exact hall u hu)
  have hfilter : (∑ w : U, sgn (Q.f (a + w.val) + Q.f a) * (if w.val ∈ Q.orth U then (Nat.card U : ℤ) else 0)) =
      (Nat.card U : ℤ) * (∑ w : ↥(U ⊓ Q.orth U), sgn (Q.f (a + w.val) + Q.f a)) := by
    rw [Finset.mul_sum]
    have h1 : (∑ w : U, sgn (Q.f (a + w.val) + Q.f a) * (if w.val ∈ Q.orth U then (Nat.card U : ℤ) else 0)) =
        ∑ w ∈ Finset.univ.filter (fun w : U => w.val ∈ Q.orth U),
          (Nat.card U : ℤ) * sgn (Q.f (a + w.val) + Q.f a) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun w _ => by split_ifs <;> ring)
    rw [h1]
    refine Finset.sum_bij (fun w hw => (⟨w.val, w.2, (Finset.mem_filter.mp hw).2⟩ : ↥(U ⊓ Q.orth U)))
      (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · intro x _ y _ h
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥(U ⊓ Q.orth U) → Vec n) h
    · rintro ⟨x, hx1, hx2⟩ _
      exact ⟨⟨x, hx1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx2⟩, rfl⟩
  have hlin_orth : ∀ u ∈ U ⊓ Q.orth U, ∀ v ∈ U ⊓ Q.orth U,
      (Q.f (a + (u + v)) + Q.f a) = (Q.f (a + u) + Q.f a) + (Q.f (a + v) + Q.f a) := by
    intro u hu v hv
    have hq := Q.hquad a u v
    have hB0 : Q.B u v = 0 := hu.2 v hv.1
    rw [hB0] at hq
    have hz := f2_add_self (Q.f a)
    have hadd : Q.f (a + (u + v)) + Q.f a = Q.f (a + u) + Q.f (a + v) := by
      have h1 : Q.f (a + u + v) + Q.f (a + u) + Q.f (a + v) + Q.f a = 0 := hq
      rw [← add_assoc]
      have hz1 := f2_add_self (Q.f (a + u))
      have hz2 := f2_add_self (Q.f (a + v))
      calc Q.f (a + u + v) + Q.f a
          = (Q.f (a + u + v) + Q.f (a + u) + Q.f (a + v) + Q.f a) + Q.f (a + u) + Q.f (a + v) := by
            calc Q.f (a + u + v) + Q.f a
                = Q.f (a + u + v) + Q.f a + (Q.f (a + u) + Q.f (a + u)) + (Q.f (a + v) + Q.f (a + v)) := by
                  rw [hz1, hz2, add_zero, add_zero]
              _ = _ := by ring
        _ = Q.f (a + u) + Q.f (a + v) := by rw [h1, zero_add]
    calc Q.f (a + (u + v)) + Q.f a
        = Q.f (a + u) + Q.f (a + v) + (Q.f a + Q.f a) := by rw [hz, add_zero, hadd]
      _ = _ := by ring
  have hsq2 : (Q.Wsum a U) ^ 2 =
      (Nat.card U : ℤ) * (∑ w : ↥(U ⊓ Q.orth U), sgn (Q.f (a + w.val) + Q.f a)) := by
    rw [hsq, Finset.sum_congr rfl (fun w _ => by rw [hinner w]), hfilter]
  constructor
  · intro hconst
    rw [hsq2, sum_sgn_linear_of_zero (U ⊓ Q.orth U) (fun w => Q.f (a + w) + Q.f a)
      (fun u hu => by rw [hconst u hu, f2_add_self])]
  · intro hnot
    rw [hsq2, sum_sgn_linear_of_ne (U ⊓ Q.orth U) (fun w => Q.f (a + w) + Q.f a) hlin_orth, mul_zero]
    intro hall
    apply hnot
    intro u hu
    have h1 := hall u hu
    have hz := f2_add_self (Q.f a)
    calc Q.f (a + u) = (Q.f (a + u) + Q.f a) + Q.f a := by rw [add_assoc, hz, add_zero]
      _ = Q.f a := by rw [h1, zero_add]

lemma Wsum_top_bal_iff :
    (Nat.card {x : Vec n // Q.f x = 0} = Nat.card {x : Vec n // Q.f x = 1}) ↔
      Q.Wsum 0 ⊤ = 0 := by
  classical
  have hW : Q.Wsum 0 ⊤ = (Nat.card {x : Vec n // Q.f x = 0} : ℤ) -
      (Nat.card {x : Vec n // Q.f x = 1} : ℤ) := by
    have h1 : Q.Wsum 0 ⊤ = ∑ x : Vec n, sgn (Q.f x) := by
      rw [Q.Wsum_eq_sum]
      refine Finset.sum_bij (fun (u : (⊤ : Submodule F2 (Vec n))) _ => u.val)
        (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => Subtype.ext h)
        (fun x _ => ⟨⟨x, trivial⟩, Finset.mem_univ _, rfl⟩)
        (fun u _ => by simp)
    rw [h1]
    have hpt : ∀ x : Vec n, sgn (Q.f x) =
        (if Q.f x = 0 then (1 : ℤ) else 0) - (if Q.f x = 1 then (1 : ℤ) else 0) := by
      intro x; rcases f2_cases (Q.f x) with h | h <;> simp [h, sgn]
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib]
    simp only [Finset.sum_boole]
    have hc0 : (Finset.univ.filter (fun x : Vec n => Q.f x = 0)).card =
        Nat.card {x : Vec n // Q.f x = 0} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hc1 : (Finset.univ.filter (fun x : Vec n => Q.f x = 1)).card =
        Nat.card {x : Vec n // Q.f x = 1} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hc0, hc1]
  rw [hW]
  omega

lemma dim_inf_orth_le (S : Submodule F2 (Vec n)) :
    Module.finrank F2 ↥(S ⊓ Q.orth S) ≤ (n - Module.finrank F2 S) + Module.finrank F2 Q.rad := by
  let A : Submodule F2 (Vec n) := (S ⊓ Q.orth S) ⊔ Q.rad
  have hRA : Q.rad ≤ A := le_sup_right
  have hS_le : S ≤ Q.orth A := by
    intro x hx u hu
    rcases Submodule.mem_sup.mp hu with ⟨a, ha, r, hr, rfl⟩
    rw [Q.B_add_right, Q.B_symm x a, ha.2 x hx, Q.B_symm x r, hr x trivial, add_zero]
  have hrA := Q.finrank_orth_add_of_rad_le A hRA
  have hSle_rk : Module.finrank F2 S ≤ Module.finrank F2 (Q.orth A) := Submodule.finrank_mono hS_le
  have hinf_le : Module.finrank F2 ↥(S ⊓ Q.orth S) ≤ Module.finrank F2 A :=
    Submodule.finrank_mono (le_sup_left : S ⊓ Q.orth S ≤ A)
  have hSn : Module.finrank F2 S ≤ n := by
    have h1 := Submodule.finrank_le S
    simpa [Vec] using h1
  omega

lemma dim_inf_orth_eq_implies (S : Submodule F2 (Vec n))
    (heq : Module.finrank F2 ↥(S ⊓ Q.orth S) = (n - Module.finrank F2 S) + Module.finrank F2 Q.rad) :
    Q.rad ≤ S ∧ Q.orth (S ⊓ Q.orth S) = S := by
  let A : Submodule F2 (Vec n) := (S ⊓ Q.orth S) ⊔ Q.rad
  have hRA : Q.rad ≤ A := le_sup_right
  have hS_le : S ≤ Q.orth A := by
    intro x hx u hu
    rcases Submodule.mem_sup.mp hu with ⟨a, ha, r, hr, rfl⟩
    rw [Q.B_add_right, Q.B_symm x a, ha.2 x hx, Q.B_symm x r, hr x trivial, add_zero]
  have hrA := Q.finrank_orth_add_of_rad_le A hRA
  have hSle_rk : Module.finrank F2 S ≤ Module.finrank F2 (Q.orth A) := Submodule.finrank_mono hS_le
  have hinf_le : Module.finrank F2 ↥(S ⊓ Q.orth S) ≤ Module.finrank F2 A :=
    Submodule.finrank_mono (le_sup_left : S ⊓ Q.orth S ≤ A)
  have hSn : Module.finrank F2 S ≤ n := by
    have h1 := Submodule.finrank_le S
    simpa [Vec] using h1
  have hA_eq_rk : Module.finrank F2 ↥(S ⊓ Q.orth S) = Module.finrank F2 A := by omega
  have hA_eq : S ⊓ Q.orth S = A := Submodule.eq_of_le_of_finrank_eq le_sup_left hA_eq_rk
  have hrad_in : Q.rad ≤ S ⊓ Q.orth S := by rw [hA_eq]; exact le_sup_right
  have hrad_S : Q.rad ≤ S := hrad_in.trans inf_le_left
  have horth_rk : Module.finrank F2 S = Module.finrank F2 (Q.orth (S ⊓ Q.orth S)) := by
    rw [hA_eq]; omega
  have hS_le_orth : S ≤ Q.orth (S ⊓ Q.orth S) := by rw [hA_eq]; exact hS_le
  exact ⟨hrad_S, (Submodule.eq_of_le_of_finrank_eq hS_le_orth horth_rk).symm⟩

end QuadForm

lemma div_pow2_antitone {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (b : ℚ) / (2 : ℚ) ^ b ≤ (a : ℚ) / (2 : ℚ) ^ a := by
  induction hab with
  | refl => exact le_rfl
  | @step k hk ih =>
    refine le_trans ?_ ih
    have hpos : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
    have hstep : ((k + 1 : ℕ) : ℚ) / (2 : ℚ) ^ (k + 1) ≤ (k : ℚ) / (2 : ℚ) ^ k := by
      rw [pow_succ, div_le_div_iff₀ (by positivity) hpos]
      have hk1 : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast (le_trans ha hk)
      push_cast
      nlinarith
    exact hstep

lemma main_proof :
    ∀ (n : ℕ),
      let F := ZMod 2
      let X := Fin n → F
      ∀ f : X → F,
        let B := fun u v : X => f (u+v)+f u+f v+f 0
        (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p=B u v) →
        let m := (n-(Nat.card {u : X // ∀ v : X, B u v=0}).log2)/2
        let bal := Nat.card {x : X // f x=0} = Nat.card {x : X // f x=1}
        let rootBias := if bal then (0 : ℚ) else 1/(2:ℚ)^m
        let size := (Nat.card X : ℚ)
        ∀ k : ℕ, 2 ≤ k →
          ∀ (a : Fin k → X) (S : Fin k → Submodule F X) (out : Fin k → F),
            (∀ x : X, ∃! j : Fin k, x-a j ∈ S j) →
            let C := (∑ j : Fin k, ((n - Module.finrank F (S j) : ℕ) : ℚ) *
              (Nat.card {x : X // x-a j ∈ S j} : ℚ)) / size
            let A := 2*(Nat.card {x : X // ∃ j, x-a j ∈ S j ∧ f x=out j} : ℚ)/size-1
            ((m:ℚ)+1)*A-rootBias ≤ C := by
  classical
  intro n F X f B hquad m bal rootBias size k hk a S out hpart C A
  let Q : QuadForm n := ⟨f, B, fun _ _ => rfl, hquad⟩
  let r := Module.finrank F2 Q.rad
  have hrad_card : Nat.card {u : X // ∀ v : X, B u v = 0} = 2 ^ r := by
    have heq : Nat.card {u : X // ∀ v : X, B u v = 0} = Nat.card Q.rad :=
      Nat.card_congr
        { toFun := fun u => ⟨u.1, (Q.mem_rad_iff u.1).mpr u.2⟩
          invFun := fun u => ⟨u.1, (Q.mem_rad_iff u.1).mp u.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [heq, card_sub_eq_pow]
  have hlog : (Nat.card {u : X // ∀ v : X, B u v = 0}).log2 = r := by
    rw [hrad_card, Nat.log2_two_pow]
  have heven : Even (n - r) := Q.finrank_sub_rad_even
  have hm_eq : 2 * m = n - r := by
    dsimp only [m]
    rw [hlog]
    rcases heven with ⟨q, hq⟩
    omega
  have hr_le_n : r ≤ n := by
    have h1 := Submodule.finrank_le Q.rad
    simpa [Vec] using h1
  have hSn_all : ∀ j : Fin k, Module.finrank F2 (S j) ≤ n := by
    intro j
    have h1 := Submodule.finrank_le (S j)
    dsimp only [F, X] at h1
    simpa [Vec] using h1
  have hsize : size = (2 : ℚ) ^ n := by
    dsimp only [size, X]
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card 2]
    push_cast; rfl
  have hd_pos : ∀ j : Fin k, 1 ≤ n - Module.finrank F2 (S j) := by
    intro j
    have hSn := hSn_all j
    by_contra h0
    have hfull : Module.finrank F2 (S j) = n := by omega
    have htop : S j = ⊤ := Submodule.eq_top_of_finrank_eq (by
      have hn : Module.finrank F X = n := by dsimp only [F, X]; simp
      rw [hn]; exact hfull)
    let j' : Fin k := if j.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hjne : j' ≠ j := by
      intro h
      dsimp only [j'] at h
      split_ifs at h with h0'
      · have hv := congrArg Fin.val h; dsimp only at hv; omega
      · have hv := congrArg Fin.val h; dsimp only at hv; omega
    have h1 : a j' - a j ∈ S j := by rw [htop]; trivial
    have h2 : a j' - a j' ∈ S j' := by rw [sub_self]; exact (S j').zero_mem
    have huniq := (hpart (a j')).unique h1 h2
    exact hjne huniq.symm
  have hC_eq : C = ∑ j : Fin k, ((n - Module.finrank F2 (S j) : ℕ) : ℚ) /
      (2 : ℚ) ^ (n - Module.finrank F2 (S j)) := by
    dsimp only [C]
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hSn := hSn_all j
    rw [card_coset_eq_sub, card_sub_eq_pow, hsize, ← div_eq_mul_inv]
    push_cast
    have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ Module.finrank F2 (S j) *
        (2 : ℚ) ^ (n - Module.finrank F2 (S j)) := by
      rw [← pow_add, Nat.add_sub_of_le hSn]
    rw [hpow]
    have hpos1 : (2 : ℚ) ^ Module.finrank F2 (S j) ≠ 0 := by positivity
    have hpos2 : (2 : ℚ) ^ (n - Module.finrank F2 (S j)) ≠ 0 := by positivity
    dsimp only [F]
    field_simp
    rfl
  have hA_le : A ≤ ∑ j : Fin k, (|(Q.Wsum (a j) (S j) : ℚ)|) / (2 : ℚ) ^ n := by
    have hhit : (2 * (Nat.card {x : X // ∃ j, x - a j ∈ S j ∧ f x = out j} : ℤ) - (Nat.card X : ℤ)) =
        ∑ j : Fin k, sgn (out j) * Q.Wsum (a j) (S j) := by
      have h1 : (2 * (Nat.card {x : X // ∃ j, x - a j ∈ S j ∧ f x = out j} : ℤ) - (Nat.card X : ℤ)) =
          ∑ x : X, if ∃ j, x - a j ∈ S j ∧ f x = out j then (1 : ℤ) else -1 := by
        have hpt : ∀ x : X, (if ∃ j, x - a j ∈ S j ∧ f x = out j then (1 : ℤ) else -1) =
            2 * (if ∃ j, x - a j ∈ S j ∧ f x = out j then (1 : ℤ) else 0) - 1 := by
          intro x; split_ifs <;> omega
        rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_boole, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [h1]
      let cell : Fin k → Finset X := fun j => Finset.univ.filter (fun x : X => x - a j ∈ S j)
      have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)) cell := by
        intro j1 _ j2 _ hne
        exact Finset.disjoint_filter.mpr (fun x _ h1 h2 => hne ((hpart x).unique h1 h2))
      have hunion : (Finset.univ : Finset (Fin k)).biUnion cell = Finset.univ := by
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, iff_true, cell]
        rcases hpart x with ⟨j, hj, _⟩
        exact ⟨j, hj⟩
      rw [← hunion, Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hcell_eq : (∑ x ∈ cell j, if ∃ j', x - a j' ∈ S j' ∧ f x = out j' then (1 : ℤ) else -1) =
          ∑ x ∈ cell j, sgn (out j) * sgn (f x) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        have hxS : x - a j ∈ S j := (Finset.mem_filter.mp hx).2
        have hiff : (∃ j', x - a j' ∈ S j' ∧ f x = out j') ↔ f x = out j := by
          constructor
          · rintro ⟨j', hj', hf⟩
            have heq : j' = j := (hpart x).unique hj' hxS
            rwa [← heq]
          · intro hf; exact ⟨j, hxS, hf⟩
        by_cases hf : f x = out j
        · split_ifs with h
          · rw [hf, sgn_mul_self]
          · exact (h (hiff.mpr hf)).elim
        · split_ifs with h
          · exact (hf (hiff.mp h)).elim
          · exact (sgn_mul_ne (out j) (f x) (Ne.symm hf)).symm
      rw [hcell_eq, ← Finset.mul_sum]
      congr 1
      rw [Q.Wsum_eq_sum]
      refine Finset.sum_bij (fun x hx => (⟨x - a j, (Finset.mem_filter.mp hx).2⟩ : S j))
        (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro x1 _ x2 _ h
        have := congrArg (Subtype.val : S j → Vec n) h
        exact sub_left_inj.mp this
      · rintro ⟨u, hu⟩ _
        refine ⟨a j + u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu]⟩, ?_⟩
        apply Subtype.ext; simp
      · intro x _
        simp [Q, add_sub_cancel]
    have hhit_q : A = (∑ j : Fin k, (sgn (out j) * Q.Wsum (a j) (S j) : ℚ)) / (2 : ℚ) ^ n := by
      have hcast : ((2 * (Nat.card {x : X // ∃ j, x - a j ∈ S j ∧ f x = out j} : ℤ) - (Nat.card X : ℤ) : ℤ) : ℚ) =
          ((∑ j : Fin k, sgn (out j) * Q.Wsum (a j) (S j) : ℤ) : ℚ) := by exact_mod_cast hhit
      push_cast at hcast
      dsimp only [A]
      rw [hsize]
      have hpos : (2 : ℚ) ^ n ≠ 0 := by positivity
      have hnat : (Nat.card X : ℚ) = (2 : ℚ) ^ n := hsize
      rw [hnat] at hcast
      field_simp at *
      linarith
    rw [hhit_q, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [← div_eq_mul_inv]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rcases f2_cases (out j) with h1 | h1
    · rw [h1]; change (1 : ℚ) * _ ≤ _; rw [one_mul]; exact le_abs_self _
    · rw [h1]; change (-1 : ℚ) * _ ≤ _; rw [neg_one_mul]; exact neg_le_abs _
  let isExc : Fin k → Prop := fun j =>
    (Q.Wsum (a j) (S j)) ^ 2 = ((2 : ℤ) ^ (n - m)) ^ 2
  have hcell_dich : ∀ j : Fin k,
      isExc j ∨ |(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n ≤ 1 / (2 : ℚ) ^ (m + 1) := by
    intro j
    by_cases hconst : ∀ w ∈ S j ⊓ Q.orth (S j), Q.f (a j + w) = Q.f (a j)
    · have hsq := (Q.Wsum_sq_cases (a j) (S j)).1 hconst
      rw [card_sub_eq_pow, card_sub_eq_pow] at hsq
      let d := n - Module.finrank F2 (S j)
      let s0 := Module.finrank F2 ↥(S j ⊓ Q.orth (S j))
      have hSn := hSn_all j
      have hdim_le : s0 ≤ d + r := Q.dim_inf_orth_le (S j)
      have hdim_even : Even (Module.finrank F2 (S j) - s0) :=
        Q.finrank_sub_rad_even_aux (Module.finrank F2 (S j)) (S j) rfl
      have hs0_le : s0 ≤ Module.finrank F2 (S j) := Submodule.finrank_mono inf_le_left
      by_cases heq : s0 = d + r
      · left
        dsimp only [isExc]
        rw [hsq]
        have hexp : Module.finrank F2 (S j) + s0 = 2 * (n - m) := by omega
        push_cast
        rw [← pow_add, hexp, pow_mul', sq]
      · right
        have hlt2 : Module.finrank F2 (S j) + s0 + 2 ≤ 2 * (n - m) := by
          rcases hdim_even with ⟨q, hq⟩
          omega
        have hsq_le : ((Q.Wsum (a j) (S j) : ℚ)) ^ 2 * (2 : ℚ) ^ (2 * (m + 1)) ≤ ((2 : ℚ) ^ n) ^ 2 := by
          have h1 : ((Q.Wsum (a j) (S j) : ℚ)) ^ 2 = (2 : ℚ) ^ (Module.finrank F2 (S j) + s0) := by
            have hc : ((Q.Wsum (a j) (S j) ^ 2 : ℤ) : ℚ) =
                (((2 ^ Module.finrank F2 (S j) : ℕ) : ℤ) * ((2 ^ s0 : ℕ) : ℤ) : ℚ) := by
              exact_mod_cast hsq
            push_cast at hc
            rw [hc, pow_add]
          rw [h1, ← pow_add, ← pow_mul]
          have hexp : Module.finrank F2 (S j) + s0 + 2 * (m + 1) ≤ n * 2 := by omega
          exact pow_le_pow_right₀ (by norm_num) hexp
        have habs_sq : (|(Q.Wsum (a j) (S j) : ℚ)| * (2 : ℚ) ^ (m + 1)) ^ 2 ≤ ((2 : ℚ) ^ n) ^ 2 := by
          rw [mul_pow, sq_abs, ← pow_mul, mul_comm (m + 1) 2]
          exact hsq_le
        have hle : |(Q.Wsum (a j) (S j) : ℚ)| * (2 : ℚ) ^ (m + 1) ≤ (2 : ℚ) ^ n :=
          le_of_sq_le_sq habs_sq (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        exact hle
    · right
      have hsq := (Q.Wsum_sq_cases (a j) (S j)).2 hconst
      have h0 : Q.Wsum (a j) (S j) = 0 := sq_eq_zero_iff.mp hsq
      rw [h0]; simp
  have hord_charge : ∀ j : Fin k,
      |(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n ≤ 1 / (2 : ℚ) ^ (m + 1) →
      ((m : ℚ) + 1) * (|(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n) ≤
        ((n - Module.finrank F2 (S j) : ℕ) : ℚ) / (2 : ℚ) ^ (n - Module.finrank F2 (S j)) := by
    intro j hle
    let d := n - Module.finrank F2 (S j)
    have hd1 : 1 ≤ d := hd_pos j
    have hSn := hSn_all j
    by_cases hdm : d ≤ m + 1
    · calc ((m : ℚ) + 1) * (|(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n)
          ≤ ((m : ℚ) + 1) * (1 / (2 : ℚ) ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = ((m + 1 : ℕ) : ℚ) / (2 : ℚ) ^ (m + 1) := by push_cast; ring
        _ ≤ (d : ℚ) / (2 : ℚ) ^ d := div_pow2_antitone hd1 hdm
    · have htriv : |(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n ≤ 1 / (2 : ℚ) ^ d := by
        have hWle : |(Q.Wsum (a j) (S j) : ℚ)| ≤ (2 : ℚ) ^ Module.finrank F2 (S j) := by
          have h1 : |Q.Wsum (a j) (S j)| ≤ (Nat.card (S j) : ℤ) := by
            rw [Q.Wsum_eq_sum]
            calc |∑ u : S j, sgn (Q.f (a j + u.val))|
                ≤ ∑ u : S j, |sgn (Q.f (a j + u.val))| := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ _u : S j, (1 : ℤ) := Finset.sum_congr rfl (fun u _ => abs_sgn _)
              _ = (Nat.card (S j) : ℤ) := by simp [Nat.card_eq_fintype_card]
          rw [card_sub_eq_pow] at h1
          exact_mod_cast h1
        have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ Module.finrank F2 (S j) * (2 : ℚ) ^ d := by
          rw [← pow_add, Nat.add_sub_of_le hSn]
        rw [hpow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        nlinarith [show (0 : ℚ) < (2 : ℚ) ^ d by positivity]
      have hmd : ((m : ℚ) + 1) ≤ (d : ℚ) := by
        have : m + 1 ≤ d := by omega
        exact_mod_cast this
      calc ((m : ℚ) + 1) * (|(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n)
          ≤ ((m : ℚ) + 1) * (1 / (2 : ℚ) ^ d) := mul_le_mul_of_nonneg_left htriv (by positivity)
        _ ≤ (d : ℚ) * (1 / (2 : ℚ) ^ d) := mul_le_mul_of_nonneg_right hmd (by positivity)
        _ = (d : ℚ) / (2 : ℚ) ^ d := by ring
  have hexc_props : ∀ j : Fin k, isExc j →
      ¬ bal ∧
      Q.rad ≤ S j ⊓ Q.orth (S j) ∧
      Q.orth (S j ⊓ Q.orth (S j)) = S j ∧
      (∀ w ∈ S j ⊓ Q.orth (S j), Q.f (a j + w) = Q.f (a j)) ∧
      n - Module.finrank F2 (S j) ≤ m ∧
      |(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n = 1 / (2 : ℚ) ^ m := by
    intro j hexc
    dsimp only [isExc] at hexc
    have hpos_sq : ((2 : ℤ) ^ (n - m)) ^ 2 ≠ 0 := by positivity
    have hconst : ∀ w ∈ S j ⊓ Q.orth (S j), Q.f (a j + w) = Q.f (a j) := by
      by_contra hnot
      have h0 := (Q.Wsum_sq_cases (a j) (S j)).2 hnot
      exact hpos_sq (hexc.symm.trans h0)
    have hsq := (Q.Wsum_sq_cases (a j) (S j)).1 hconst
    rw [hexc, card_sub_eq_pow, card_sub_eq_pow] at hsq
    have hSn := hSn_all j
    have hpow_eq : (2 : ℕ) ^ (2 * (n - m)) = 2 ^ (Module.finrank F2 (S j) + Module.finrank F2 ↥(S j ⊓ Q.orth (S j))) := by
      have h1 : (((2 : ℕ) ^ (2 * (n - m)) : ℕ) : ℤ) =
          (((2 : ℕ) ^ (Module.finrank F2 (S j) + Module.finrank F2 ↥(S j ⊓ Q.orth (S j))) : ℕ) : ℤ) := by
        push_cast at hsq ⊢
        rw [pow_add, mul_comm 2 (n - m), pow_mul]
        exact hsq
      exact_mod_cast h1
    have hexp : 2 * (n - m) = Module.finrank F2 (S j) + Module.finrank F2 ↥(S j ⊓ Q.orth (S j)) :=
      Nat.pow_right_injective (by decide : 1 < 2) hpow_eq
    have hdim_eq : Module.finrank F2 ↥(S j ⊓ Q.orth (S j)) = (n - Module.finrank F2 (S j)) + r := by omega
    rcases Q.dim_inf_orth_eq_implies (S j) hdim_eq with ⟨hradS, horthS⟩
    have hrad_inf : Q.rad ≤ S j ⊓ Q.orth (S j) := le_inf hradS (Q.rad_le_orth (S j))
    have hnotbal : ¬ bal := by
      intro hbal
      have hW0 : Q.Wsum 0 ⊤ = 0 := (Q.Wsum_top_bal_iff).mp hbal
      have hrad_const : ∀ w ∈ (⊤ : Submodule F2 (Vec n)) ⊓ Q.orth ⊤, Q.f (0 + w) = Q.f 0 := by
        intro w hw
        have hwR : w ∈ Q.rad := hw.2
        have h1 := hconst w (hrad_inf hwR)
        have hB0 : Q.B (a j) w = 0 := (Q.B_symm (a j) w) ▸ hwR (a j) trivial
        rw [Q.hB] at hB0
        rw [zero_add]
        have hz1 := f2_add_self (Q.f (a j))
        have hz2 := f2_add_self (Q.f 0)
        calc Q.f w = (Q.f (a j + w) + Q.f (a j) + Q.f w + Q.f 0) + Q.f 0 := by
              rw [h1]
              calc Q.f w = Q.f w + (Q.f (a j) + Q.f (a j)) + (Q.f 0 + Q.f 0) := by
                    rw [hz1, hz2, add_zero, add_zero]
                _ = _ := by ring
          _ = Q.f 0 := by rw [hB0, zero_add]
      have htop_sq := (Q.Wsum_sq_cases 0 ⊤).1 hrad_const
      rw [hW0, zero_pow (by decide : 2 ≠ 0)] at htop_sq
      have hpos1 : (0 : ℤ) < Nat.card (⊤ : Submodule F2 (Vec n)) := by
        rw [card_sub_eq_pow]; positivity
      have hpos2 : (0 : ℤ) < Nat.card ↥((⊤ : Submodule F2 (Vec n)) ⊓ Q.orth ⊤) := by
        rw [card_sub_eq_pow]; positivity
      nlinarith
    have hdm : n - Module.finrank F2 (S j) ≤ m := by
      have hle : Module.finrank F2 ↥(S j ⊓ Q.orth (S j)) ≤ Module.finrank F2 (S j) :=
        Submodule.finrank_mono inf_le_left
      omega
    have habs : |(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n = 1 / (2 : ℚ) ^ m := by
      have hsq_q : (|(Q.Wsum (a j) (S j) : ℚ)|) ^ 2 = ((2 : ℚ) ^ (n - m)) ^ 2 := by
        rw [sq_abs]
        exact_mod_cast hexc
      have habs_eq : |(Q.Wsum (a j) (S j) : ℚ)| = (2 : ℚ) ^ (n - m) :=
        le_antisymm (le_of_sq_le_sq hsq_q.le (by positivity))
          (le_of_sq_le_sq hsq_q.symm.le (abs_nonneg _))
      rw [habs_eq]
      have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - m) * (2 : ℚ) ^ m := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      rw [hpow]
      have h1 : (2 : ℚ) ^ (n - m) ≠ 0 := by positivity
      have h2 : (2 : ℚ) ^ m ≠ 0 := by positivity
      field_simp
    exact ⟨hnotbal, hrad_inf, horthS, hconst, hdm, habs⟩
  have hexc_uniq : ∀ j1 j2 : Fin k, isExc j1 → isExc j2 → j1 = j2 := by
    intro j1 j2 h1 h2
    rcases hexc_props j1 h1 with ⟨_, hR1, hO1, hC1, _, _⟩
    rcases hexc_props j2 h2 with ⟨_, hR2, hO2, hC2, _, _⟩
    have hmem : a j1 + a j2 ∈ Q.orth ((S j1 ⊓ Q.orth (S j1)) ⊓ (S j2 ⊓ Q.orth (S j2))) := by
      intro w hw
      have hw1 := hC1 w hw.1
      have hw2 := hC2 w hw.2
      have hB1 : Q.B (a j1) w = Q.f w + Q.f 0 := by
        rw [Q.hB, hw1, f2_add_self, zero_add]
      have hB2 : Q.B (a j2) w = Q.f w + Q.f 0 := by
        rw [Q.hB, hw2, f2_add_self, zero_add]
      rw [Q.B_add_left, hB1, hB2, f2_add_self]
    rw [Q.orth_inf_eq_sup_orth _ _ hR1 hR2, hO1, hO2] at hmem
    rcases Submodule.mem_sup.mp hmem with ⟨s1, hs1, s2, hs2, hs12⟩
    let x := a j1 + s1
    have hx1 : x - a j1 ∈ S j1 := by
      simpa [x] using hs1
    have hx2 : x - a j2 ∈ S j2 := by
      have heq : x - a j2 = s2 := by
        rw [f2_sub_eq_add]
        funext i
        have hi := congrFun hs12 i
        have hz1 := f2_add_self (s1 i)
        rw [Pi.add_apply, Pi.add_apply] at hi
        dsimp only [x, Pi.add_apply]
        calc a j1 i + s1 i + a j2 i
            = (a j1 i + a j2 i) + s1 i := by ring
          _ = (s1 i + s2 i) + s1 i := by rw [← hi]
          _ = s2 i + (s1 i + s1 i) := by ring
          _ = s2 i := by rw [hz1, add_zero]
      rw [heq]; exact hs2
    exact (hpart x).unique hx1 hx2
  by_cases hex : ∃ j0 : Fin k, isExc j0
  · rcases hex with ⟨j0, hj0⟩
    rcases hexc_props j0 hj0 with ⟨hnotbal, _, _, _, hd0m, habs0⟩
    have hrb : rootBias = 1 / (2 : ℚ) ^ m := by dsimp only [rootBias]; simp [hnotbal]
    have hsplit_lhs : ((m : ℚ) + 1) * (∑ j : Fin k, |(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n) - rootBias =
        (((m : ℚ) + 1) * (|(Q.Wsum (a j0) (S j0) : ℚ)| / (2 : ℚ) ^ n) - rootBias) +
        ∑ j ∈ Finset.univ.erase j0, ((m : ℚ) + 1) * (|(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n) := by
      rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
      ring
    have hsplit_rhs : C =
        ((n - Module.finrank F2 (S j0) : ℕ) : ℚ) / (2 : ℚ) ^ (n - Module.finrank F2 (S j0)) +
        ∑ j ∈ Finset.univ.erase j0,
          ((n - Module.finrank F2 (S j) : ℕ) : ℚ) / (2 : ℚ) ^ (n - Module.finrank F2 (S j)) := by
      rw [hC_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
    have hj0_le : ((m : ℚ) + 1) * (|(Q.Wsum (a j0) (S j0) : ℚ)| / (2 : ℚ) ^ n) - rootBias ≤
        ((n - Module.finrank F2 (S j0) : ℕ) : ℚ) / (2 : ℚ) ^ (n - Module.finrank F2 (S j0)) := by
      rw [habs0, hrb]
      have heq : ((m : ℚ) + 1) * (1 / (2 : ℚ) ^ m) - 1 / (2 : ℚ) ^ m = (m : ℚ) / (2 : ℚ) ^ m := by ring
      rw [heq]
      exact div_pow2_antitone (hd_pos j0) hd0m
    have hrest_le : (∑ j ∈ Finset.univ.erase j0, ((m : ℚ) + 1) * (|(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n)) ≤
        ∑ j ∈ Finset.univ.erase j0,
          ((n - Module.finrank F2 (S j) : ℕ) : ℚ) / (2 : ℚ) ^ (n - Module.finrank F2 (S j)) := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hne : j ≠ j0 := (Finset.mem_erase.mp hj).1
      have hnot : ¬ isExc j := fun h => hne (hexc_uniq j j0 h hj0)
      exact hord_charge j ((hcell_dich j).resolve_left hnot)
    have h1 : ((m : ℚ) + 1) * A - rootBias ≤
        ((m : ℚ) + 1) * (∑ j : Fin k, |(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n) - rootBias := by
      linarith [mul_le_mul_of_nonneg_left hA_le (by positivity : (0 : ℚ) ≤ (m : ℚ) + 1)]
    rw [hsplit_lhs] at h1
    rw [hsplit_rhs]
    linarith
  · push Not at hex
    have hrb_nn : (0 : ℚ) ≤ rootBias := by
      dsimp only [rootBias]; split_ifs <;> positivity
    have hsum_le : ((m : ℚ) + 1) * (∑ j : Fin k, |(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n) ≤ C := by
      rw [Finset.mul_sum, hC_eq]
      exact Finset.sum_le_sum (fun j _ => hord_charge j ((hcell_dich j).resolve_left (hex j)))
    have h1 : ((m : ℚ) + 1) * A ≤
        ((m : ℚ) + 1) * (∑ j : Fin k, |(Q.Wsum (a j) (S j) : ℚ)| / (2 : ℚ) ^ n) :=
      mul_le_mul_of_nonneg_left hA_le (by positivity)
    linarith

end PEqualNP.Outside.L_pcx_455_aux

theorem PEqualNP.Outside.L_pcx_455 :
∀ (n : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  ∀ f : X → F,
    let B := fun u v : X => f (u+v)+f u+f v+f 0
    (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p=B u v) →
    let m := (n-(Nat.card {u : X // ∀ v : X, B u v=0}).log2)/2
    let bal := Nat.card {x : X // f x=0} = Nat.card {x : X // f x=1}
    let rootBias := if bal then (0 : ℚ) else 1/(2:ℚ)^m
    let size := (Nat.card X : ℚ)
    ∀ k : ℕ, 2 ≤ k →
      ∀ (a : Fin k → X) (S : Fin k → Submodule F X) (out : Fin k → F),
        (∀ x : X, ∃! j : Fin k, x-a j ∈ S j) →
        let C := (∑ j : Fin k, ((n - Module.finrank F (S j) : ℕ) : ℚ) *
          (Nat.card {x : X // x-a j ∈ S j} : ℚ)) / size
        let A := 2*(Nat.card {x : X // ∃ j, x-a j ∈ S j ∧ f x=out j} : ℚ)/size-1
        ((m:ℚ)+1)*A-rootBias ≤ C := by
  exact PEqualNP.Outside.L_pcx_455_aux.main_proof

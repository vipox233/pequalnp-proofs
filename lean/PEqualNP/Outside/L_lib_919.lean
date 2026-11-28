import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_919

open PEqualNP.CircuitLowerBounds

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  match a with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

private lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

private lemma b2z_inj : Function.Injective b2z := by
  intro a b h
  cases a <;> cases b <;> simp_all [b2z]

private lemma b2z_unary_affine (f : Bool → Bool) :
    ∃ c0 c1 : ZMod 2, ∀ u : Bool, b2z (f u) = c0 + c1 * b2z u := by
  refine ⟨b2z (f false), b2z (f true) + b2z (f false), ?_⟩
  intro u
  cases h0 : f false <;> cases h1 : f true <;> cases u <;> simp only [h0, h1, b2z] <;> decide

private lemma b2z_mod2_pair (u v : Bool) :
    b2z (GateOp.mod 2 |>.eval [u, v]) = 1 + b2z u + b2z v := by
  cases u <;> cases v <;> decide

private def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresOf]
  | append_singleton gs g ih =>
    simp only [wiresOf, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton] at ih ⊢
    omega

private lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_last {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

private lemma getD_of_ge_length {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma wiresOf_append_prefix (gs₁ gs₂ : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs₁.length) :
    (wiresOf (gs₁ ++ gs₂) x).getD w false = (wiresOf gs₁ x).getD w false := by
  induction gs₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton gs₂ g ih =>
    rw [← List.append_assoc]
    have hstep : wiresOf ((gs₁ ++ gs₂) ++ [g]) x =
        wiresOf (gs₁ ++ gs₂) x ++
          [g.op.eval (g.inputs.map fun i => (wiresOf (gs₁ ++ gs₂) x).getD i false)] := by
      simp [wiresOf, List.foldl_append]
    rw [hstep, getD_append_left _ _ _ _ (by rw [wiresOf_length, List.length_append]; omega)]
    exact ih

private noncomputable def isPaid (h : Gate) : Bool :=
  @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)

private def legalGates (n : ℕ) (gs : List Gate) : Prop :=
  (∀ i : Fin gs.length, ∀ w ∈ (gs.get i).inputs, w < n + i.val) ∧
  (∀ h ∈ gs, h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))

private lemma wires_affine_paid (n : ℕ) (gs : List Gate)
    (hallow : ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))) :
    ∃ (q : ℕ) (nl : Fin q → (Fin n → Bool) → ZMod 2),
      q ≤ gs.countP isPaid ∧
      ∀ w : ℕ, ∃ (A : Fin n → ZMod 2) (D : Fin q → ZMod 2) (a : ZMod 2),
        ∀ x : Fin n → Bool,
          b2z ((wiresOf gs (List.ofFn x)).getD w false) =
            a + (∑ i : Fin n, A i * b2z (x i)) + ∑ r : Fin q, D r * nl r x := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨0, Fin.elim0, by simp, fun w => ?_⟩
    by_cases hw : w < n
    · refine ⟨fun i => if i.val = w then 1 else 0, Fin.elim0, 0, fun x => ?_⟩
      simp only [wiresOf, List.foldl_nil, zero_add, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      rw [Finset.sum_eq_single (⟨w, hw⟩ : Fin n)]
      · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw]
      · intro i _ hne
        have : i.val ≠ w := fun h => hne (Fin.ext h)
        simp [this]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · refine ⟨fun _ => 0, Fin.elim0, 0, fun x => ?_⟩
      simp only [wiresOf, List.foldl_nil, zero_mul, Finset.sum_const_zero, add_zero]
      rw [getD_of_ge_length _ _ _ (by simp; omega)]
      rfl
  | append_singleton gs g ih =>
    have hallow_gs : ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)) :=
      fun h hh => hallow h (List.mem_append_left _ hh)
    have hallow_g := hallow g (List.mem_append_right _ List.mem_cons_self)
    rcases ih hallow_gs with ⟨q, nl, hq_le, ihw⟩
    set curLen := n + gs.length
    have hw_len : ∀ x : Fin n → Bool, (wiresOf gs (List.ofFn x)).length = curLen := fun x => by
      rw [wiresOf_length, List.length_ofFn]
    have hw_step : ∀ x : Fin n → Bool, wiresOf (gs ++ [g]) (List.ofFn x) =
        wiresOf gs (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresOf gs (List.ofFn x)).getD i false)] := by
      intro x; simp [wiresOf, List.foldl_append]
    have hw_old : ∀ w < curLen, ∀ x : Fin n → Bool,
        (wiresOf (gs ++ [g]) (List.ofFn x)).getD w false =
          (wiresOf gs (List.ofFn x)).getD w false := by
      intro w hlt x
      rw [hw_step x, getD_append_left _ _ _ _ (by rw [hw_len x]; omega)]
    have hw_new : ∀ x : Fin n → Bool,
        (wiresOf (gs ++ [g]) (List.ofFn x)).getD curLen false =
          g.op.eval (g.inputs.map fun i => (wiresOf gs (List.ofFn x)).getD i false) := by
      intro x
      rw [hw_step x, ← hw_len x, getD_append_last]
    have hw_hi : ∀ w, curLen < w → ∀ x : Fin n → Bool,
        (wiresOf (gs ++ [g]) (List.ofFn x)).getD w false = false := by
      intro w hgt x
      rw [getD_of_ge_length _ _ _ (by rw [wiresOf_length, List.length_ofFn, List.length_append, List.length_singleton]; omega)]
    have hcnt : (gs ++ [g]).countP isPaid = gs.countP isPaid + (isPaid g).toNat := by
      rw [List.countP_append, List.countP_cons, List.countP_nil]
      cases isPaid g <;> simp
    cases hp : isPaid g
    · refine ⟨q, nl, by rw [hcnt, hp]; simp; exact hq_le, fun w => ?_⟩
      by_cases hlt : w < curLen
      · rcases ihw w with ⟨A, D, a, hrepr⟩
        exact ⟨A, D, a, fun x => by rw [hw_old w hlt x, hrepr x]⟩
      · by_cases hgt : curLen < w
        · exact ⟨fun _ => 0, fun _ => 0, 0, fun x => by rw [hw_hi w hgt x]; simp [b2z]⟩
        · have heq : w = curLen := by omega
          subst heq
          rcases hgin : g.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
          · refine ⟨fun _ => 0, fun _ => 0, b2z (g.op.eval []), fun x => ?_⟩
            rw [hw_new x, hgin]; simp
          · rcases ihw u with ⟨Au, Du, au, hu⟩
            rcases b2z_unary_affine (fun b => g.op.eval [b]) with ⟨c0, c1, haff⟩
            refine ⟨fun i => c1 * Au i, fun r => c1 * Du r, c0 + c1 * au, fun x => ?_⟩
            rw [hw_new x, hgin, List.map_cons, List.map_nil, haff, hu x]
            simp only [mul_assoc, ← Finset.mul_sum]
            ring
          · have hmod2 : g.op = .mod 2 := by
              have hnotpaid : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) := by
                intro h
                have : isPaid g = true := by simp [isPaid, h]
                rw [hp] at this; cases this
              have hlen2 : g.inputs.length = 2 := by simp [hgin]
              rcases hallow_g.2 with h1 | h2 | h3 | ⟨_, h4⟩
              · exact (hnotpaid ⟨Or.inl h1, hlen2⟩).elim
              · exact (hnotpaid ⟨Or.inr h2, hlen2⟩).elim
              · exact h3
              · omega
            rcases ihw u with ⟨Au, Du, au, hu⟩
            rcases ihw v with ⟨Av, Dv, av, hv⟩
            refine ⟨fun i => Au i + Av i, fun r => Du r + Dv r, 1 + au + av, fun x => ?_⟩
            rw [hw_new x, hgin, hmod2, List.map_cons, List.map_cons, List.map_nil, b2z_mod2_pair,
              hu x, hv x]
            simp only [add_mul, Finset.sum_add_distrib]
            ring
          · have := hallow_g.1; rw [hgin] at this; simp at this
    · let nl' : Fin (q + 1) → (Fin n → Bool) → ZMod 2 := fun r x =>
        if hr : r.val < q then nl ⟨r.val, hr⟩ x else b2z ((wiresOf (gs ++ [g]) (List.ofFn x)).getD curLen false)
      refine ⟨q + 1, nl', by rw [hcnt, hp]; simp; exact hq_le, fun w => ?_⟩
      by_cases hlt : w < curLen
      · rcases ihw w with ⟨A, D, a, hrepr⟩
        let D' : Fin (q + 1) → ZMod 2 := fun r => if hr : r.val < q then D ⟨r.val, hr⟩ else 0
        refine ⟨A, D', a, fun x => ?_⟩
        rw [hw_old w hlt x, hrepr x]
        congr 1
        rw [Fin.sum_univ_castSucc]
        have hlast : D' (Fin.last q) = 0 := by simp [D']
        rw [hlast, zero_mul, add_zero]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp [D', nl', r.isLt]
      · by_cases hgt : curLen < w
        · exact ⟨fun _ => 0, fun _ => 0, 0, fun x => by rw [hw_hi w hgt x]; simp [b2z]⟩
        · have heq : w = curLen := by omega
          subst heq
          refine ⟨fun _ => 0, fun r => if r = Fin.last q then 1 else 0, 0, fun x => ?_⟩
          simp only [zero_mul, Finset.sum_const_zero, zero_add]
          rw [Finset.sum_eq_single (Fin.last q)]
          · simp [nl']
          · intro r _ hne; simp [hne]
          · intro h; exact (h (Finset.mem_univ _)).elim

private def linDot {K : Type*} [Field K] {m : ℕ} (v : Fin m → K) : (Fin m → K) →ₗ[K] K where
  toFun x := ∑ i : Fin m, v i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => by ring

private def matT {K : Type*} [Field K] {c m : ℕ} (M : Fin c → Fin m → K) :
    (Fin c → K) →ₗ[K] (Fin m → K) where
  toFun u i := ∑ j : Fin c, u j * M j i
  map_add' u v := by funext i; simp [add_mul, Finset.sum_add_distrib]
  map_smul' s u := by funext i; simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma card_dual_ann_clean {K : Type*} [Field K] {m : ℕ}
    (V : Submodule K (Fin m → K)) :
    Module.finrank K (LinearMap.ker (LinearMap.pi fun u : V => linDot u.1)) =
      m - Module.finrank K V := by
  classical
  have : Module.Free K V := Module.Free.of_divisionRing K V
  let bV := Module.finBasis K V
  let d := Module.finrank K V
  let Ψ : (Fin m → K) →ₗ[K] (V → K) := LinearMap.pi fun u : V => linDot u.1
  let Φ : (Fin m → K) →ₗ[K] (Fin d → K) :=
    { toFun := fun x t => ∑ i : Fin m, (bV t).1 i * x i
      map_add' := fun x y => by funext t; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        funext t
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => by ring }
  have hker_eq : LinearMap.ker Ψ = LinearMap.ker Φ := by
    ext x
    simp only [LinearMap.mem_ker, Ψ, Φ, linDot]
    constructor
    · intro h; funext t; exact congr_fun h (bV t)
    · intro h; funext u
      have huval : u.1 = ∑ t : Fin d, (bV.repr u t) • (bV t).1 := by
        have := congrArg Subtype.val (bV.sum_repr u).symm
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using this
      change ∑ i : Fin m, u.1 i * x i = 0
      rw [huval]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro t _
      have hmul : (∑ i : Fin m, (bV.repr u t) * (bV t).1 i * x i) =
          (bV.repr u t) * ∑ i : Fin m, (bV t).1 i * x i := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      have ht : ∑ i : Fin m, (bV t).1 i * x i = 0 := congr_fun h t
      rw [hmul, ht, mul_zero]
  have hΦ_surj : Function.Surjective Φ := by
    by_contra hnot
    let R := LinearMap.range Φ
    have hR_ne : R ≠ ⊤ := fun htop => hnot (LinearMap.range_eq_top.mp htop)
    have hR_dim : Module.finrank K R < d := by
      have := Submodule.finrank_lt hR_ne
      simpa [Module.finrank_pi] using this
    have : Module.Free K R := Module.Free.of_divisionRing K R
    let bR := Module.finBasis K R
    let r := Module.finrank K R
    let killR : (Fin d → K) →ₗ[K] (Fin r → K) :=
      { toFun := fun α s => ∑ t : Fin d, α t * (bR s).1 t
        map_add' := fun a b => by funext s; simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun c a => by funext s; simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
    have hker_pos : 0 < Module.finrank K (LinearMap.ker killR) := by
      have h1 := LinearMap.finrank_range_add_finrank_ker killR
      have h2 : Module.finrank K (LinearMap.range killR) ≤ r := by
        have := Submodule.finrank_le (LinearMap.range killR)
        simpa [Module.finrank_pi] using this
      rw [Module.finrank_pi, Fintype.card_fin] at h1
      omega
    have hker_ne : LinearMap.ker killR ≠ ⊥ := fun h => by rw [h, finrank_bot] at hker_pos; omega
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hker_ne with ⟨α, hα_ker, hα_ne⟩
    have hα_orth : ∀ x : Fin m → K, ∑ t : Fin d, α t * Φ x t = 0 := by
      intro x
      have hxR : Φ x ∈ R := ⟨x, rfl⟩
      have hrepr := congrArg Subtype.val (bR.sum_repr ⟨Φ x, hxR⟩).symm
      have hxval : Φ x = ∑ s : Fin r, (bR.repr ⟨Φ x, hxR⟩ s) • (bR s).1 := by
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using hrepr
      rw [hxval]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro s _
      have hmul : (∑ t : Fin d, α t * ((bR.repr ⟨Φ x, hxR⟩ s) * (bR s).1 t)) =
          (bR.repr ⟨Φ x, hxR⟩ s) * ∑ t : Fin d, α t * (bR s).1 t := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => by ring
      have hs : ∑ t : Fin d, α t * (bR s).1 t = 0 := congr_fun hα_ker s
      rw [hmul, hs, mul_zero]
    have hsum0 : ∑ t : Fin d, α t • bV t = 0 := by
      apply Subtype.ext
      funext i
      have h := hα_orth (fun j => if j = i then 1 else 0)
      have h1 : ∀ t : Fin d, Φ (fun j => if j = i then 1 else 0) t = (bV t).1 i := by
        intro t
        change ∑ j : Fin m, (bV t).1 j * (if j = i then 1 else 0) = (bV t).1 i
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; simp [hji]
        · intro hm; exact (hm (Finset.mem_univ i)).elim
      simp_rw [h1] at h
      simpa [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
    have hα0 := Fintype.linearIndependent_iff.mp bV.linearIndependent α hsum0
    exact hα_ne (funext hα0)
  have hrk := LinearMap.finrank_range_add_finrank_ker Φ
  rw [LinearMap.range_eq_top.mpr hΦ_surj, finrank_top, Module.finrank_pi, Module.finrank_pi,
    Fintype.card_fin, Fintype.card_fin] at hrk
  rw [hker_eq]
  have hd_le : d ≤ m := by
    have := Submodule.finrank_le V
    simpa [Module.finrank_pi] using this
  omega

private lemma elim_D_bounds {K : Type*} [Field K] {n c q : ℕ}
    (A : Fin c → Fin n → K) (D : Fin c → Fin q → K) :
    Module.finrank K ↥((LinearMap.ker (matT A) ⊓ LinearMap.ker (matT D) : Submodule K (Fin c → K))) ≤ c ∧
    Module.finrank K ↥(LinearMap.ker (LinearMap.pi fun u :
      ((LinearMap.ker (matT A) ⊓ LinearMap.ker (matT D) : Submodule K (Fin c → K))) =>
      linDot u.1)) =
      c - Module.finrank K ↥((LinearMap.ker (matT A) ⊓ LinearMap.ker (matT D) : Submodule K (Fin c → K))) ∧
    Module.finrank K ↥(LinearMap.ker (LinearMap.pi fun u : LinearMap.ker (matT D) =>
      linDot (matT A u.1))) + c ≤
      n + q + Module.finrank K ↥((LinearMap.ker (matT A) ⊓ LinearMap.ker (matT D) : Submodule K (Fin c → K))) := by
  let DT := matT D
  let AT := matT A
  let KerD := LinearMap.ker DT
  let W0 := LinearMap.ker AT ⊓ KerD
  let KerL := LinearMap.ker (LinearMap.pi fun u : KerD => linDot (AT u.1))
  let AnnW0 := LinearMap.ker (LinearMap.pi fun u : W0 => linDot u.1)
  have hp_le : Module.finrank K W0 ≤ c := by
    have := Submodule.finrank_le W0
    simpa [Module.finrank_pi] using this
  have hann : Module.finrank K AnnW0 = c - Module.finrank K W0 := card_dual_ann_clean W0
  let ATres : KerD →ₗ[K] (Fin n → K) := AT.comp KerD.subtype
  have hker_iso : Module.finrank K (LinearMap.ker ATres) = Module.finrank K W0 := by
    let e : LinearMap.ker ATres ≃ₗ[K] W0 :=
      { toFun := fun x => ⟨x.1.1, ⟨x.2, x.1.2⟩⟩
        invFun := fun y => ⟨⟨y.1, y.2.2⟩, y.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact e.finrank_eq
  have hrk_D : Module.finrank K (LinearMap.range DT) + Module.finrank K KerD = c := by
    have h := LinearMap.finrank_range_add_finrank_ker DT
    rw [Module.finrank_pi, Fintype.card_fin] at h
    exact h
  have hrange_D : Module.finrank K (LinearMap.range DT) ≤ q := by
    have := Submodule.finrank_le (LinearMap.range DT)
    simpa [Module.finrank_pi] using this
  have hrk_AT : Module.finrank K (LinearMap.range ATres) + Module.finrank K W0 = Module.finrank K KerD := by
    have h := LinearMap.finrank_range_add_finrank_ker ATres
    rw [hker_iso] at h
    exact h
  have hKerL_eq : KerL = LinearMap.ker (LinearMap.pi fun v : LinearMap.range ATres => linDot v.1) := by
    ext x
    simp only [KerL, LinearMap.mem_ker]
    constructor
    · intro h
      funext v
      rcases v.2 with ⟨u, hu⟩
      change ∑ i : Fin n, v.1 i * x i = 0
      rw [← hu]
      exact congr_fun h u
    · intro h
      funext u
      exact congr_fun h ⟨ATres u, ⟨u, rfl⟩⟩
  have hKerL_dim : Module.finrank K KerL = n - Module.finrank K (LinearMap.range ATres) := by
    rw [hKerL_eq]
    exact card_dual_ann_clean (LinearMap.range ATres)
  have hrange_le_n : Module.finrank K (LinearMap.range ATres) ≤ n := by
    have := Submodule.finrank_le (LinearMap.range ATres)
    simpa [Module.finrank_pi] using this
  refine ⟨hp_le, hann, ?_⟩
  change Module.finrank K KerL + c ≤ n + q + Module.finrank K W0
  omega

open Classical in
private lemma card_ball1_inter_flat_le {n : ℕ}
    (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (z0 y : Fin n → Bool) :
    (Finset.univ.filter (fun x : Fin n → Bool =>
      (fun i => b2z (x i) - b2z (z0 i)) ∈ V ∧
      (Finset.univ.filter (fun i : Fin n => x i != y i)).card ≤ 1)).card ≤
    Module.finrank (ZMod 2) V + 1 := by
  let S := Finset.univ.filter (fun x : Fin n → Bool =>
    (fun i => b2z (x i) - b2z (z0 i)) ∈ V ∧
    (Finset.univ.filter (fun i : Fin n => x i != y i)).card ≤ 1)
  change S.card ≤ Module.finrank (ZMod 2) V + 1
  by_cases hne : S.Nonempty
  · rcases hne with ⟨x0, hx0⟩
    have hx0_mem : (fun i => b2z (x0 i) - b2z (z0 i)) ∈ V := (Finset.mem_filter.mp hx0).2.1
    have hx0_b : (Finset.univ.filter (fun i : Fin n => x0 i != y i)).card ≤ 1 := (Finset.mem_filter.mp hx0).2.2
    let S' := S.erase x0
    have hcard_eq : S.card = S'.card + 1 := (Finset.card_erase_add_one hx0).symm
    suffices hS' : S'.card ≤ Module.finrank (ZMod 2) V by omega
    have hv_mem : ∀ x ∈ S', (fun i => b2z (x i) + b2z (x0 i)) ∈ V := by
      intro x hx
      have hxV : (fun i => b2z (x i) - b2z (z0 i)) ∈ V := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hx)).2.1
      have hdiff := V.sub_mem hxV hx0_mem
      have heq : (fun i => b2z (x i) - b2z (z0 i)) - (fun i => b2z (x0 i) - b2z (z0 i)) =
          fun i => b2z (x i) + b2z (x0 i) := by
        funext i
        simp only [Pi.sub_apply]
        rcases zmod2_cases (b2z (x i)) with h1 | h1 <;>
          rcases zmod2_cases (b2z (x0 i)) with h2 | h2 <;>
          rcases zmod2_cases (b2z (z0 i)) with h3 | h3 <;>
          simp only [h1, h2, h3] <;> decide
      rwa [← heq]
    let vec : S' → V := fun x => ⟨fun i => b2z (x.1 i) + b2z (x0 i), hv_mem x.1 x.2⟩
    have hli : LinearIndependent (ZMod 2) vec := by
      rw [Fintype.linearIndependent_iff]
      intro c hsum
      have hsum_val : ∀ i : Fin n, ∑ x : S', c x * (b2z (x.1 i) + b2z (x0 i)) = 0 := by
        intro i
        have := congr_fun (congrArg Subtype.val hsum) i
        simpa [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vec] using this
      have hsupp : ∀ x : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => x i != y i)).card ≤ 1 →
          x = y ∨ ∃! i : Fin n, x i ≠ y i := by
        intro x hx
        by_cases h0 : (Finset.univ.filter (fun i : Fin n => x i != y i)).card = 0
        · left
          funext i
          have hemp := Finset.card_eq_zero.mp h0
          by_contra hne
          have hm : i ∈ Finset.univ.filter (fun j : Fin n => x j != y j) := by
            simp [hne]
          rw [hemp] at hm; exact Finset.notMem_empty i hm
        · right
          have h1 : (Finset.univ.filter (fun i : Fin n => x i != y i)).card = 1 := by omega
          rcases Finset.card_eq_one.mp h1 with ⟨i, hi⟩
          refine ⟨i, ?_, ?_⟩
          · have hm : i ∈ Finset.univ.filter (fun j : Fin n => x j != y j) := by rw [hi]; simp
            simpa using hm
          · intro j hj
            have hm : j ∈ Finset.univ.filter (fun k : Fin n => x k != y k) := by simp [hj]
            rw [hi] at hm
            exact Finset.mem_singleton.mp hm
      have hbool_eq_of_ne : ∀ a b c : Bool, a ≠ c → b ≠ c → a = b := by
        intro a b c; cases a <;> cases b <;> cases c <;> decide
      have hcoord_flip : ∀ (x : Fin n → Bool) (i : Fin n),
          b2z (x i) + b2z (y i) = if x i ≠ y i then 1 else 0 := by
        intro x i
        cases x i <;> cases y i <;> decide
      rcases hsupp x0 hx0_b with rfl | ⟨i0, hi0_ne, hi0_uniq⟩
      · intro x
        have hx_ne : x.1 ≠ x0 := Finset.ne_of_mem_erase x.2
        have hx_b := (Finset.mem_filter.mp (Finset.mem_of_mem_erase x.2)).2.2
        rcases hsupp x.1 hx_b with heq | ⟨ix, hix_ne, hix_uniq⟩
        · exact (hx_ne heq).elim
        · have h := hsum_val ix
          rw [Finset.sum_eq_single x] at h
          · rw [hcoord_flip x.1 ix, if_pos hix_ne, mul_one] at h
            exact h
          · intro x' _ hne'
            have hx'_b := (Finset.mem_filter.mp (Finset.mem_of_mem_erase x'.2)).2.2
            have hx'_ne : x'.1 ≠ x0 := Finset.ne_of_mem_erase x'.2
            rcases hsupp x'.1 hx'_b with heq' | ⟨ix', hix'_ne, hix'_uniq⟩
            · exact (hx'_ne heq').elim
            · have hix_eq : x'.1 ix = x0 ix := by
                by_contra hdiff
                have heqi : ix' = ix := (hix'_uniq ix hdiff).symm
                subst heqi
                apply hne'
                apply Subtype.ext
                funext j
                by_cases hj : j = ix'
                · rw [hj]; exact hbool_eq_of_ne (x'.1 ix') (x.1 ix') (x0 ix') hix'_ne hix_ne
                · have h1 : x.1 j = x0 j := by by_contra hd; exact hj (hix_uniq j hd)
                  have h2 : x'.1 j = x0 j := by by_contra hd; exact hj (hix'_uniq j hd)
                  rw [h1, h2]
              rw [hcoord_flip x'.1 ix, if_neg (not_not.mpr hix_eq), mul_zero]
          · intro hm; exact (hm (Finset.mem_univ x)).elim
      · have hother : ∀ x : S', x.1 ≠ y → c x = 0 := by
          intro x hxy
          have hx_b := (Finset.mem_filter.mp (Finset.mem_of_mem_erase x.2)).2.2
          rcases hsupp x.1 hx_b with heq | ⟨ix, hix_ne, hix_uniq⟩
          · exact (hxy heq).elim
          · have hix_ne_i0 : ix ≠ i0 := by
              intro heq
              subst heq
              apply Finset.ne_of_mem_erase x.2
              funext j
              by_cases hj : j = ix
              · rw [hj]; exact hbool_eq_of_ne (x.1 ix) (x0 ix) (y ix) hix_ne hi0_ne
              · have h1 : x.1 j = y j := by by_contra hd; exact hj (hix_uniq j hd)
                have h2 : x0 j = y j := by by_contra hd; exact hj (hi0_uniq j hd)
                rw [h1, h2]
            have hx0_ix : x0 ix = y ix := by by_contra hd; exact hix_ne_i0 (hi0_uniq ix hd)
            have h := hsum_val ix
            rw [Finset.sum_eq_single x] at h
            · rw [hx0_ix, hcoord_flip x.1 ix, if_pos hix_ne, mul_one] at h
              exact h
            · intro x' _ hne'
              have hx'_ix : x'.1 ix = y ix := by
                have hx'_b := (Finset.mem_filter.mp (Finset.mem_of_mem_erase x'.2)).2.2
                rcases hsupp x'.1 hx'_b with heq' | ⟨ix', hix'_ne, hix'_uniq⟩
                · rw [heq']
                · by_contra hdiff
                  have heqi : ix' = ix := (hix'_uniq ix hdiff).symm
                  subst heqi
                  apply hne'
                  apply Subtype.ext
                  funext j
                  by_cases hj : j = ix'
                  · rw [hj]; exact hbool_eq_of_ne (x'.1 ix') (x.1 ix') (y ix') hix'_ne hix_ne
                  · have h1 : x.1 j = y j := by by_contra hd; exact hj (hix_uniq j hd)
                    have h2 : x'.1 j = y j := by by_contra hd; exact hj (hix'_uniq j hd)
                    rw [h1, h2]
              rw [hx0_ix, hx'_ix, zmod2_add_self, mul_zero]
            · intro hm; exact (hm (Finset.mem_univ x)).elim
        intro x
        by_cases hxy : x.1 = y
        · have h := hsum_val i0
          rw [Finset.sum_eq_single x] at h
          · rw [hxy] at h
            have h1 : b2z (y i0) + b2z (x0 i0) = 1 := by
              rw [add_comm, hcoord_flip x0 i0, if_pos hi0_ne]
            rw [h1, mul_one] at h
            exact h
          · intro x' _ hne'
            have hx'y : x'.1 ≠ y := fun heq => hne' (Subtype.ext (heq.trans hxy.symm))
            rw [hother x' hx'y, zero_mul]
          · intro hm; exact (hm (Finset.mem_univ x)).elim
        · exact hother x hxy
    have hcard := hli.fintype_card_le_finrank
    simpa [Fintype.card_coe] using hcard
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty]
    omega

private lemma card_ball1_le {n : ℕ} (y : Fin n → Bool) :
    (Finset.univ.filter (fun x : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => x i != y i)).card ≤ 1)).card ≤ n + 1 := by
  have h := card_ball1_inter_flat_le (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) y y
  have htop : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) = n := by
    rw [finrank_top, Module.finrank_pi, Fintype.card_fin]
  rw [htop] at h
  simpa using h

private lemma linear_mul_pow2_bound (M p : ℕ) :
    M + p + 1 ≤ 2 ^ p * (M + 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ]
    have hpos : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by norm_num)
    nlinarith

private lemma sum_two_pow_fin (m : ℕ) : (∑ i : Fin m, 2 ^ i.val) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc, Fin.val_last, pow_succ]
    change (∑ i : Fin m, 2 ^ i.val) + 2 ^ m + 1 = 2 ^ m * 2
    omega

private lemma subset_key_inj (b : ℕ) :
    Function.Injective (fun S : Finset (Fin b) => S.card * 2 ^ b + ∑ i ∈ S, 2 ^ i.val) := by
  have hsum_lt : ∀ S : Finset (Fin b), (∑ i ∈ S, 2 ^ i.val) < 2 ^ b := by
    intro S
    have hle : (∑ i ∈ S, 2 ^ i.val) ≤ ∑ i : Fin b, 2 ^ i.val :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    have htot := sum_two_pow_fin b
    omega
  have hbit_sum : ∀ (S : Finset (Fin b)) (j : Fin b),
      (∑ i ∈ S, 2 ^ i.val).testBit j.val = decide (j ∈ S) := by
    intro S j
    have hsplit : ∀ (m : ℕ) (T : Finset (Fin m)) (k : ℕ),
        (∑ i ∈ T, 2 ^ i.val).testBit k = decide (∃ i ∈ T, i.val = k) := by
      intro m T
      induction m with
      | zero =>
        intro k
        have hT : T = ∅ := Finset.eq_empty_of_isEmpty T
        subst hT
        simp
      | succ m ih =>
        intro k
        let T' : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.castSucc ∈ T)
        have hsum_T : ∑ i ∈ T, 2 ^ i.val =
            (∑ i ∈ T', 2 ^ i.val) + if Fin.last m ∈ T then 2 ^ m else 0 := by
          have h1 : ∑ i ∈ T, 2 ^ i.val = ∑ i : Fin (m + 1), if i ∈ T then 2 ^ i.val else 0 := by
            rw [← Finset.sum_filter]
            congr 1; ext i; simp
          rw [h1, Fin.sum_univ_castSucc, Fin.val_last]
          congr 1
          rw [← Finset.sum_filter]
          rfl
        have hlt_T' : (∑ i ∈ T', 2 ^ i.val) < 2 ^ m := by
          have hle : (∑ i ∈ T', 2 ^ i.val) ≤ ∑ i : Fin m, 2 ^ i.val :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ T')
          have htot := sum_two_pow_fin m
          omega
        rw [hsum_T]
        by_cases hlast : Fin.last m ∈ T
        · rw [if_pos hlast]
          have hxor : (∑ i ∈ T', 2 ^ i.val) + 2 ^ m = (∑ i ∈ T', 2 ^ i.val) ||| 2 ^ m := by
            rw [Nat.add_comm, Nat.or_comm]
            simpa using Nat.two_pow_add_eq_or_of_lt (a := 1) hlt_T'
          rw [hxor, Nat.testBit_or, ih T' k, Nat.testBit_two_pow]
          by_cases hkm : m = k
          · subst hkm
            simp only [decide_true, Bool.or_true]
            symm; simp only [decide_eq_true_eq]
            exact ⟨Fin.last m, hlast, rfl⟩
          · simp only [hkm, decide_false, Bool.or_false]
            congr 1
            apply propext
            constructor
            · rintro ⟨i, hi, rfl⟩
              exact ⟨i.castSucc, (Finset.mem_filter.mp hi).2, rfl⟩
            · rintro ⟨i, hi, rfl⟩
              have hne : i ≠ Fin.last m := fun heq => hkm (by rw [heq]; rfl)
              have hlt : i.val < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) (fun h => hne (Fin.ext h))
              refine ⟨⟨i.val, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
              convert hi using 1
              exact Fin.ext rfl
        · rw [if_neg hlast, add_zero, ih T' k]
          congr 1
          apply propext
          constructor
          · rintro ⟨i, hi, rfl⟩
            exact ⟨i.castSucc, (Finset.mem_filter.mp hi).2, rfl⟩
          · rintro ⟨i, hi, rfl⟩
            have hne : i ≠ Fin.last m := fun heq => hlast (heq ▸ hi)
            have hlt : i.val < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) (fun h => hne (Fin.ext h))
            refine ⟨⟨i.val, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
            convert hi using 1
            exact Fin.ext rfl
    rw [hsplit b S j.val]
    congr 1
    apply propext
    constructor
    · rintro ⟨i, hi, hval⟩
      exact (Fin.ext hval) ▸ hi
    · intro hj
      exact ⟨j, hj, rfl⟩
  intro S1 S2 heq
  have hlt1 := hsum_lt S1
  have hlt2 := hsum_lt S2
  have hsum_eq : (∑ i ∈ S1, 2 ^ i.val) = ∑ i ∈ S2, 2 ^ i.val := by
    have hmod := congrArg (fun x => x % 2 ^ b) heq
    rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod
    exact hmod
  ext j
  have ht := congrArg (fun x => x.testBit j.val) hsum_eq
  rw [hbit_sum S1 j, hbit_sum S2 j] at ht
  exact decide_eq_decide.mp ht

private lemma rank_bij_of_inj {α : Type*} [Fintype α] [DecidableEq α] (key : α → ℕ)
    (hinj : Function.Injective key) :
    let rk := fun x : α => (Finset.univ.filter (fun y : α => key y < key x)).card
    (∀ x y : α, key x < key y ↔ rk x < rk y) ∧
    (∀ x : α, rk x < Fintype.card α) ∧
    Function.Injective rk ∧
    (∀ m < Fintype.card α, ∃ x : α, rk x = m) := by
  intro rk
  have hmono : ∀ x y : α, key x < key y → rk x < rk y := by
    intro x y hlt
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, lt_trans (Finset.mem_filter.mp hz).2 hlt⟩
    · intro heq
      have hx : x ∈ Finset.univ.filter (fun z : α => key z < key y) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ x, hlt⟩
      rw [← heq] at hx
      exact lt_irrefl _ (Finset.mem_filter.mp hx).2
  have hiff : ∀ x y : α, key x < key y ↔ rk x < rk y := by
    intro x y
    constructor
    · exact hmono x y
    · intro hrk
      by_contra hnot
      rcases eq_or_lt_of_le (le_of_not_gt hnot) with heq | hgt
      · rw [hinj heq] at hrk; exact lt_irrefl _ hrk
      · exact lt_asymm hrk (hmono y x hgt)
  have hlt_card : ∀ x : α, rk x < Fintype.card α := by
    intro x
    have hss : Finset.univ.filter (fun y : α => key y < key x) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_univ _, fun heq => ?_⟩
      have hx : x ∈ Finset.univ.filter (fun y : α => key y < key x) := by rw [heq]; exact Finset.mem_univ x
      exact lt_irrefl _ (Finset.mem_filter.mp hx).2
    simpa [Finset.card_univ] using Finset.card_lt_card hss
  have hrk_inj : Function.Injective rk := by
    intro x y heq
    by_contra hne
    rcases lt_or_gt_of_ne (fun hk => hne (hinj hk)) with hlt | hgt
    · exact ne_of_lt (hmono x y hlt) heq
    · exact ne_of_gt (hmono y x hgt) heq
  have hsurj : ∀ m < Fintype.card α, ∃ x : α, rk x = m := by
    let f : α → Fin (Fintype.card α) := fun x => ⟨rk x, hlt_card x⟩
    have hf_inj : Function.Injective f := fun x y h => hrk_inj (Fin.mk.inj h)
    have hf_bij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by simp⟩
    intro m hm
    rcases hf_bij.2 ⟨m, hm⟩ with ⟨x, hx⟩
    exact ⟨x, congrArg Fin.val hx⟩
  exact ⟨hiff, hlt_card, hrk_inj, hsurj⟩

private lemma mobius_downset_zmod2 {b : ℕ} (D : Finset (Finset (Fin b)))
    (hdown : ∀ S ∈ D, ∀ T : Finset (Fin b), T ⊆ S → T ∈ D)
    (S U : Finset (Fin b)) (hS : S ∈ D) (hU : U ∈ D) :
    (∑ T ∈ D.filter (fun T => S ⊆ T), if T ⊆ U then (1 : ZMod 2) else 0) =
      if U = S then 1 else 0 := by
  classical
  have hfilt : (D.filter (fun T => S ⊆ T)).filter (fun T => T ⊆ U) =
      Finset.univ.filter (fun T : Finset (Fin b) => S ⊆ T ∧ T ⊆ U) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hST⟩, hTU⟩; exact ⟨hST, hTU⟩
    · rintro ⟨hST, hTU⟩; exact ⟨⟨hdown U hU T hTU, hST⟩, hTU⟩
  rw [← Finset.sum_filter, hfilt, Finset.sum_const, nsmul_eq_mul, mul_one]
  by_cases hSU : S ⊆ U
  · by_cases heq : U = S
    · subst heq
      rw [if_pos rfl]
      have hsing : Finset.univ.filter (fun T : Finset (Fin b) => U ⊆ T ∧ T ⊆ U) = {U} := by
        ext T; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun ⟨h1, h2⟩ => Finset.Subset.antisymm h2 h1, fun h => h ▸ ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩⟩
      rw [hsing, Finset.card_singleton]; simp
    · rw [if_neg heq]
      have hcard_pow : (Finset.univ.filter (fun T : Finset (Fin b) => S ⊆ T ∧ T ⊆ U)).card =
          2 ^ (U \ S).card := by
        have hbij : (Finset.univ.filter (fun T : Finset (Fin b) => S ⊆ T ∧ T ⊆ U)).card =
            (U \ S).powerset.card := by
          refine Finset.card_bij (fun T _ => T \ S)
            (fun T hT => Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff (Finset.mem_filter.mp hT).2.2 (Finset.Subset.refl _)))
            (fun T1 hT1 T2 hT2 heq' => by
              have h1 := Finset.sdiff_union_of_subset (Finset.mem_filter.mp hT1).2.1
              have h2 := Finset.sdiff_union_of_subset (Finset.mem_filter.mp hT2).2.1
              rw [← h1, ← h2, heq'])
            (fun R hR => ⟨R ∪ S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_right,
              Finset.union_subset ((Finset.mem_powerset.mp hR).trans Finset.sdiff_subset) hSU⟩, by
                rw [Finset.union_sdiff_cancel_right]
                exact Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hR) Finset.sdiff_disjoint⟩)
        rw [hbij, Finset.card_powerset]
      rw [hcard_pow]
      have hpos : 0 < (U \ S).card := by
        rw [Finset.card_pos, Finset.sdiff_nonempty]
        intro hUS
        exact heq (Finset.Subset.antisymm hUS hSU)
      have heven : 2 ∣ 2 ^ (U \ S).card := by
        have h1 : (U \ S).card = ((U \ S).card - 1) + 1 := by omega
        rw [h1, pow_succ]
        exact dvd_mul_left 2 _
      rcases heven with ⟨k, hk⟩
      rw [hk, Nat.cast_mul]
      have h20 : ((2 : ℕ) : ZMod 2) = 0 := by decide
      rw [h20, zero_mul]
  · have hne : U ≠ S := fun h => hSU (h ▸ Finset.Subset.refl _)
    rw [if_neg hne]
    have hemp : Finset.univ.filter (fun T : Finset (Fin b) => S ⊆ T ∧ T ⊆ U) = ∅ := by
      ext T; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2⟩; exact hSU (h1.trans h2)
    rw [hemp, Finset.card_empty]; simp

private lemma list_get_append_left {α : Type*} (l₁ l₂ : List α) (i : Fin (l₁ ++ l₂).length)
    (h : i.val < l₁.length) : (l₁ ++ l₂).get i = l₁.get ⟨i.val, h⟩ := by
  simp only [List.get_eq_getElem]
  exact List.getElem_append_left h

private lemma list_get_append_right {α : Type*} (l₁ l₂ : List α) (i : Fin (l₁ ++ l₂).length)
    (h : l₁.length ≤ i.val) :
    (l₁ ++ l₂).get i = l₂.get ⟨i.val - l₁.length, by have := i.isLt; simp at this; omega⟩ := by
  simp only [List.get_eq_getElem]
  exact List.getElem_append_right h

private def appendXor2 (n : ℕ) (gs : List Gate) (u v : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.mod 2, [u, v]⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1)

private lemma appendXor2_spec (n : ℕ) (gs : List Gate) (u v : ℕ)
    (hleg : legalGates n gs) (hu : u < n + gs.length) (hv : v < n + gs.length) :
    let res := appendXor2 n gs u v
    legalGates n res.1 ∧
    res.1.countP isPaid = gs.countP isPaid ∧
    res.2 < n + res.1.length ∧
    (∀ w < n + gs.length, ∀ x : Fin n → Bool,
      (wiresOf res.1 (List.ofFn x)).getD w false = (wiresOf gs (List.ofFn x)).getD w false) ∧
    (∀ x : Fin n → Bool,
      (wiresOf res.1 (List.ofFn x)).getD res.2 false =
        xor ((wiresOf gs (List.ofFn x)).getD u false) ((wiresOf gs (List.ofFn x)).getD v false)) := by
  intro res
  have hlen : res.1.length = gs.length + 2 := by simp [res, appendXor2]
  have hleg' : legalGates n res.1 := by
    refine ⟨?_, ?_⟩
    · intro i w hw
      by_cases h1 : i.val < gs.length
      · have hget : res.1.get i = gs.get ⟨i.val, h1⟩ := list_get_append_left gs _ i h1
        rw [hget] at hw
        exact hleg.1 ⟨i.val, h1⟩ w hw
      · have hright := list_get_append_right gs [⟨.mod 2, [u, v]⟩, ⟨.not, [n + gs.length]⟩] i (by omega)
        change res.1.get i = _ at hright
        rw [hright] at hw
        have hi : i.val < gs.length + 2 := lt_of_lt_of_eq i.isLt hlen
        by_cases h2 : i.val = gs.length
        · have hidx : (⟨i.val - gs.length, by omega⟩ : Fin 2) = ⟨0, by decide⟩ := Fin.ext (by dsimp only; omega)
          rw [hidx] at hw
          simp only [List.get_eq_getElem, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl <;> omega
        · have h3 : i.val = gs.length + 1 := by omega
          have hidx : (⟨i.val - gs.length, by omega⟩ : Fin 2) = ⟨1, by decide⟩ := Fin.ext (by dsimp only; omega)
          rw [hidx] at hw
          simp only [List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero,
            List.mem_cons, List.not_mem_nil, or_false] at hw
          omega
    · intro h hh
      simp only [res, appendXor2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with hgs | rfl | rfl
      · exact hleg.2 h hgs
      · exact ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  have hcnt : res.1.countP isPaid = gs.countP isPaid := by
    have h1 : isPaid ⟨.mod 2, [u, v]⟩ = false := by simp [isPaid]
    have h2 : isPaid ⟨.not, [n + gs.length]⟩ = false := by simp [isPaid]
    simp [res, appendXor2, List.countP_append, h1, h2]
  have hpref : ∀ w < n + gs.length, ∀ x : Fin n → Bool,
      (wiresOf res.1 (List.ofFn x)).getD w false = (wiresOf gs (List.ofFn x)).getD w false := by
    intro w hw x
    exact wiresOf_append_prefix gs _ (List.ofFn x) w (by simp [hw])
  have heval : ∀ x : Fin n → Bool,
      (wiresOf res.1 (List.ofFn x)).getD res.2 false =
        xor ((wiresOf gs (List.ofFn x)).getD u false) ((wiresOf gs (List.ofFn x)).getD v false) := by
    intro x
    set w0 := wiresOf gs (List.ofFn x)
    have hw0_len : w0.length = n + gs.length := by rw [wiresOf_length, List.length_ofFn]
    set g1 : Gate := ⟨.mod 2, [u, v]⟩
    set w1 := w0 ++ [g1.op.eval [w0.getD u false, w0.getD v false]]
    have hw1_len : w1.length = n + gs.length + 1 := by simp [w1, hw0_len]
    have hres_w : wiresOf res.1 (List.ofFn x) =
        w1 ++ [GateOp.not.eval [w1.getD (n + gs.length) false]] := by
      simp [res, appendXor2, wiresOf, List.foldl_append, w1, w0, g1]
    have hmid : w1.getD (n + gs.length) false = g1.op.eval [w0.getD u false, w0.getD v false] := by
      rw [← hw0_len]; exact getD_append_last w0 _ false
    rw [hres_w, show res.2 = w1.length from hw1_len.symm, getD_append_last, hmid]
    simp only [g1]
    cases w0.getD u false <;> cases w0.getD v false <;> decide
  exact ⟨hleg', hcnt, by simp [res, appendXor2]; omega, hpref, heval⟩

private def appendConstFalse (n : ℕ) (gs : List Gate) : List Gate × ℕ :=
  (gs ++ [⟨.or, []⟩], n + gs.length)

private lemma appendConstFalse_spec (n : ℕ) (gs : List Gate) (hleg : legalGates n gs) :
    let res := appendConstFalse n gs
    legalGates n res.1 ∧
    res.1.countP isPaid = gs.countP isPaid ∧
    res.2 < n + res.1.length ∧
    (∀ w < n + gs.length, ∀ x : Fin n → Bool,
      (wiresOf res.1 (List.ofFn x)).getD w false = (wiresOf gs (List.ofFn x)).getD w false) ∧
    (∀ x : Fin n → Bool, (wiresOf res.1 (List.ofFn x)).getD res.2 false = false) := by
  intro res
  have hlen : res.1.length = gs.length + 1 := by simp [res, appendConstFalse]
  have hleg' : legalGates n res.1 := by
    refine ⟨?_, ?_⟩
    · intro i w hw
      by_cases h1 : i.val < gs.length
      · have hget : res.1.get i = gs.get ⟨i.val, h1⟩ := list_get_append_left gs _ i h1
        rw [hget] at hw
        exact hleg.1 ⟨i.val, h1⟩ w hw
      · have hright := list_get_append_right gs [⟨.or, []⟩] i (by omega)
        change res.1.get i = _ at hright
        rw [hright] at hw
        have hidx : (⟨i.val - gs.length, by have := i.isLt; omega⟩ : Fin 1) = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
        rw [hidx] at hw
        simp at hw
    · intro h hh
      simp only [res, appendConstFalse, List.mem_append, List.mem_singleton] at hh
      rcases hh with hgs | rfl
      · exact hleg.2 h hgs
      · exact ⟨by simp, Or.inr (Or.inl rfl)⟩
  have hcnt : res.1.countP isPaid = gs.countP isPaid := by
    have h1 : isPaid ⟨.or, []⟩ = false := by simp [isPaid]
    simp [res, appendConstFalse, List.countP_append, h1]
  have hpref : ∀ w < n + gs.length, ∀ x : Fin n → Bool,
      (wiresOf res.1 (List.ofFn x)).getD w false = (wiresOf gs (List.ofFn x)).getD w false := by
    intro w hw x
    exact wiresOf_append_prefix gs _ (List.ofFn x) w (by simp [hw])
  have heval : ∀ x : Fin n → Bool, (wiresOf res.1 (List.ofFn x)).getD res.2 false = false := by
    intro x
    set w0 := wiresOf gs (List.ofFn x)
    have hw0_len : w0.length = n + gs.length := by rw [wiresOf_length, List.length_ofFn]
    have hstep : wiresOf res.1 (List.ofFn x) = w0 ++ [GateOp.or.eval []] := by
      simp [res, appendConstFalse, wiresOf, List.foldl_append, w0]
    rw [hstep, show res.2 = w0.length from hw0_len.symm, getD_append_last]
    rfl
  exact ⟨hleg', hcnt, by simp [res, appendConstFalse], hpref, heval⟩

private def appendAnd2 (n : ℕ) (gs : List Gate) (u v : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.and, [u, v]⟩], n + gs.length)

private lemma appendAnd2_spec (n : ℕ) (gs : List Gate) (u v : ℕ)
    (hleg : legalGates n gs) (hu : u < n + gs.length) (hv : v < n + gs.length) :
    let res := appendAnd2 n gs u v
    legalGates n res.1 ∧
    res.1.countP isPaid = gs.countP isPaid + 1 ∧
    res.2 < n + res.1.length ∧
    (∀ w < n + gs.length, ∀ x : Fin n → Bool,
      (wiresOf res.1 (List.ofFn x)).getD w false = (wiresOf gs (List.ofFn x)).getD w false) ∧
    (∀ x : Fin n → Bool,
      (wiresOf res.1 (List.ofFn x)).getD res.2 false =
        ((wiresOf gs (List.ofFn x)).getD u false && (wiresOf gs (List.ofFn x)).getD v false)) := by
  intro res
  have hlen : res.1.length = gs.length + 1 := by simp [res, appendAnd2]
  have hleg' : legalGates n res.1 := by
    refine ⟨?_, ?_⟩
    · intro i w hw
      by_cases h1 : i.val < gs.length
      · have hget : res.1.get i = gs.get ⟨i.val, h1⟩ := list_get_append_left gs _ i h1
        rw [hget] at hw
        exact hleg.1 ⟨i.val, h1⟩ w hw
      · have hright := list_get_append_right gs [⟨.and, [u, v]⟩] i (by omega)
        change res.1.get i = _ at hright
        rw [hright] at hw
        have hidx : (⟨i.val - gs.length, by have := i.isLt; omega⟩ : Fin 1) = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
        rw [hidx] at hw
        simp only [List.get_eq_getElem, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> omega
    · intro h hh
      simp only [res, appendAnd2, List.mem_append, List.mem_singleton] at hh
      rcases hh with hgs | rfl
      · exact hleg.2 h hgs
      · exact ⟨by simp, Or.inl rfl⟩
  have hcnt : res.1.countP isPaid = gs.countP isPaid + 1 := by
    have h1 : isPaid ⟨.and, [u, v]⟩ = true := by simp [isPaid]
    simp [res, appendAnd2, List.countP_append, h1]
  have hpref : ∀ w < n + gs.length, ∀ x : Fin n → Bool,
      (wiresOf res.1 (List.ofFn x)).getD w false = (wiresOf gs (List.ofFn x)).getD w false := by
    intro w hw x
    exact wiresOf_append_prefix gs _ (List.ofFn x) w (by simp [hw])
  have heval : ∀ x : Fin n → Bool,
      (wiresOf res.1 (List.ofFn x)).getD res.2 false =
        ((wiresOf gs (List.ofFn x)).getD u false && (wiresOf gs (List.ofFn x)).getD v false) := by
    intro x
    set w0 := wiresOf gs (List.ofFn x)
    have hw0_len : w0.length = n + gs.length := by rw [wiresOf_length, List.length_ofFn]
    have hstep : wiresOf res.1 (List.ofFn x) = w0 ++ [GateOp.and.eval [w0.getD u false, w0.getD v false]] := by
      simp [res, appendAnd2, wiresOf, List.foldl_append, w0]
    rw [hstep, show res.2 = w0.length from hw0_len.symm, getD_append_last]
    cases w0.getD u false <;> cases w0.getD v false <;> decide
  exact ⟨hleg', hcnt, by simp [res, appendAnd2], hpref, heval⟩

private lemma exists_xorList_wire (n : ℕ) (gs : List Gate) (ws : List ℕ)
    (hleg : legalGates n gs) (hws : ∀ w ∈ ws, w < n + gs.length) :
    ∃ (gs' : List Gate) (out : ℕ),
      gs.length ≤ gs'.length ∧
      legalGates n gs' ∧
      gs'.countP isPaid = gs.countP isPaid ∧
      out < n + gs'.length ∧
      (∀ w < n + gs.length, ∀ x : Fin n → Bool,
        (wiresOf gs' (List.ofFn x)).getD w false = (wiresOf gs (List.ofFn x)).getD w false) ∧
      (∀ x : Fin n → Bool,
        b2z ((wiresOf gs' (List.ofFn x)).getD out false) =
          (ws.map (fun w => b2z ((wiresOf gs (List.ofFn x)).getD w false))).sum) := by
  induction ws with
  | nil =>
    have h := appendConstFalse_spec n gs hleg
    refine ⟨(appendConstFalse n gs).1, (appendConstFalse n gs).2, by simp [appendConstFalse],
      h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun x => by rw [h.2.2.2.2 x]; simp [b2z]⟩
  | cons a t ih =>
    have ha : a < n + gs.length := hws a List.mem_cons_self
    have ht : ∀ w ∈ t, w < n + gs.length := fun w hw => hws w (List.mem_cons_of_mem a hw)
    rcases ih ht with ⟨gs1, out1, hlen1, hleg1, hcnt1, hout1, hpref1, heval1⟩
    have h2 := appendXor2_spec n gs1 a out1 hleg1 (by omega) hout1
    refine ⟨(appendXor2 n gs1 a out1).1, (appendXor2 n gs1 a out1).2,
      by simp [appendXor2]; omega, h2.1, by rw [h2.2.1, hcnt1], h2.2.2.1, ?_, ?_⟩
    · intro w hw x
      rw [h2.2.2.2.1 w (by omega) x, hpref1 w hw x]
    · intro x
      rw [h2.2.2.2.2 x, b2z_xor, hpref1 a ha x, heval1 x]
      simp

private lemma upper_bound_919 (n b g : ℕ) (hbn : b ≤ n)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin (n - b) → ℕ)
    (read : (Fin (n - b) → Bool) → (Fin n → Bool))
    (hleg : (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < n + i.val) ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))))
    (hcost : C.gates.countP (fun h => @decide
      ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)) ≤ g) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      let wires := C.wires (List.ofFn x)
      let y := read (fun j => wires.getD (tap j) false)
      ((Finset.univ : Finset (Fin n)).filter (fun i => x i != y i)).card ≤ 1)).card ≤
    2 ^ (n - b) * min (2 ^ b) (min (n + 1) (b + g + 1)) := by
  classical
  let c := n - b
  let W := Fin n → Bool
  let Msg := Fin c → Bool
  let send : W → Msg := fun x j => (C.wires (List.ofFn x)).getD (tap j) false
  let hitsVal : ℕ :=
    ((Finset.univ : Finset W).filter (fun x =>
      ((Finset.univ : Finset (Fin n)).filter (fun i => x i != read (send x) i)).card ≤ 1)).card
  change hitsVal ≤ 2 ^ c * min (2 ^ b) (min (n + 1) (b + g + 1))
  have h1 : hitsVal ≤ 2 ^ c * 2 ^ b := by
    have hcard : hitsVal ≤ Fintype.card W := Finset.card_le_univ _
    have hW : Fintype.card W = 2 ^ n := by simp [W]
    have hcb : 2 ^ c * 2 ^ b = 2 ^ n := by rw [← pow_add]; congr 1; omega
    omega
  have h2 : hitsVal ≤ 2 ^ c * (n + 1) := by
    have hpart : hitsVal = ∑ m : Msg,
        (Finset.univ.filter (fun x : W => send x = m ∧
          (Finset.univ.filter (fun i : Fin n => x i != read m i)).card ≤ 1)).card := by
      have hbiU : (Finset.univ : Finset W).filter (fun x =>
          (Finset.univ.filter (fun i : Fin n => x i != read (send x) i)).card ≤ 1) =
          (Finset.univ : Finset Msg).biUnion (fun m =>
            Finset.univ.filter (fun x : W => send x = m ∧
              (Finset.univ.filter (fun i : Fin n => x i != read m i)).card ≤ 1)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        constructor
        · intro h; exact ⟨send x, rfl, h⟩
        · rintro ⟨m, rfl, h⟩; exact h
      change ((Finset.univ : Finset W).filter (fun x =>
          (Finset.univ.filter (fun i : Fin n => x i != read (send x) i)).card ≤ 1)).card = _
      rw [hbiU, Finset.card_biUnion]
      intro m1 _ m2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact hne ((Finset.mem_filter.mp hx1).2.1.symm.trans (Finset.mem_filter.mp hx2).2.1)
    rw [hpart]
    have hle : ∑ m : Msg,
        (Finset.univ.filter (fun x : W => send x = m ∧
          (Finset.univ.filter (fun i : Fin n => x i != read m i)).card ≤ 1)).card ≤
        ∑ _m : Msg, (n + 1) := by
      refine Finset.sum_le_sum fun m _ => ?_
      refine (Finset.card_le_card ?_).trans (card_ball1_le (read m))
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2.2⟩
    have hrhs : ∑ _m : Msg, (n + 1) = 2 ^ c * (n + 1) := by simp [Msg]
    exact hle.trans (le_of_eq hrhs)
  have h3 : hitsVal ≤ 2 ^ c * (b + g + 1) := by
    rcases wires_affine_paid n C.gates hleg.2 with ⟨q, nl, hq_le, hwire_aff⟩
    have hq_leg : q ≤ g := hq_le.trans hcost
    let A : Fin c → Fin n → ZMod 2 := fun j => Classical.choose (hwire_aff (tap j))
    let D : Fin c → Fin q → ZMod 2 := fun j => Classical.choose (Classical.choose_spec (hwire_aff (tap j)))
    let a : Fin c → ZMod 2 := fun j =>
      Classical.choose (Classical.choose_spec (Classical.choose_spec (hwire_aff (tap j))))
    have hsend_aff : ∀ (j : Fin c) (x : W),
        b2z (send x j) = a j + (∑ i : Fin n, A j i * b2z (x i)) + ∑ r : Fin q, D j r * nl r x :=
      fun j => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hwire_aff (tap j))))
    let DT := matT D
    let AT := matT A
    let KerD : Submodule (ZMod 2) (Fin c → ZMod 2) := LinearMap.ker DT
    let W0 : Submodule (ZMod 2) (Fin c → ZMod 2) := LinearMap.ker AT ⊓ KerD
    let KerL : Submodule (ZMod 2) (Fin n → ZMod 2) :=
      LinearMap.ker (LinearMap.pi fun u : KerD => linDot (AT u.1))
    let AnnW0 : Submodule (ZMod 2) (Fin c → ZMod 2) :=
      LinearMap.ker (LinearMap.pi fun u : W0 => linDot u.1)
    have hbounds := elim_D_bounds A D
    have hp_le : Module.finrank (ZMod 2) W0 ≤ c := hbounds.1
    have hann_dim : Module.finrank (ZMod 2) AnnW0 = c - Module.finrank (ZMod 2) W0 := hbounds.2.1
    have hKerL_dim : Module.finrank (ZMod 2) KerL + c ≤ n + q + Module.finrank (ZMod 2) W0 := hbounds.2.2
    set p := Module.finrank (ZMod 2) W0
    let Mimg : Finset Msg := Finset.univ.image send
    have hMimg_card : Mimg.card ≤ 2 ^ (c - p) := by
      by_cases hne : Mimg.Nonempty
      · rcases hne with ⟨m0, hm0⟩
        rcases Finset.mem_image.mp hm0 with ⟨x0, _, rfl⟩
        have hm_mem : ∀ m ∈ Mimg, (fun j => b2z (m j) - b2z (send x0 j)) ∈ AnnW0 := by
          intro m hm
          rcases Finset.mem_image.mp hm with ⟨x, _, rfl⟩
          rw [LinearMap.mem_ker]
          funext u
          change ∑ j : Fin c, u.1 j * (b2z (send x j) - b2z (send x0 j)) = 0
          have hlin : ∀ z : W, ∑ j : Fin c, u.1 j * b2z (send z j) = ∑ j : Fin c, u.1 j * a j := by
            intro z
            simp_rw [hsend_aff _ z, mul_add, Finset.sum_add_distrib]
            have hA0 : ∑ j : Fin c, u.1 j * ∑ i : Fin n, A j i * b2z (z i) = 0 := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_eq_zero
              intro i _
              have h1 : (∑ j : Fin c, u.1 j * (A j i * b2z (z i))) = (AT u.1 i) * b2z (z i) := by
                simp only [AT, matT, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, mul_assoc]
              rw [h1, congr_fun u.2.1 i, Pi.zero_apply, zero_mul]
            have hD0 : ∑ j : Fin c, u.1 j * ∑ r : Fin q, D j r * nl r z = 0 := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_eq_zero
              intro r _
              have h1 : (∑ j : Fin c, u.1 j * (D j r * nl r z)) = (DT u.1 r) * nl r z := by
                simp only [DT, matT, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, mul_assoc]
              rw [h1, congr_fun u.2.2 r, Pi.zero_apply, zero_mul]
            rw [hA0, hD0, add_zero, add_zero]
          simp_rw [mul_sub, Finset.sum_sub_distrib, hlin x, hlin x0, sub_self]
        have hinj_m : Set.InjOn (fun m : Msg => (fun j => b2z (m j) - b2z (send x0 j))) (Mimg : Set Msg) := by
          intro m1 _ m2 _ heq
          funext j
          have hj := congr_fun heq j
          exact b2z_inj (sub_left_inj.mp hj)
        have hcard_le : Mimg.card ≤ Fintype.card AnnW0 := by
          have h1 := Finset.card_le_card_of_injOn
            (f := fun m : Msg => if hm : m ∈ Mimg then (⟨fun j => b2z (m j) - b2z (send x0 j), hm_mem m hm⟩ : AnnW0) else 0)
            (s := Mimg) (t := Finset.univ)
            (fun _ _ => Finset.mem_univ _)
            (fun m1 hm1 m2 hm2 heq => by
              dsimp only at heq
              rw [dif_pos (Finset.mem_coe.mp hm1), dif_pos (Finset.mem_coe.mp hm2)] at heq
              exact hinj_m hm1 hm2 (congrArg Subtype.val heq))
          simpa using h1
        have hAnn_card : Fintype.card AnnW0 = 2 ^ (c - p) := by
          have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := AnnW0)
          rw [ZMod.card, hann_dim] at h1
          exact h1
        omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.card_empty]; exact Nat.zero_le _
    have hpart : hitsVal = ∑ m ∈ Mimg,
        (Finset.univ.filter (fun x : W => send x = m ∧
          (Finset.univ.filter (fun i : Fin n => x i != read m i)).card ≤ 1)).card := by
      have hbiU : (Finset.univ : Finset W).filter (fun x =>
          (Finset.univ.filter (fun i : Fin n => x i != read (send x) i)).card ≤ 1) =
          Mimg.biUnion (fun m =>
            Finset.univ.filter (fun x : W => send x = m ∧
              (Finset.univ.filter (fun i : Fin n => x i != read m i)).card ≤ 1)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        constructor
        · intro h; exact ⟨send x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, rfl, h⟩
        · rintro ⟨m, _, rfl, h⟩; exact h
      change ((Finset.univ : Finset W).filter (fun x =>
          (Finset.univ.filter (fun i : Fin n => x i != read (send x) i)).card ≤ 1)).card = _
      rw [hbiU, Finset.card_biUnion]
      intro m1 _ m2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact hne ((Finset.mem_filter.mp hx1).2.1.symm.trans (Finset.mem_filter.mp hx2).2.1)
    rw [hpart]
    have hfiber_le : ∀ m ∈ Mimg,
        (Finset.univ.filter (fun x : W => send x = m ∧
          (Finset.univ.filter (fun i : Fin n => x i != read m i)).card ≤ 1)).card ≤ b + g + p + 1 := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨x0, _, rfl⟩
      have hsub : Finset.univ.filter (fun x : W => send x = send x0 ∧
          (Finset.univ.filter (fun i : Fin n => x i != read (send x0) i)).card ≤ 1) ⊆
          Finset.univ.filter (fun x : W =>
            (fun i => b2z (x i) - b2z (x0 i)) ∈ KerL ∧
            (Finset.univ.filter (fun i : Fin n => x i != read (send x0) i)).card ≤ 1) := by
        intro x hx
        rcases (Finset.mem_filter.mp hx).2 with ⟨hsx, hball⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_, hball⟩
        rw [LinearMap.mem_ker]
        funext u
        change ∑ i : Fin n, AT u.1 i * (b2z (x i) - b2z (x0 i)) = 0
        have hlin : ∀ z : W, ∑ j : Fin c, u.1 j * b2z (send z j) =
            (∑ j : Fin c, u.1 j * a j) + ∑ i : Fin n, AT u.1 i * b2z (z i) := by
          intro z
          simp_rw [hsend_aff _ z, mul_add, Finset.sum_add_distrib]
          have hA : ∑ j : Fin c, u.1 j * ∑ i : Fin n, A j i * b2z (z i) =
              ∑ i : Fin n, AT u.1 i * b2z (z i) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [AT, matT, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, mul_assoc]
          have hD0 : ∑ j : Fin c, u.1 j * ∑ r : Fin q, D j r * nl r z = 0 := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_eq_zero
            intro r _
            have h1 : (∑ j : Fin c, u.1 j * (D j r * nl r z)) = (DT u.1 r) * nl r z := by
              simp only [DT, matT, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, mul_assoc]
            rw [h1, congr_fun u.2 r, Pi.zero_apply, zero_mul]
          rw [hA, hD0, add_zero]
        have heq_m : ∑ j : Fin c, u.1 j * b2z (send x j) = ∑ j : Fin c, u.1 j * b2z (send x0 j) := by
          rw [hsx]
        rw [hlin x, hlin x0] at heq_m
        have hdiff := sub_eq_zero.mpr (add_left_cancel heq_m)
        simpa only [mul_sub, Finset.sum_sub_distrib] using hdiff
      have hfb := (Finset.card_le_card hsub).trans (card_ball1_inter_flat_le KerL x0 (read (send x0)))
      omega
    calc ∑ m ∈ Mimg,
          (Finset.univ.filter (fun x : W => send x = m ∧
            (Finset.univ.filter (fun i : Fin n => x i != read m i)).card ≤ 1)).card
        ≤ ∑ _m ∈ Mimg, (b + g + p + 1) := Finset.sum_le_sum hfiber_le
      _ = Mimg.card * (b + g + p + 1) := by simp
      _ ≤ 2 ^ (c - p) * (b + g + p + 1) := Nat.mul_le_mul_right _ hMimg_card
      _ ≤ 2 ^ (c - p) * (2 ^ p * (b + g + 1)) := Nat.mul_le_mul_left _ (linear_mul_pow2_bound (b + g) p)
      _ = 2 ^ c * (b + g + 1) := by
          rw [← mul_assoc, ← pow_add]
          congr 2; omega
  rcases min_cases (2 ^ b) (min (n + 1) (b + g + 1)) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]; exact h1
  · rw [heq]
    rcases min_cases (n + 1) (b + g + 1) with ⟨heq2, _⟩ | ⟨heq2, _⟩
    · rw [heq2]; exact h2
    · rw [heq2]; exact h3

end PEqualNP.Outside.L_lib_919

open PEqualNP.Outside.L_lib_919 in
theorem PEqualNP.Outside.L_lib_919 :
    ∀ (n b g : Nat), b ≤ n →
      let c := n-b
      let W := Fin n → Bool
      let Msg := Fin c → Bool
      let Circ := PEqualNP.CircuitLowerBounds.Circuit
      let legal := fun (C : Circ) =>
        (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < n+i.val) ∧
        (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
          (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
      let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
        ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
      let hits := fun (C : Circ) (tap : Fin c → Nat) (read : Msg → W) =>
        ((Finset.univ : Finset W).filter (fun x =>
          let wires := C.wires (List.ofFn x)
          let y := read (fun j => wires.getD (tap j) false)
          ((Finset.univ : Finset (Fin n)).filter (fun i => x i != y i)).card ≤ 1)).card
      let attainable : Set Nat := {s | ∃ (C : Circ) (tap : Fin c → Nat) (read : Msg → W),
        legal C ∧ cost C ≤ g ∧ (∀ j, tap j < n+C.gates.length) ∧ hits C tap read = s}
      IsGreatest attainable (2^c * min (2^b) (min (n+1) (b+g+1))) := by
  classical
  intro n b g hbn c W Msg Circ legal cost hits attainable
  set L := min (2 ^ b) (min (n + 1) (b + g + 1))
  have hupper : ∀ s ∈ attainable, s ≤ 2 ^ c * L := by
    rintro s ⟨C, tap, read, hleg, hcost, _, rfl⟩
    exact upper_bound_919 n b g hbn C tap read hleg hcost
  refine ⟨?_, hupper⟩
  have hb1_le_L : b + 1 ≤ L := by
    have h1 : b + 1 ≤ 2 ^ b := Nat.lt_two_pow_self
    omega
  have hL_le_2b : L ≤ 2 ^ b := min_le_left _ _
  have hL_le_n1 : L ≤ n + 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hL_le_bg1 : L ≤ b + g + 1 := (min_le_right _ _).trans (min_le_right _ _)
  let e : ℕ := L - (b + 1)
  have he_le_g : e ≤ g := by omega
  have he_le_c : e ≤ c := by omega
  let key : Finset (Fin b) → ℕ := fun S => S.card * 2 ^ b + ∑ i ∈ S, 2 ^ i.val
  have hkey_inj : Function.Injective key := subset_key_inj b
  have hcard_fb : Fintype.card (Finset (Fin b)) = 2 ^ b := by simp
  let rk : Finset (Fin b) → ℕ := fun S => (Finset.univ.filter (fun T : Finset (Fin b) => key T < key S)).card
  have hrk_all := rank_bij_of_inj key hkey_inj
  have hrk_iff : ∀ x y : Finset (Fin b), key x < key y ↔ rk x < rk y := hrk_all.1
  have hrk_lt : ∀ x : Finset (Fin b), rk x < Fintype.card (Finset (Fin b)) := hrk_all.2.1
  have hrk_inj : Function.Injective rk := hrk_all.2.2.1
  have hrk_surj : ∀ m < Fintype.card (Finset (Fin b)), ∃ x : Finset (Fin b), rk x = m := hrk_all.2.2.2
  have hkey_mono : ∀ T S : Finset (Fin b), T.card < S.card → key T < key S := by
    intro T S hlt
    have hT_lt : (∑ i ∈ T, 2 ^ i.val) < 2 ^ b := by
      have hle : (∑ i ∈ T, 2 ^ i.val) ≤ ∑ i : Fin b, 2 ^ i.val :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ T)
      have htot := sum_two_pow_fin b
      omega
    have hmul : (T.card + 1) * 2 ^ b ≤ S.card * 2 ^ b := Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, one_mul] at hmul
    simp only [key]
    omega
  let D : Finset (Finset (Fin b)) := Finset.univ.filter (fun S => rk S < L)
  have hD_card : D.card = L := by
    have hbij : D.card = (Finset.range L).card := by
      refine Finset.card_bij (fun S _ => rk S)
        (fun S hS => Finset.mem_range.mpr (Finset.mem_filter.mp hS).2)
        (fun S1 _ S2 _ heq => hrk_inj heq)
        (fun m hm => ?_)
      rcases hrk_surj m (by rw [hcard_fb]; exact lt_of_lt_of_le (Finset.mem_range.mp hm) hL_le_2b) with ⟨S, hS⟩
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, by rw [hS]; exact Finset.mem_range.mp hm⟩, hS⟩
    rw [hbij, Finset.card_range]
  have hD_down : ∀ S ∈ D, ∀ T : Finset (Fin b), T ⊆ S → T ∈ D := by
    intro S hS T hTS
    by_cases heq : T = S
    · exact heq ▸ hS
    · have hlt : T.card < S.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, heq⟩)
      have hrk_lt' : rk T < rk S := (hrk_iff T S).mp (hkey_mono T S hlt)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ T, lt_trans hrk_lt' (Finset.mem_filter.mp hS).2⟩
  have hrk_emp : rk ∅ = 0 := by
    rw [Finset.card_eq_zero]
    ext T; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt]
    simp [key]
  have hrk_sing_lt : ∀ r : Fin b, 0 < rk {r} ∧ rk {r} < b + 1 := by
    intro r
    have hpos : 0 < rk {r} := by
      rw [← hrk_emp, ← hrk_iff]
      exact hkey_mono ∅ {r} (by simp)
    have hsub : Finset.univ.filter (fun T : Finset (Fin b) => key T < key {r}) ⊆
        insert ∅ (Finset.univ.image (fun j : Fin b => ({j} : Finset (Fin b)))) := by
      intro T hT
      have hlt := (Finset.mem_filter.mp hT).2
      have hcard_le : T.card ≤ 1 := by
        by_contra hgt
        have : 1 < T.card := by omega
        have h1 := hkey_mono {r} T (by simpa using this)
        omega
      by_cases h0 : T.card = 0
      · exact Finset.mem_insert_self ∅ _ |> fun hm => (Finset.card_eq_zero.mp h0).symm ▸ hm
      · have h1 : T.card = 1 := by omega
        rcases Finset.card_eq_one.mp h1 with ⟨j, rfl⟩
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    have hle : rk {r} ≤ b + 1 := by
      refine (Finset.card_le_card hsub).trans ?_
      refine (Finset.card_insert_le _ _).trans ?_
      have himg : (Finset.univ.image (fun j : Fin b => ({j} : Finset (Fin b)))).card ≤ b := by
        simpa using Finset.card_image_le (f := fun j : Fin b => ({j} : Finset (Fin b))) (s := Finset.univ)
      omega
    have hne : rk {r} ≠ b + 1 := by
      intro heq
      have hmem : {r} ∉ Finset.univ.filter (fun T : Finset (Fin b) => key T < key {r}) := by
        simp
      have hmem2 : {r} ∈ insert (∅ : Finset (Fin b)) (Finset.univ.image (fun j : Fin b => ({j} : Finset (Fin b)))) :=
        Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)
      have hlt_strict : rk {r} <
          (insert (∅ : Finset (Fin b)) (Finset.univ.image (fun j : Fin b => ({j} : Finset (Fin b))))).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hmem (h ▸ hmem2)⟩)
      have hle2 : (insert (∅ : Finset (Fin b)) (Finset.univ.image (fun j : Fin b => ({j} : Finset (Fin b))))).card ≤ b + 1 := by
        refine (Finset.card_insert_le _ _).trans ?_
        have himg : (Finset.univ.image (fun j : Fin b => ({j} : Finset (Fin b)))).card ≤ b := by
          simpa using Finset.card_image_le (f := fun j : Fin b => ({j} : Finset (Fin b))) (s := Finset.univ)
        omega
      omega
    exact ⟨hpos, by omega⟩
  have hge2_iff : ∀ S : Finset (Fin b), 2 ≤ S.card ↔ b + 1 ≤ rk S := by
    intro S
    constructor
    · intro h2
      have hsub : insert (∅ : Finset (Fin b)) (Finset.univ.image (fun j : Fin b => ({j} : Finset (Fin b)))) ⊆
          Finset.univ.filter (fun T : Finset (Fin b) => key T < key S) := by
        intro T hT
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ T, ?_⟩
        rcases Finset.mem_insert.mp hT with rfl | hmem
        · exact hkey_mono ∅ S (by rw [Finset.card_empty]; omega)
        · rcases Finset.mem_image.mp hmem with ⟨j, _, rfl⟩
          exact hkey_mono {j} S (by rw [Finset.card_singleton]; omega)
      have hcard_ins : (insert (∅ : Finset (Fin b))
          (Finset.univ.image (fun j : Fin b => ({j} : Finset (Fin b))))).card = b + 1 := by
        rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_image_of_injective _ (fun j1 j2 h => Finset.singleton_injective h),
            Finset.card_univ, Fintype.card_fin]
        · intro h
          rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
          exact Finset.singleton_ne_empty j hj
      exact hcard_ins ▸ Finset.card_le_card hsub
    · intro hrk_ge
      by_contra hlt2
      by_cases h0 : S.card = 0
      · rw [Finset.card_eq_zero.mp h0, hrk_emp] at hrk_ge; omega
      · have h1 : S.card = 1 := by omega
        rcases Finset.card_eq_one.mp h1 with ⟨r, rfl⟩
        have := (hrk_sing_lt r).2
        omega
  have hex_S : ∀ j : Fin e, ∃ S : Finset (Fin b), rk S = b + 1 + j.val :=
    fun j => hrk_surj (b + 1 + j.val) (by rw [hcard_fb]; omega)
  let Sof : Fin e → Finset (Fin b) := fun j => Classical.choose (hex_S j)
  have hSof_rk : ∀ j : Fin e, rk (Sof j) = b + 1 + j.val := fun j => Classical.choose_spec (hex_S j)
  have hSof_D : ∀ j : Fin e, Sof j ∈ D := fun j =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hSof_rk j]; omega⟩
  have hSof_ge2 : ∀ j : Fin e, 2 ≤ (Sof j).card := fun j =>
    (hge2_iff (Sof j)).mpr (by rw [hSof_rk j]; omega)
  have hSof_inj : Function.Injective Sof := fun j1 j2 heq => by
    have := congrArg rk heq
    rw [hSof_rk j1, hSof_rk j2] at this
    exact Fin.ext (by omega)
  let syn : W → Fin b → Bool := fun x r =>
    ((x ⟨r.val, by omega⟩ ::
      ((List.finRange e).filter (fun j => decide (r ∈ Sof j))).map
        (fun j => x ⟨b + j.val, by omega⟩)).foldr xor false)
  have hsyn_zmod : ∀ (x : W) (r : Fin b),
      b2z (syn x r) = b2z (x ⟨r.val, by omega⟩) +
        ∑ j ∈ Finset.univ.filter (fun j : Fin e => r ∈ Sof j), b2z (x ⟨b + j.val, by omega⟩) := by
    intro x r
    have hfold : ∀ l : List Bool, b2z (l.foldr xor false) = (l.map b2z).sum := by
      intro l
      induction l with
      | nil => simp [b2z]
      | cons a t ih => simp only [List.foldr_cons, b2z_xor, ih, List.map_cons, List.sum_cons]
    simp only [syn, hfold, List.map_cons, List.sum_cons, List.map_map]
    congr 1
  let synSet : W → Finset (Fin b) := fun x => Finset.univ.filter (fun r : Fin b => syn x r = true)
  have hstage1 : ∀ (k : ℕ) (hkb : k ≤ b),
      ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (synW : Fin k → ℕ),
        legalGates n gs ∧ gs.countP isPaid = 0 ∧
        (∀ r : Fin k, synW r < n + gs.length) ∧
        (∀ (r : Fin k) (x : W),
          (wiresOf gs (List.ofFn x)).getD (synW r) false = syn x ⟨r.val, by omega⟩) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], Fin.elim0, ⟨fun i => Fin.elim0 i, fun _ h => by cases h⟩, rfl,
        fun r => Fin.elim0 r, fun r => Fin.elim0 r⟩
    | succ k ih =>
      intro hkb
      rcases ih (by omega) with ⟨gs, synW, hleg, hcnt, hlt, heval⟩
      let r : Fin b := ⟨k, by omega⟩
      let inW : List ℕ := k :: ((List.finRange e).filter (fun j => decide (r ∈ Sof j))).map (fun j => b + j.val)
      have hinW_lt : ∀ w ∈ inW, w < n + gs.length := by
        intro w hw
        simp only [inW, List.mem_cons, List.mem_map, List.mem_filter] at hw
        rcases hw with rfl | ⟨j, _, rfl⟩ <;> omega
      rcases exists_xorList_wire n gs inW hleg hinW_lt with ⟨gs', out, hlen', hleg', hcnt', hout', hpref', hsum'⟩
      let synW' : Fin (k + 1) → ℕ := fun i =>
        if hi : i.val < k then synW ⟨i.val, hi⟩ else out
      refine ⟨gs', synW', hleg', by rw [hcnt', hcnt], ?_, ?_⟩
      · intro i
        by_cases hi : i.val < k
        · simp only [synW', dif_pos hi]
          have := hlt ⟨i.val, hi⟩; omega
        · simp only [synW', dif_neg hi]; exact hout'
      · intro i x
        by_cases hi : i.val < k
        · simp only [synW', dif_pos hi]
          rw [hpref' (synW ⟨i.val, hi⟩) (hlt ⟨i.val, hi⟩) x, heval ⟨i.val, hi⟩ x]
        · have hik : i.val = k := by omega
          simp only [synW', dif_neg hi]
          apply b2z_inj
          rw [hsum' x]
          have heq_r : (⟨i.val, by omega⟩ : Fin b) = r := Fin.ext hik
          rw [heq_r, hsyn_zmod x r]
          have hinput : ∀ (m : ℕ) (hm : m < n),
              (wiresOf gs (List.ofFn x)).getD m false = x ⟨m, hm⟩ := by
            intro m hm
            have h1 := wiresOf_append_prefix [] gs (List.ofFn x) m (by simp [hm])
            change (wiresOf gs (List.ofFn x)).getD m false = (List.ofFn x).getD m false at h1
            rw [h1]
            simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hm]
          simp only [inW, List.map_cons, List.sum_cons, List.map_map]
          rw [hinput k (by omega)]
          congr 1
          have hnodup : ((List.finRange e).filter (fun j => decide (r ∈ Sof j))).Nodup :=
            (List.nodup_finRange e).filter _
          have htoF : ((List.finRange e).filter (fun j => decide (r ∈ Sof j))).toFinset =
              Finset.univ.filter (fun j : Fin e => r ∈ Sof j) := by
            ext j; simp
          rw [← htoF, ← List.sum_toFinset _ hnodup]
          congr 1
          funext j
          dsimp only [Function.comp]
          rw [hinput (b + j.val) (by omega)]
  rcases hstage1 b le_rfl with ⟨gs1, synW, hleg1, hcnt1, hsyn_lt, hsyn_eval⟩
  let monB : Finset (Fin b) → W → Bool := fun S x => decide (S ⊆ synSet x)
  have hstage2 : ∀ (k : ℕ) (hke : k ≤ e),
      ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (monW : Fin k → ℕ),
        gs1.length ≤ gs.length ∧ legalGates n gs ∧ gs.countP isPaid = k ∧
        (∀ (r : Fin b) (x : W), (wiresOf gs (List.ofFn x)).getD (synW r) false = syn x r) ∧
        (∀ j : Fin k, monW j < n + gs.length) ∧
        (∀ (j : Fin k) (x : W),
          (wiresOf gs (List.ofFn x)).getD (monW j) false = monB (Sof ⟨j.val, by omega⟩) x) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨gs1, Fin.elim0, le_rfl, hleg1, hcnt1, fun r x => hsyn_eval r x,
        fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
    | succ k ih =>
      intro hke
      rcases ih (by omega) with ⟨gs, monW, hlen_gs, hleg_gs, hcnt_gs, hsyn_gs, hmon_lt, hmon_eval⟩
      let S : Finset (Fin b) := Sof ⟨k, by omega⟩
      have hS2 : 2 ≤ S.card := hSof_ge2 ⟨k, by omega⟩
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      let r0 : Fin b := Classical.choose hSne
      have hr0_mem : r0 ∈ S := Classical.choose_spec hSne
      let S' : Finset (Fin b) := S.erase r0
      have hS'_card : S'.card = S.card - 1 := Finset.card_erase_of_mem hr0_mem
      have hS'_rk_lt : rk S' < rk S := (hrk_iff S' S).mp (hkey_mono S' S (by omega))
      have hS'_prev : ∃ u : ℕ, u < n + gs.length ∧
          ∀ x : W, (wiresOf gs (List.ofFn x)).getD u false = monB S' x := by
        by_cases h1 : S'.card = 1
        · rcases Finset.card_eq_one.mp h1 with ⟨r1, hr1⟩
          refine ⟨synW r1, by have := hsyn_lt r1; omega, fun x => ?_⟩
          rw [hsyn_gs r1 x, hr1]
          simp only [monB, Finset.singleton_subset_iff, synSet, Finset.mem_filter, Finset.mem_univ, true_and]
          cases syn x r1 <;> rfl
        · have hge2 : 2 ≤ S'.card := by omega
          have hrk_ge : b + 1 ≤ rk S' := (hge2_iff S').mp hge2
          have hrk_S : rk S = b + 1 + k := hSof_rk ⟨k, by omega⟩
          let j' : Fin k := ⟨rk S' - (b + 1), by omega⟩
          have hSof_j' : Sof ⟨j'.val, by omega⟩ = S' := by
            apply hrk_inj
            rw [hSof_rk ⟨j'.val, by omega⟩]
            dsimp only [j']
            omega
          refine ⟨monW j', hmon_lt j', fun x => ?_⟩
          rw [hmon_eval j' x, hSof_j']
      rcases hS'_prev with ⟨u, hu_lt, hu_eval⟩
      have hres := appendAnd2_spec n gs u (synW r0) hleg_gs hu_lt (by have := hsyn_lt r0; omega)
      let gs' := (appendAnd2 n gs u (synW r0)).1
      let out := (appendAnd2 n gs u (synW r0)).2
      let monW' : Fin (k + 1) → ℕ := fun j => if hj : j.val < k then monW ⟨j.val, hj⟩ else out
      refine ⟨gs', monW', by simp [gs', appendAnd2]; omega, hres.1, by rw [hres.2.1, hcnt_gs], ?_, ?_, ?_⟩
      · intro r x
        rw [hres.2.2.2.1 (synW r) (by have := hsyn_lt r; omega) x, hsyn_gs r x]
      · intro j
        by_cases hj : j.val < k
        · simp only [monW', dif_pos hj]
          have := hmon_lt ⟨j.val, hj⟩
          simp [gs', appendAnd2]; omega
        · simp only [monW', dif_neg hj]; exact hres.2.2.1
      · intro j x
        by_cases hj : j.val < k
        · simp only [monW', dif_pos hj]
          rw [hres.2.2.2.1 (monW ⟨j.val, hj⟩) (hmon_lt ⟨j.val, hj⟩) x, hmon_eval ⟨j.val, hj⟩ x]
        · have hjk : j.val = k := by omega
          simp only [monW', dif_neg hj]
          rw [hres.2.2.2.2 x, hu_eval x, hsyn_gs r0 x]
          have hSeq : Sof ⟨j.val, by omega⟩ = S := by congr 1; exact Fin.ext hjk
          rw [hSeq]
          have hS_ins : S = insert r0 S' := (Finset.insert_erase hr0_mem).symm
          rw [hS_ins]
          simp only [monB, Finset.insert_subset_iff, synSet, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases h1 : S' ⊆ synSet x <;> cases h2 : syn x r0 <;> simp [h1, h2]
  rcases hstage2 e le_rfl with ⟨gs2, monW, hlen2, hleg2, hcnt2, hsyn2, hmon_lt, hmon_eval⟩
  have hstage3 : ∀ (k : ℕ) (hke : k ≤ e),
      ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (outW : Fin k → ℕ),
        gs2.length ≤ gs.length ∧ legalGates n gs ∧ gs.countP isPaid = e ∧
        (∀ (idx : Fin e) (x : W), (wiresOf gs (List.ofFn x)).getD (monW idx) false = monB (Sof idx) x) ∧
        (∀ j : Fin k, outW j < n + gs.length) ∧
        (∀ (j : Fin k) (x : W),
          b2z ((wiresOf gs (List.ofFn x)).getD (outW j) false) =
            b2z (x ⟨b + j.val, by omega⟩) +
              ∑ idx ∈ Finset.univ.filter (fun idx : Fin e => Sof ⟨j.val, by omega⟩ ⊆ Sof idx),
                b2z (monB (Sof idx) x)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨gs2, Fin.elim0, le_rfl, hleg2, hcnt2, hmon_eval, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
    | succ k ih =>
      intro hke
      rcases ih (by omega) with ⟨gs, outW, hlen_gs, hleg_gs, hcnt_gs, hmon_gs, hout_lt, hout_eval⟩
      let S : Finset (Fin b) := Sof ⟨k, by omega⟩
      let supIdxs : List (Fin e) := (List.finRange e).filter (fun idx => decide (S ⊆ Sof idx))
      let inW : List ℕ := (b + k) :: supIdxs.map monW
      have hinW_lt : ∀ w ∈ inW, w < n + gs.length := by
        intro w hw
        simp only [inW, List.mem_cons, List.mem_map] at hw
        rcases hw with rfl | ⟨idx, _, rfl⟩
        · omega
        · have := hmon_lt idx; omega
      rcases exists_xorList_wire n gs inW hleg_gs hinW_lt with ⟨gs', out, hlen', hleg', hcnt', hout', hpref', hsum'⟩
      let outW' : Fin (k + 1) → ℕ := fun j => if hj : j.val < k then outW ⟨j.val, hj⟩ else out
      refine ⟨gs', outW', by omega, hleg', by rw [hcnt', hcnt_gs], ?_, ?_, ?_⟩
      · intro idx x
        rw [hpref' (monW idx) (by have := hmon_lt idx; omega) x, hmon_gs idx x]
      · intro j
        by_cases hj : j.val < k
        · simp only [outW', dif_pos hj]
          have := hout_lt ⟨j.val, hj⟩; omega
        · simp only [outW', dif_neg hj]; exact hout'
      · intro j x
        by_cases hj : j.val < k
        · simp only [outW', dif_pos hj]
          rw [hpref' (outW ⟨j.val, hj⟩) (hout_lt ⟨j.val, hj⟩) x, hout_eval ⟨j.val, hj⟩ x]
        · have hjk : j.val = k := by omega
          simp only [outW', dif_neg hj]
          rw [hsum' x]
          have hinput : (wiresOf gs (List.ofFn x)).getD (b + k) false = x ⟨b + k, by omega⟩ := by
            have h1 := wiresOf_append_prefix [] gs (List.ofFn x) (b + k) (by simp; omega)
            change (wiresOf gs (List.ofFn x)).getD (b + k) false = (List.ofFn x).getD (b + k) false at h1
            rw [h1]
            simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, show b + k < n by omega]
          simp only [inW, List.map_cons, List.sum_cons, List.map_map]
          have hbk_eq : (⟨b + j.val, by omega⟩ : Fin n) = ⟨b + k, by omega⟩ := Fin.ext (by dsimp only; omega)
          have hSj_eq : Sof ⟨j.val, by omega⟩ = S := by congr 1; exact Fin.ext hjk
          rw [hbk_eq, hSj_eq, hinput]
          congr 1
          have hnodup : supIdxs.Nodup := (List.nodup_finRange e).filter _
          have htoF : supIdxs.toFinset = Finset.univ.filter (fun idx : Fin e => S ⊆ Sof idx) := by
            ext idx; simp [supIdxs]
          rw [← htoF, ← List.sum_toFinset _ hnodup]
          congr 1
          funext idx
          dsimp only [Function.comp]
          rw [hmon_gs idx x]
  rcases hstage3 e le_rfl with ⟨gs3, outW, hlen3, hleg3, hcnt3, _, hout3_lt, hout3_eval⟩
  let C : Circ := ⟨gs3, 0⟩
  let tap : Fin c → ℕ := fun j => if hj : j.val < e then outW ⟨j.val, hj⟩ else b + j.val
  let code : Msg → W := fun m i =>
    if hi : i.val < b then
      (((List.finRange e).filter (fun j => decide ((⟨i.val, hi⟩ : Fin b) ∈ Sof j))).map
        (fun j => m ⟨j.val, by omega⟩)).foldr xor false
    else
      m ⟨i.val - b, by omega⟩
  have hcode_zmod : ∀ (m : Msg) (r : Fin b),
      b2z (code m ⟨r.val, by omega⟩) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin e => r ∈ Sof j), b2z (m ⟨j.val, by omega⟩) := by
    intro m r
    have hfold : ∀ l : List Bool, b2z (l.foldr xor false) = (l.map b2z).sum := by
      intro l
      induction l with
      | nil => simp [b2z]
      | cons a t ih => simp only [List.foldr_cons, b2z_xor, ih, List.map_cons, List.sum_cons]
    simp only [code, dif_pos r.isLt, hfold, List.map_map]
    have hnodup : ((List.finRange e).filter (fun j => decide (r ∈ Sof j))).Nodup :=
      (List.nodup_finRange e).filter _
    have htoF : ((List.finRange e).filter (fun j => decide (r ∈ Sof j))).toFinset =
        Finset.univ.filter (fun j : Fin e => r ∈ Sof j) := by
      ext j; simp
    rw [← htoF, ← List.sum_toFinset _ hnodup]
    rfl
  have hC_leg : legal C := hleg3
  have hC_cost : cost C ≤ g := by change gs3.countP isPaid ≤ g; omega
  have hC_tap : ∀ j : Fin c, tap j < n + C.gates.length := by
    intro j
    by_cases hj : j.val < e
    · simp only [tap, dif_pos hj]; exact hout3_lt ⟨j.val, hj⟩
    · simp only [tap, dif_neg hj]; omega
  have hhits_le : hits C tap code ≤ 2 ^ c * L :=
    hupper _ ⟨C, tap, code, hC_leg, hC_cost, hC_tap, rfl⟩
  let sendC : W → Msg := fun x j => (C.wires (List.ofFn x)).getD (tap j) false
  have hsend_good : ∀ (x : W), synSet x ∈ D → ∀ j : Fin c,
      b2z (sendC x j) =
        b2z (x ⟨b + j.val, by omega⟩) +
          if hj : j.val < e then (if synSet x = Sof ⟨j.val, hj⟩ then 1 else 0) else 0 := by
    intro x hxD j
    by_cases hj : j.val < e
    · simp only [sendC, tap, dif_pos hj, PEqualNP.CircuitLowerBounds.Circuit.wires]
      change b2z ((wiresOf gs3 (List.ofFn x)).getD (outW ⟨j.val, hj⟩) false) = _
      rw [hout3_eval ⟨j.val, hj⟩ x]
      congr 1
      have hsum_D : ∑ idx ∈ Finset.univ.filter (fun idx : Fin e => Sof ⟨j.val, hj⟩ ⊆ Sof idx),
          b2z (monB (Sof idx) x) =
          ∑ T ∈ D.filter (fun T => Sof ⟨j.val, hj⟩ ⊆ T), if T ⊆ synSet x then (1 : ZMod 2) else 0 := by
        refine Finset.sum_bij (fun idx _ => Sof idx)
          (fun idx hidx => Finset.mem_filter.mpr ⟨hSof_D idx, (Finset.mem_filter.mp hidx).2⟩)
          (fun i1 _ i2 _ heq => hSof_inj heq)
          (fun T hT => ?_)
          (fun idx _ => by simp only [monB]; by_cases h : Sof idx ⊆ synSet x <;> simp [h, b2z])
        rcases Finset.mem_filter.mp hT with ⟨hTD, hsub⟩
        have hT2 : 2 ≤ T.card := (hSof_ge2 ⟨j.val, hj⟩).trans (Finset.card_le_card hsub)
        have hrk_ge : b + 1 ≤ rk T := (hge2_iff T).mp hT2
        have hrk_lt' : rk T < L := (Finset.mem_filter.mp hTD).2
        let idx : Fin e := ⟨rk T - (b + 1), by omega⟩
        have hSof_idx : Sof idx = T := by
          apply hrk_inj
          rw [hSof_rk idx]; dsimp only [idx]; omega
        exact ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_univ idx, hSof_idx.symm ▸ hsub⟩, hSof_idx⟩
      rw [hsum_D]
      exact mobius_downset_zmod2 D hD_down (Sof ⟨j.val, hj⟩) (synSet x) (hSof_D ⟨j.val, hj⟩) hxD
    · simp only [sendC, tap, dif_neg hj, add_zero, PEqualNP.CircuitLowerBounds.Circuit.wires]
      change b2z ((wiresOf gs3 (List.ofFn x)).getD (b + j.val) false) = _
      have h1 := wiresOf_append_prefix [] gs3 (List.ofFn x) (b + j.val) (by simp; omega)
      change (wiresOf gs3 (List.ofFn x)).getD (b + j.val) false = (List.ofFn x).getD (b + j.val) false at h1
      rw [h1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, show b + j.val < n by omega]
  let mkWord : Msg × {S : Finset (Fin b) // S ∈ D} → W := fun p i =>
    let m := p.1
    let S := p.2.1
    if S = ∅ then code m i
    else if h1 : S.card = 1 then
      if hi : i.val < b then
        if (⟨i.val, hi⟩ : Fin b) ∈ S then !(code m i) else code m i
      else code m i
    else
      if i.val = b + (rk S - (b + 1)) then !(code m i) else code m i
  have hmk_syn : ∀ (m : Msg) (S : {S : Finset (Fin b) // S ∈ D}), synSet (mkWord (m, S)) = S.1 := by
    intro m ⟨S, hSD⟩
    ext r
    simp only [synSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hiff : syn (mkWord (m, ⟨S, hSD⟩)) r = true ↔ b2z (syn (mkWord (m, ⟨S, hSD⟩)) r) = 1 := by
      cases syn (mkWord (m, ⟨S, hSD⟩)) r <;> decide
    rw [hiff, hsyn_zmod]
    by_cases h0 : S = ∅
    · subst h0
      have hval : ∀ i : Fin n, mkWord (m, ⟨∅, hSD⟩) i = code m i := fun i => by simp [mkWord]
      simp_rw [hval, hcode_zmod m r]
      have hsuf : ∀ j : Fin e, code m ⟨b + j.val, by omega⟩ = m ⟨j.val, by omega⟩ := fun j => by
        simp only [code, dif_neg (by omega : ¬ b + j.val < b)]
        congr 1; exact Fin.ext (by dsimp only; omega)
      simp_rw [hsuf, zmod2_add_self]
      simp
    · by_cases h1 : S.card = 1
      · have hsuf : ∀ j : Fin e, mkWord (m, ⟨S, hSD⟩) ⟨b + j.val, by omega⟩ = m ⟨j.val, by omega⟩ := fun j => by
          simp only [mkWord, if_neg h0, dif_pos h1, dif_neg (by omega : ¬ b + j.val < b), code]
          congr 1; exact Fin.ext (by dsimp only; omega)
        simp_rw [hsuf]
        have hpref : b2z (mkWord (m, ⟨S, hSD⟩) ⟨r.val, by omega⟩) =
            b2z (code m ⟨r.val, by omega⟩) + (if r ∈ S then 1 else 0) := by
          simp only [mkWord, if_neg h0, dif_pos h1, dif_pos r.isLt]
          by_cases hr : r ∈ S
          · rw [if_pos hr, if_pos hr, b2z_not, add_comm]
          · rw [if_neg hr, if_neg hr, add_zero]
        rw [hpref, hcode_zmod m r]
        have hcancel : (∑ j ∈ Finset.univ.filter (fun j : Fin e => r ∈ Sof j), b2z (m ⟨j.val, by omega⟩)) +
            (if r ∈ S then (1 : ZMod 2) else 0) +
            (∑ j ∈ Finset.univ.filter (fun j : Fin e => r ∈ Sof j), b2z (m ⟨j.val, by omega⟩)) =
            if r ∈ S then 1 else 0 := by
          rw [add_right_comm, zmod2_add_self, zero_add]
        rw [hcancel]
        by_cases hr : r ∈ S <;> simp [hr]
      · have hS2 : 2 ≤ S.card := by
          have : S.card ≠ 0 := fun hz => h0 (Finset.card_eq_zero.mp hz)
          omega
        have hrk_ge : b + 1 ≤ rk S := (hge2_iff S).mp hS2
        have hrk_lt' : rk S < L := (Finset.mem_filter.mp hSD).2
        let j0 : Fin e := ⟨rk S - (b + 1), by omega⟩
        have hSof_j0 : Sof j0 = S := by
          apply hrk_inj; rw [hSof_rk j0]; dsimp only [j0]; omega
        have hpref : mkWord (m, ⟨S, hSD⟩) ⟨r.val, by omega⟩ = code m ⟨r.val, by omega⟩ := by
          simp only [mkWord, if_neg h0, dif_neg h1]
          rw [if_neg (by omega : ¬ r.val = b + (rk S - (b + 1)))]
        have hsuf : ∀ j : Fin e, b2z (mkWord (m, ⟨S, hSD⟩) ⟨b + j.val, by omega⟩) =
            b2z (m ⟨j.val, by omega⟩) + if j = j0 then 1 else 0 := by
          intro j
          simp only [mkWord, if_neg h0, dif_neg h1]
          have hcode_j : code m ⟨b + j.val, by omega⟩ = m ⟨j.val, by omega⟩ := by
            simp only [code, dif_neg (by omega : ¬ b + j.val < b)]
            congr 1; exact Fin.ext (by dsimp only; omega)
          by_cases hjj : j = j0
          · subst hjj
            rw [if_pos rfl, if_pos rfl, hcode_j, b2z_not, add_comm]
          · have hne_val : ¬ b + j.val = b + (rk S - (b + 1)) := fun heq => hjj (Fin.ext (by dsimp only [j0]; omega))
            rw [if_neg hne_val, if_neg hjj, hcode_j, add_zero]
        rw [hpref, hcode_zmod m r]
        simp_rw [hsuf, Finset.sum_add_distrib]
        have hcancel : (∑ j ∈ Finset.univ.filter (fun j : Fin e => r ∈ Sof j), b2z (m ⟨j.val, by omega⟩)) +
            ((∑ j ∈ Finset.univ.filter (fun j : Fin e => r ∈ Sof j), b2z (m ⟨j.val, by omega⟩)) +
              ∑ j ∈ Finset.univ.filter (fun j : Fin e => r ∈ Sof j), if j = j0 then (1 : ZMod 2) else 0) =
            ∑ j ∈ Finset.univ.filter (fun j : Fin e => r ∈ Sof j), if j = j0 then (1 : ZMod 2) else 0 := by
          rw [← add_assoc, zmod2_add_self, zero_add]
        rw [hcancel]
        by_cases hr : r ∈ S
        · have hj0_mem : j0 ∈ Finset.univ.filter (fun j : Fin e => r ∈ Sof j) := by
            simp [hSof_j0, hr]
          rw [Finset.sum_eq_single j0]
          · simp [hr]
          · intro j _ hne; simp [hne]
          · intro h; exact (h hj0_mem).elim
        · have hzero : ∑ j ∈ Finset.univ.filter (fun j : Fin e => r ∈ Sof j),
              (if j = j0 then (1 : ZMod 2) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            have hne : j ≠ j0 := fun heq => hr (hSof_j0 ▸ heq ▸ (Finset.mem_filter.mp hj).2)
            simp [hne]
          rw [hzero]; simp [hr]
  have hmk_send : ∀ (m : Msg) (S : {S : Finset (Fin b) // S ∈ D}), sendC (mkWord (m, S)) = m := by
    intro m ⟨S, hSD⟩
    funext j
    apply b2z_inj
    have hsyn_eq := hmk_syn m ⟨S, hSD⟩
    rw [hsend_good _ (hsyn_eq.symm ▸ hSD) j, hsyn_eq]
    by_cases h0 : S = ∅
    · subst h0
      have hval : mkWord (m, ⟨∅, hSD⟩) ⟨b + j.val, by omega⟩ = m j := by
        simp only [mkWord, ↓reduceIte, code, dif_neg (by omega : ¬ b + j.val < b)]
        congr 1; exact Fin.ext (by dsimp only; omega)
      rw [hval]
      by_cases hj : j.val < e
      · rw [dif_pos hj, if_neg (fun heq => by have := hSof_ge2 ⟨j.val, hj⟩; rw [← heq] at this; simp at this), add_zero]
      · rw [dif_neg hj, add_zero]
    · by_cases h1 : S.card = 1
      · have hval : mkWord (m, ⟨S, hSD⟩) ⟨b + j.val, by omega⟩ = m j := by
          simp only [mkWord, if_neg h0, dif_pos h1, dif_neg (by omega : ¬ b + j.val < b), code]
          congr 1; exact Fin.ext (by dsimp only; omega)
        rw [hval]
        by_cases hj : j.val < e
        · rw [dif_pos hj, if_neg (fun heq => by have := hSof_ge2 ⟨j.val, hj⟩; rw [← heq] at this; dsimp only at this; omega), add_zero]
        · rw [dif_neg hj, add_zero]
      · have hS2 : 2 ≤ S.card := by
          have : S.card ≠ 0 := fun hz => h0 (Finset.card_eq_zero.mp hz)
          omega
        have hrk_ge : b + 1 ≤ rk S := (hge2_iff S).mp hS2
        have hrk_lt' : rk S < L := (Finset.mem_filter.mp hSD).2
        have hcode_j : code m ⟨b + j.val, by omega⟩ = m j := by
          simp only [code, dif_neg (by omega : ¬ b + j.val < b)]
          congr 1; exact Fin.ext (by dsimp only; omega)
        by_cases hj : j.val < e
        · rw [dif_pos hj]
          have hiff_j : (b + j.val = b + (rk S - (b + 1))) ↔ S = Sof ⟨j.val, hj⟩ := by
            constructor
            · intro heq
              apply hrk_inj
              rw [hSof_rk ⟨j.val, hj⟩]
              dsimp only; omega
            · intro heq
              rw [heq, hSof_rk ⟨j.val, hj⟩]
              dsimp only; omega
          simp only [mkWord, if_neg h0, dif_neg h1]
          by_cases heq : S = Sof ⟨j.val, hj⟩
          · rw [if_pos (hiff_j.mpr heq), if_pos heq, hcode_j, b2z_not]
            rw [add_comm (1 : ZMod 2), add_assoc, zmod2_add_self, add_zero]
          · rw [if_neg (fun h => heq (hiff_j.mp h)), if_neg heq, hcode_j, add_zero]
        · rw [dif_neg hj, add_zero]
          simp only [mkWord, if_neg h0, dif_neg h1]
          rw [if_neg (by omega : ¬ b + j.val = b + (rk S - (b + 1))), hcode_j]
  have hmk_dist : ∀ (m : Msg) (S : {S : Finset (Fin b) // S ∈ D}),
      (Finset.univ.filter (fun i : Fin n => mkWord (m, S) i != code m i)).card ≤ 1 := by
    intro m ⟨S, hSD⟩
    by_cases h0 : S = ∅
    · subst h0
      have hemp : Finset.univ.filter (fun i : Fin n => mkWord (m, ⟨∅, hSD⟩) i != code m i) = ∅ := by
        ext i; simp [mkWord]
      rw [hemp, Finset.card_empty]; omega
    · by_cases h1 : S.card = 1
      · rcases Finset.card_eq_one.mp h1 with ⟨r0, hr0⟩
        have hsub : Finset.univ.filter (fun i : Fin n => mkWord (m, ⟨S, hSD⟩) i != code m i) ⊆
            {⟨r0.val, by omega⟩} := by
          intro i hi
          have hne : mkWord (m, ⟨S, hSD⟩) i ≠ code m i := by simpa using (Finset.mem_filter.mp hi).2
          simp only [mkWord, if_neg h0, dif_pos h1] at hne
          by_cases hib : i.val < b
          · rw [dif_pos hib] at hne
            by_cases hmem : (⟨i.val, hib⟩ : Fin b) ∈ S
            · rw [hr0, Finset.mem_singleton] at hmem
              exact Finset.mem_singleton.mpr (Fin.ext (congrArg (fun t : Fin b => t.val) hmem))
            · rw [if_neg hmem] at hne; exact (hne rfl).elim
          · rw [dif_neg hib] at hne; exact (hne rfl).elim
        exact (Finset.card_le_card hsub).trans (by simp)
      · have hS2 : 2 ≤ S.card := by
          have : S.card ≠ 0 := fun hz => h0 (Finset.card_eq_zero.mp hz)
          omega
        have hrk_ge : b + 1 ≤ rk S := (hge2_iff S).mp hS2
        have hrk_lt' : rk S < L := (Finset.mem_filter.mp hSD).2
        have hsub : Finset.univ.filter (fun i : Fin n => mkWord (m, ⟨S, hSD⟩) i != code m i) ⊆
            {⟨b + (rk S - (b + 1)), by omega⟩} := by
          intro i hi
          have hne : mkWord (m, ⟨S, hSD⟩) i ≠ code m i := by simpa using (Finset.mem_filter.mp hi).2
          simp only [mkWord, if_neg h0, dif_neg h1] at hne
          by_cases hieq : i.val = b + (rk S - (b + 1))
          · exact Finset.mem_singleton.mpr (Fin.ext hieq)
          · rw [if_neg hieq] at hne; exact (hne rfl).elim
        exact (Finset.card_le_card hsub).trans (by simp)
  have hmk_inj : Function.Injective mkWord := by
    rintro ⟨m1, S1⟩ ⟨m2, S2⟩ heq
    have hm : m1 = m2 := by
      rw [← hmk_send m1 S1, ← hmk_send m2 S2, heq]
    have hS : S1 = S2 := by
      apply Subtype.ext
      rw [← hmk_syn m1 S1, ← hmk_syn m2 S2, heq]
    rw [hm, hS]
  have hhits_ge : 2 ^ c * L ≤ hits C tap code := by
    have hcard_dom : Fintype.card (Msg × {S : Finset (Fin b) // S ∈ D}) = 2 ^ c * L := by
      rw [Fintype.card_prod, Fintype.card_coe, hD_card]
      simp [Msg]
    rw [← hcard_dom, ← Finset.card_univ]
    refine Finset.card_le_card_of_injOn mkWord (fun p _ => ?_) (fun p1 _ p2 _ h => hmk_inj h)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hs : (fun j : Fin c => (C.wires (List.ofFn (mkWord p))).getD (tap j) false) = p.1 :=
      hmk_send p.1 p.2
    dsimp only
    rw [hs]
    exact hmk_dist p.1 p.2
  have hhits_eq : hits C tap code = 2 ^ c * L := le_antisymm hhits_le hhits_ge
  exact ⟨C, tap, code, hC_leg, hC_cost, hC_tap, hhits_eq⟩

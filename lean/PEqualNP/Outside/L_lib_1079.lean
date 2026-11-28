import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1079_aux

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hlt : x.val < 2 := ZMod.val_lt x
  have hval : (x.val : ZMod 2) = x := ZMod.natCast_zmod_val x
  interval_cases hv : x.val
  · left
    rw [← hval]
    rfl
  · right
    rw [← hval]
    rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma vec_add_self {k : ℕ} (v : Fin k → ZMod 2) : v + v = 0 := by
  ext i
  exact zmod2_add_self (v i)

private lemma vec_add_cancel_right {k : ℕ} (u v : Fin k → ZMod 2) : u + v + v = u := by
  rw [add_assoc, vec_add_self, add_zero]

private lemma vec_add_eq_zero_iff {k : ℕ} {u v : Fin k → ZMod 2} : u + v = 0 ↔ u = v := by
  constructor
  · intro h
    have h1 := congrArg (fun w => w + v) h
    rw [vec_add_cancel_right, zero_add] at h1
    exact h1
  · rintro rfl
    exact vec_add_self u

private lemma part1 (k m : ℕ) (σ : Equiv.Perm (Fin k))
    (F : (Fin k → ZMod 2) → (Fin m → ZMod 2)) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let W := Fin k → ZMod 2
    let R := fun (x : W) (i : Fin k) => x (σ i)
    let edge := fun a b : Fin k => σ a = b
    let N := fun (x : W) (i : Fin k) =>
      (Finset.univ.filter (fun j : Fin k => Relation.EqvGen edge i j)).sum x
    let period := fun v : W => ∀ x : W, F (x + v) = F x
    let trans := fun h : W => ∀ x : W, F (R x + h) = F x
    let good := fun g : W => ∀ x : W, F (R x + g) = F (x + g)
    (∀ g : W, good g ↔ trans (g + R g)) ∧
    (∀ h : W, trans h → ((∃ g : W, good g) ↔ ∃ v : W, period v ∧ N v = N h)) ∧
    Nat.card {g : W // good g} =
      2 ^ (Nat.card (Quot edge)) * Nat.card {h : W // trans h ∧ N h = 0} := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let R : (Fin k → ZMod 2) → (Fin k → ZMod 2) := fun x i => x (σ i)
  let edge := fun a b : Fin k => σ a = b
  let N : (Fin k → ZMod 2) → (Fin k → ZMod 2) := fun x i =>
    (Finset.univ.filter (fun j : Fin k => Relation.EqvGen edge i j)).sum x
  let period := fun v : Fin k → ZMod 2 => ∀ x : Fin k → ZMod 2, F (x + v) = F x
  let trans := fun h : Fin k → ZMod 2 => ∀ x : Fin k → ZMod 2, F (R x + h) = F x
  let good := fun g : Fin k → ZMod 2 => ∀ x : Fin k → ZMod 2, F (R x + g) = F (x + g)
  have hR_add : ∀ x y : Fin k → ZMod 2, R (x + y) = R x + R y := fun _ _ => rfl
  have hR_surj : Function.Surjective R := by
    intro y
    refine ⟨fun i => y (σ.symm i), ?_⟩
    ext i
    simp [R]
  have hgood_iff : ∀ g : Fin k → ZMod 2, good g ↔ trans (g + R g) := by
    intro g
    constructor
    · intro hg x
      have hx := hg (x + g)
      have h1 : R (x + g) + g = R x + (g + R g) := by
        rw [hR_add, add_assoc, add_comm (R g) g]
      rw [h1, vec_add_cancel_right] at hx
      exact hx
    · intro ht x
      have hx := ht (x + g)
      have h1 : R (x + g) + (g + R g) = R x + g := by
        rw [hR_add]
        ext i
        simp only [Pi.add_apply]
        have := zmod2_add_self (R g i)
        calc
          R x i + R g i + (g i + R g i) = R x i + g i + (R g i + R g i) := by ring
          _ = R x i + g i + 0 := by rw [this]
          _ = R x i + g i := add_zero _
      rw [h1] at hx
      exact hx
  let φ : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    { toFun := fun g => g + R g
      map_add' := fun g₁ g₂ => by
        ext i
        simp only [R, Pi.add_apply]
        ring
      map_smul' := fun c g => by
        ext i
        simp only [R, Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hN_add : ∀ x y : Fin k → ZMod 2, N (x + y) = N x + N y := by
    intro x y
    ext i
    simp only [N, Pi.add_apply, Finset.sum_add_distrib]
  have hN_eqv : ∀ (x : Fin k → ZMod 2) {a b : Fin k}, Relation.EqvGen edge a b → N x a = N x b := by
    intro x a b hab
    simp only [N]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun haj => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hab) haj,
      fun hbj => Relation.EqvGen.trans _ _ _ hab hbj⟩
  let Nlin : (Fin k → ZMod 2) →ₗ[ZMod 2] (Quot edge → ZMod 2) :=
    { toFun := fun x => Quot.lift (N x) (fun a b hab => hN_eqv x (Relation.EqvGen.rel a b hab))
      map_add' := fun x y => by
        funext q
        induction q using Quot.ind with
        | _ i => exact congrFun (hN_add x y) i
      map_smul' := fun c x => by
        funext q
        induction q using Quot.ind with
        | _ i =>
          change N (c • x) i = c * N x i
          simp only [N, Pi.smul_apply, smul_eq_mul, Finset.mul_sum] }
  have hker_phi_equiv : LinearMap.ker φ ≃ₗ[ZMod 2] (Quot edge → ZMod 2) :=
    { toFun := fun g => Quot.lift g.1 (fun a b hab => by
        have h0 : g.1 + R g.1 = 0 := g.2
        have hga : g.1 a = g.1 (σ a) := congrFun (vec_add_eq_zero_iff.mp h0) a
        rw [← hab]
        exact hga)
      map_add' := fun g₁ g₂ => by
        funext q
        induction q using Quot.ind with
        | _ i => rfl
      map_smul' := fun c g => by
        funext q
        induction q using Quot.ind with
        | _ i => rfl
      invFun := fun f => ⟨fun i => f (Quot.mk edge i), by
        change (fun i => f (Quot.mk edge i)) + R (fun i => f (Quot.mk edge i)) = 0
        rw [vec_add_eq_zero_iff]
        ext i
        exact congrArg f (Quot.sound (show edge i (σ i) from rfl))⟩
      left_inv := fun g => by
        ext i
        rfl
      right_inv := fun f => by
        funext q
        induction q using Quot.ind with
        | _ i => rfl }
  have hNlin_surj : Function.Surjective Nlin := by
    intro f
    choose rep hrep using fun q : Quot edge => Quot.exists_rep q
    refine ⟨fun i => if i = rep (Quot.mk edge i) then f (Quot.mk edge i) else 0, ?_⟩
    funext q
    induction q using Quot.ind with
    | _ i =>
      change N (fun j => if j = rep (Quot.mk edge j) then f (Quot.mk edge j) else 0) i = f (Quot.mk edge i)
      simp only [N]
      have hmem : rep (Quot.mk edge i) ∈ Finset.univ.filter (fun j : Fin k => Relation.EqvGen edge i j) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        exact Quot.eq.mp (hrep (Quot.mk edge i)).symm
      rw [Finset.sum_eq_single (rep (Quot.mk edge i))]
      · rw [hrep (Quot.mk edge i)]
        simp
      · intro j hj hne
        rw [Finset.mem_filter] at hj
        have hq : Quot.mk edge j = Quot.mk edge i := (Quot.eq.mpr hj.2).symm
        rw [hq]
        simp [hne]
      · intro hnot
        exact (hnot hmem).elim
  have hrange_le : LinearMap.range φ ≤ LinearMap.ker Nlin := by
    rintro _ ⟨g, rfl⟩
    rw [LinearMap.mem_ker]
    funext q
    induction q using Quot.ind with
    | _ i =>
      change N (g + R g) i = 0
      simp only [N, Pi.add_apply, Finset.sum_add_distrib]
      have hperm : (Finset.univ.filter (fun j : Fin k => Relation.EqvGen edge i j)).sum (R g) =
          (Finset.univ.filter (fun j : Fin k => Relation.EqvGen edge i j)).sum g := by
        refine Finset.sum_bij (fun j _ => σ j) ?_ ?_ ?_ ?_
        · intro j hj
          rw [Finset.mem_filter] at hj ⊢
          exact ⟨Finset.mem_univ _, Relation.EqvGen.trans _ _ _ hj.2 (Relation.EqvGen.rel j (σ j) rfl)⟩
        · intro j₁ _ j₂ _ h
          exact σ.injective h
        · intro j hj
          rw [Finset.mem_filter] at hj
          refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, Relation.EqvGen.trans _ _ _ hj.2
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel (σ.symm j) j (σ.apply_symm_apply j)))⟩
        · intro j _
          rfl
      rw [hperm]
      exact zmod2_add_self _
  have hrange_eq : LinearMap.range φ = LinearMap.ker Nlin := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 := LinearMap.finrank_range_add_finrank_ker Nlin
    have htop : LinearMap.range Nlin = ⊤ := LinearMap.range_eq_top.mpr hNlin_surj
    have hfin_ker : Module.finrank (ZMod 2) (LinearMap.ker φ) =
        Module.finrank (ZMod 2) (LinearMap.range Nlin) := by
      rw [htop, finrank_top]
      exact LinearEquiv.finrank_eq hker_phi_equiv
    have hfin_eq : Module.finrank (ZMod 2) (LinearMap.range φ) =
        Module.finrank (ZMod 2) (LinearMap.ker Nlin) := by
      rw [← hfin_ker, add_comm] at h2
      exact Nat.add_right_cancel (h1.trans h2.symm)
    exact Submodule.eq_of_le_of_finrank_eq hrange_le hfin_eq
  have hmem_range : ∀ h : Fin k → ZMod 2, h ∈ LinearMap.range φ ↔ N h = 0 := by
    intro h
    rw [hrange_eq, LinearMap.mem_ker]
    constructor
    · intro h0
      ext i
      exact congrFun h0 (Quot.mk edge i)
    · intro h0
      funext q
      induction q using Quot.ind with
      | _ i => exact congrFun h0 i
  have htrans_iff : ∀ h h' : Fin k → ZMod 2, trans h → (trans h' ↔ period (h + h')) := by
    intro h h' hh
    constructor
    · intro hh' y
      rcases hR_surj (y + h) with ⟨x, hx⟩
      have hRx : R x + h = y := by
        rw [hx, vec_add_cancel_right]
      have h1 : y + (h + h') = R x + h' := by
        rw [← hRx, add_assoc]
        ext i
        simp only [Pi.add_apply]
        have := zmod2_add_self (h i)
        calc
          R x i + (h i + (h i + h' i)) = R x i + h' i + (h i + h i) := by ring
          _ = R x i + h' i + 0 := by rw [this]
          _ = R x i + h' i := add_zero _
      rw [h1, hh' x, ← hh x, hRx]
    · intro hp x
      have h1 : R x + h' = (R x + h) + (h + h') := by
        ext i
        simp only [Pi.add_apply]
        have := zmod2_add_self (h i)
        calc
          R x i + h' i = R x i + h' i + 0 := (add_zero _).symm
          _ = R x i + h' i + (h i + h i) := by rw [this]
          _ = R x i + h i + (h i + h' i) := by ring
      rw [h1, hp (R x + h), hh x]
  refine ⟨hgood_iff, ?_, ?_⟩
  · intro h hh
    constructor
    · rintro ⟨g, hg⟩
      have htg : trans (φ g) := (hgood_iff g).mp hg
      have hNg : N (φ g) = 0 := (hmem_range (φ g)).mp (LinearMap.mem_range_self φ g)
      refine ⟨h + φ g, (htrans_iff h (φ g) hh).mp htg, ?_⟩
      change N (h + φ g) = N h
      rw [hN_add, hNg, add_zero]
    · rintro ⟨v, hpv, hNv⟩
      have hNv' : N v = N h := hNv
      have hNhv : N (h + v) = 0 := by
        rw [hN_add, hNv', vec_add_self]
      rcases (hmem_range (h + v)).mpr hNhv with ⟨g, hg⟩
      refine ⟨g, (hgood_iff g).mpr ?_⟩
      change trans (φ g)
      rw [hg, htrans_iff h (h + v) hh]
      have h1 : h + (h + v) = v := by
        rw [← add_assoc, vec_add_self, zero_add]
      rw [h1]
      exact hpv
  · change Nat.card {g : Fin k → ZMod 2 // good g} =
      2 ^ Nat.card (Quot edge) * Nat.card {h : Fin k → ZMod 2 // trans h ∧ N h = 0}
    haveI : Fintype (Quot edge) := Fintype.ofFinite (Quot edge)
    have hcard_ker : (Finset.univ.filter (fun g : Fin k → ZMod 2 => φ g = 0)).card =
        2 ^ Nat.card (Quot edge) := by
      have h1 : (Finset.univ.filter (fun g : Fin k → ZMod 2 => φ g = 0)).card =
          Fintype.card (LinearMap.ker φ) := by
        rw [Fintype.card_subtype]
        congr 1
      rw [h1, Fintype.card_congr hker_phi_equiv.toEquiv]
      simp [Fintype.card_pi, Nat.card_eq_fintype_card]
    have hcard_good : Nat.card {g : Fin k → ZMod 2 // good g} =
        (Finset.univ.filter (fun g : Fin k → ZMod 2 => good g)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hcard_rhs : Nat.card {h : Fin k → ZMod 2 // trans h ∧ N h = 0} =
        (Finset.univ.filter (fun h : Fin k → ZMod 2 => trans h ∧ N h = 0)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcard_good, hcard_rhs]
    have hfib : (Finset.univ.filter (fun g : Fin k → ZMod 2 => good g)).card =
        ∑ h ∈ Finset.univ.filter (fun h : Fin k → ZMod 2 => trans h ∧ N h = 0),
          (Finset.univ.filter (fun g : Fin k → ZMod 2 => φ g = h)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin k → ZMod 2 => φ g)
        (t := Finset.univ.filter (fun h : Fin k → ZMod 2 => trans h ∧ N h = 0))]
      · refine Finset.sum_congr rfl fun h hh => ?_
        rw [Finset.mem_filter] at hh
        congr 1
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
        intro hfg
        rw [hgood_iff g]
        change trans (φ g)
        rw [hfg]
        exact hh.2.1
      · intro g hg
        rw [Finset.mem_coe, Finset.mem_filter] at hg ⊢
        refine ⟨Finset.mem_univ _, (hgood_iff g).mp hg.2,
          (hmem_range (φ g)).mp (LinearMap.mem_range_self φ g)⟩
    rw [hfib]
    have hfib_const : ∀ h ∈ Finset.univ.filter (fun h : Fin k → ZMod 2 => trans h ∧ N h = 0),
        (Finset.univ.filter (fun g : Fin k → ZMod 2 => φ g = h)).card =
        2 ^ Nat.card (Quot edge) := by
      intro h hh
      rw [Finset.mem_filter] at hh
      rcases (hmem_range h).mpr hh.2.2 with ⟨g₀, hg₀⟩
      rw [← hcard_ker]
      symm
      refine Finset.card_bij (fun g _ => g + g₀) ?_ ?_ ?_
      · intro g hg
        rw [Finset.mem_filter] at hg ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [map_add, hg.2, hg₀, zero_add]
      · intro g₁ _ g₂ _ heq
        exact add_right_cancel heq
      · intro g hg
        rw [Finset.mem_filter] at hg
        refine ⟨g + g₀, ?_, vec_add_cancel_right g g₀⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [map_add, hg.2, hg₀, vec_add_self]
    rw [Finset.sum_congr rfl hfib_const, Finset.sum_const, smul_eq_mul, mul_comm]

private lemma part2 (k : ℕ) (hk : 0 < k) (hk3 : 3 ≤ k) :
    let W := Fin k → ZMod 2
    let R := fun (x : W) (i : Fin k) => x ⟨(i.val + k - 1) % k, Nat.mod_lt _ hk⟩
    let flip : W := fun i => if i.val = 0 then 1 else 0
    let ones : W := fun _ => 1
    let member := fun x : W => ∃ t : Fin (k + 1),
      (∀ i : Fin k, x i = (if i.val < t.val then 1 else 0)) ∨
      (∀ i : Fin k, x i = (if t.val ≤ i.val then 1 else 0))
    (∀ x : W, member (R x + flip) ↔ member x) ∧
    (∀ v : W, (∀ x : W, member (x + v) ↔ member x) ↔ v = 0 ∨ v = ones) ∧
    Nat.card {g : W // ∀ x : W, member (R x + g) ↔ member (x + g)} =
      (if k % 2 = 0 then 0 else 2) := by
  let σ : Equiv.Perm (Fin k) :=
    { toFun := fun i => ⟨(i.val + k - 1) % k, Nat.mod_lt _ hk⟩
      invFun := fun i => ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
      left_inv := fun i => by
        ext
        dsimp only
        have hi : i.val < k := i.isLt
        by_cases h0 : i.val = 0
        · rw [h0]
          have h0k : 0 + k - 1 = k - 1 := by omega
          have h1 : (0 + k - 1) % k = k - 1 := by rw [h0k]; exact Nat.mod_eq_of_lt (by omega)
          rw [h1]
          have h2 : k - 1 + 1 = k := by omega
          rw [h2, Nat.mod_self]
        · have h1 : (i.val + k - 1) % k = i.val - 1 := by
            have : i.val + k - 1 = (i.val - 1) + k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [h1]
          have h2 : i.val - 1 + 1 = i.val := by omega
          rw [h2, Nat.mod_eq_of_lt hi]
      right_inv := fun i => by
        ext
        dsimp only
        have hi : i.val < k := i.isLt
        by_cases hlast : i.val + 1 = k
        · rw [hlast, Nat.mod_self]
          have h0k : 0 + k - 1 = k - 1 := by omega
          have h1 : (0 + k - 1) % k = k - 1 := by rw [h0k]; exact Nat.mod_eq_of_lt (by omega)
          rw [h1]; omega
        · have h1 : (i.val + 1) % k = i.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1]
          have h2 : i.val + 1 + k - 1 = i.val + k := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hi] }
  let R : (Fin k → ZMod 2) → (Fin k → ZMod 2) := fun x i => x (σ i)
  let flip : Fin k → ZMod 2 := fun i => if i.val = 0 then 1 else 0
  let ones : Fin k → ZMod 2 := fun _ => 1
  let member := fun x : Fin k → ZMod 2 => ∃ t : Fin (k + 1),
    (∀ i : Fin k, x i = (if i.val < t.val then 1 else 0)) ∨
    (∀ i : Fin k, x i = (if t.val ≤ i.val then 1 else 0))
  have hmem_fwd : ∀ x : Fin k → ZMod 2, member x → member (R x + flip) := by
    rintro x ⟨t, ht | ht⟩
    · by_cases htk : t.val < k
      · refine ⟨⟨t.val + 1, by omega⟩, Or.inl fun i => ?_⟩
        rw [Pi.add_apply]
        change x (σ i) + flip i = if i.val < t.val + 1 then 1 else 0
        rw [ht (σ i)]
        dsimp only [flip, σ, Equiv.coe_fn_mk]
        by_cases hi0 : i.val = 0
        · simp [hi0, show ¬ (k - 1 < t.val) by omega]
        · have hmod : (i.val + k - 1) % k = i.val - 1 := by
            have : i.val + k - 1 = (i.val - 1) + k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hlt : (i.val + k - 1) % k < t.val ↔ i.val < t.val + 1 := by rw [hmod]; omega
          simp [hi0, hlt]
      · have ht_eq : t.val = k := by omega
        refine ⟨⟨1, by omega⟩, Or.inr fun i => ?_⟩
        rw [Pi.add_apply]
        change x (σ i) + flip i = if 1 ≤ i.val then 1 else 0
        rw [ht (σ i)]
        dsimp only [flip, σ, Equiv.coe_fn_mk]
        have hlt_k : (i.val + k - 1) % k < t.val := by
          rw [ht_eq]; exact Nat.mod_lt _ hk
        rw [ite_eq_left_iff.mpr (fun h => (h hlt_k).elim)]
        by_cases hi0 : i.val = 0
        · simp [hi0, zmod2_add_self]
        · have hge : 1 ≤ i.val := by omega
          simp [hi0, hge]
    · by_cases htk : t.val < k
      · refine ⟨⟨t.val + 1, by omega⟩, Or.inr fun i => ?_⟩
        rw [Pi.add_apply]
        change x (σ i) + flip i = if t.val + 1 ≤ i.val then 1 else 0
        rw [ht (σ i)]
        dsimp only [flip, σ, Equiv.coe_fn_mk]
        by_cases hi0 : i.val = 0
        · simp [hi0, show t.val ≤ k - 1 by omega, zmod2_add_self]
        · have hmod : (i.val + k - 1) % k = i.val - 1 := by
            have : i.val + k - 1 = (i.val - 1) + k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hge : t.val ≤ (i.val + k - 1) % k ↔ t.val + 1 ≤ i.val := by rw [hmod]; omega
          simp [hi0, hge]
      · have ht_eq : t.val = k := by omega
        refine ⟨⟨1, by omega⟩, Or.inl fun i => ?_⟩
        rw [Pi.add_apply]
        change x (σ i) + flip i = if i.val < 1 then 1 else 0
        rw [ht (σ i)]
        dsimp only [flip, σ, Equiv.coe_fn_mk]
        have hnot : ¬ (t.val ≤ (i.val + k - 1) % k) := by
          rw [ht_eq]; exact Nat.not_le_of_gt (Nat.mod_lt _ hk)
        rw [ite_eq_right_iff.mpr (fun h => (hnot h).elim), zero_add]
        by_cases hi0 : i.val = 0
        · simp [hi0]
        · have hlt : ¬ (i.val < 1) := by omega
          simp [hi0, hlt]
  have hmem_trans : ∀ x : Fin k → ZMod 2, member (R x + flip) ↔ member x := by
    classical
    let f : (Fin k → ZMod 2) → (Fin k → ZMod 2) := fun x => R x + flip
    have hf_inj : Function.Injective f := by
      intro x y hxy
      have hRxy : R x = R y := add_right_cancel hxy
      ext i
      have h := congrFun hRxy (σ.symm i)
      simpa [R] using h
    have himg : ∀ x : Fin k → ZMod 2, member (f x) → member x := by
      have hsub : Finset.univ.filter (fun x : Fin k → ZMod 2 => member x) ⊆
          Finset.univ.filter (fun x : Fin k → ZMod 2 => member (f x)) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_univ _, hmem_fwd x hx.2⟩
      have heq_card : (Finset.univ.filter (fun x : Fin k → ZMod 2 => member (f x))).card =
          (Finset.univ.filter (fun x : Fin k → ZMod 2 => member x)).card := by
        refine Finset.card_bij (fun x _ => f x) ?_ (fun _ _ _ _ h => hf_inj h) ?_
        · intro x hx
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨Finset.mem_univ _, hx.2⟩
        · intro y hy
          rw [Finset.mem_filter] at hy
          have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
          rcases hsurj y with ⟨x, rfl⟩
          exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.2⟩, rfl⟩
      have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq heq_card)
      intro x hx
      have hmem : x ∈ Finset.univ.filter (fun x : Fin k → ZMod 2 => member (f x)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      rw [← heq, Finset.mem_filter] at hmem
      exact hmem.2
    intro x
    exact ⟨himg x, hmem_fwd x⟩
  have hmem_ones : ∀ x : Fin k → ZMod 2, member (x + ones) ↔ member x := by
    have hfwd : ∀ x : Fin k → ZMod 2, member x → member (x + ones) := by
      rintro x ⟨t, ht | ht⟩
      · refine ⟨t, Or.inr fun i => ?_⟩
        rw [Pi.add_apply, ht i]
        dsimp only [ones]
        by_cases hlt : i.val < t.val
        · have hle : ¬ (t.val ≤ i.val) := by omega
          simp [hlt, hle, zmod2_add_self]
        · have hle : t.val ≤ i.val := by omega
          simp [hlt, hle]
      · refine ⟨t, Or.inl fun i => ?_⟩
        rw [Pi.add_apply, ht i]
        dsimp only [ones]
        by_cases hle : t.val ≤ i.val
        · have hlt : ¬ (i.val < t.val) := by omega
          simp [hlt, hle, zmod2_add_self]
        · have hlt : i.val < t.val := by omega
          simp [hlt, hle]
    intro x
    exact ⟨fun h => by simpa [vec_add_cancel_right] using hfwd (x + ones) h, hfwd x⟩
  have hnot_101 : ∀ (w : Fin k → ZMod 2) (i₀ i₁ i₂ : Fin k), i₀.val < i₁.val → i₁.val < i₂.val →
      w i₀ = 1 → w i₁ = 0 → w i₂ = 1 → ¬ member w := by
    rintro w i₀ i₁ i₂ h01 h12 hw0 hw1 hw2 ⟨t, ht | ht⟩
    · have h2 := ht i₂
      rw [hw2] at h2
      have h2lt : i₂.val < t.val := by
        by_contra h
        rw [ite_eq_right_iff.mpr (fun h' => (h h').elim)] at h2
        exact absurd h2 (by decide)
      have h1 := ht i₁
      rw [hw1, ite_eq_left_iff.mpr (fun h => (h (by omega)).elim)] at h1
      exact absurd h1 (by decide)
    · have h0 := ht i₀
      rw [hw0] at h0
      have h0ge : t.val ≤ i₀.val := by
        by_contra h
        rw [ite_eq_right_iff.mpr (fun h' => (h h').elim)] at h0
        exact absurd h0 (by decide)
      have h1 := ht i₁
      rw [hw1, ite_eq_left_iff.mpr (fun h => (h (by omega)).elim)] at h1
      exact absurd h1 (by decide)
  have hnot_010 : ∀ (w : Fin k → ZMod 2) (i₀ i₁ i₂ : Fin k), i₀.val < i₁.val → i₁.val < i₂.val →
      w i₀ = 0 → w i₁ = 1 → w i₂ = 0 → ¬ member w := by
    intro w i₀ i₁ i₂ h01 h12 hw0 hw1 hw2 hmem
    have h1 := (hmem_ones w).mpr hmem
    refine hnot_101 (w + ones) i₀ i₁ i₂ h01 h12 ?_ ?_ ?_ h1
    · rw [Pi.add_apply, hw0]; simp [ones]
    · rw [Pi.add_apply, hw1]; simp [ones, zmod2_add_self]
    · rw [Pi.add_apply, hw2]; simp [ones]
  have hperiod_iff : ∀ v : Fin k → ZMod 2,
      (∀ x : Fin k → ZMod 2, member (x + v) ↔ member x) ↔ v = 0 ∨ v = ones := by
    intro v
    constructor
    · intro hv
      have hmem0 : member 0 := ⟨⟨0, by omega⟩, Or.inl fun i => by simp⟩
      have hmemv : member v := by
        have := (hv 0).mpr hmem0
        simpa using this
      have hcheck_prefix : ∀ (u : Fin k → ZMod 2) (t : Fin (k + 1)),
          (∀ x : Fin k → ZMod 2, member (x + u) ↔ member x) →
          (∀ i : Fin k, u i = if i.val < t.val then 1 else 0) →
          u = 0 ∨ u = ones := by
        intro u t hu hut
        by_cases ht0 : t.val = 0
        · left
          ext i
          simp [hut i, ht0]
        · by_cases htk : t.val = k
          · right
            ext i
            simp [hut i, htk, i.isLt, ones]
          · exfalso
            by_cases ht1 : t.val = 1
            · let x : Fin k → ZMod 2 := fun i => if 2 ≤ i.val then 1 else 0
              have hx : member x := ⟨⟨2, by omega⟩, Or.inr fun i => rfl⟩
              have hxu : member (x + u) := (hu x).mpr hx
              refine hnot_101 (x + u) ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
                (by dsimp only; omega) (by dsimp only; omega) ?_ ?_ ?_ hxu
              · rw [Pi.add_apply, hut]; simp [x, ht1]
              · rw [Pi.add_apply, hut]; simp [x, ht1]
              · rw [Pi.add_apply, hut]; simp [x, ht1]
            · let x : Fin k → ZMod 2 := fun i => if i.val < 1 then 1 else 0
              have hx : member x := ⟨⟨1, by omega⟩, Or.inl fun i => rfl⟩
              have hxu : member (x + u) := (hu x).mpr hx
              refine hnot_010 (x + u) ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨k - 1, by omega⟩
                (by dsimp only; omega) (by dsimp only; omega) ?_ ?_ ?_ hxu
              · rw [Pi.add_apply, hut]; simp [x, show 0 < t.val by omega, zmod2_add_self]
              · rw [Pi.add_apply, hut]; simp [x, show 1 < t.val by omega]
              · rw [Pi.add_apply, hut]
                simp [x, show ¬ (k - 1 < t.val) by omega]
                omega
      rcases hmemv with ⟨t, ht | ht⟩
      · exact hcheck_prefix v t hv ht
      · have hv1 : ∀ x : Fin k → ZMod 2, member (x + (v + ones)) ↔ member x := by
          intro x
          rw [← add_assoc, hmem_ones, hv x]
        have hvt1 : ∀ i : Fin k, (v + ones) i = if i.val < t.val then 1 else 0 := by
          intro i
          rw [Pi.add_apply, ht i]
          dsimp only [ones]
          by_cases hlt : i.val < t.val
          · have hge : ¬ (t.val ≤ i.val) := by omega
            simp [hlt, hge]
          · have hge : t.val ≤ i.val := by omega
            simp [hlt, hge, zmod2_add_self]
        rcases hcheck_prefix (v + ones) t hv1 hvt1 with h0 | h1
        · right
          exact vec_add_eq_zero_iff.mp h0
        · left
          have := congrArg (fun w => w + ones) h1
          simpa [vec_add_cancel_right, vec_add_self] using this
    · rintro (rfl | rfl) x
      · simp
      · exact hmem_ones x
  refine ⟨hmem_trans, hperiod_iff, ?_⟩
  let F : (Fin k → ZMod 2) → (Fin 1 → ZMod 2) := fun x _ =>
    @ite (ZMod 2) (member x) (Classical.propDecidable _) 1 0
  have hF_eq : ∀ x y : Fin k → ZMod 2, F x = F y ↔ (member x ↔ member y) := by
    intro x y
    constructor
    · intro h
      have h0 := congrFun h 0
      simp only [F] at h0
      by_cases hx : member x <;> by_cases hy : member y <;> simp_all
    · intro h
      ext _
      simp [F, h]
  have hp1 := part1 k 1 σ F
  let edge := fun a b : Fin k => σ a = b
  let N : (Fin k → ZMod 2) → (Fin k → ZMod 2) := fun x i =>
    (@Finset.filter (Fin k) (fun j : Fin k => Relation.EqvGen edge i j)
      (fun _ => Classical.propDecidable _) Finset.univ).sum x
  have heqv_all : ∀ i j : Fin k, Relation.EqvGen edge i j := by
    have hpow_inv : ∀ d : ℕ, ∀ i : Fin k, ((σ.symm ^ d) i).val = (i.val + d) % k := by
      intro d
      induction d with
      | zero => intro i; simp [Nat.mod_eq_of_lt i.isLt]
      | succ d ih =>
        intro i
        have h1 : (σ.symm ^ (d + 1)) i = σ.symm ((σ.symm ^ d) i) := by
          rw [pow_succ']
          rfl
        rw [h1]
        change (((σ.symm ^ d) i).val + 1) % k = (i.val + (d + 1)) % k
        rw [ih i, Nat.mod_add_mod, add_assoc]
    have heqv_inv : ∀ d : ℕ, ∀ i : Fin k, Relation.EqvGen edge i ((σ.symm ^ d) i) := by
      intro d
      induction d with
      | zero => intro i; exact Relation.EqvGen.refl i
      | succ d ih =>
        intro i
        have h1 : (σ.symm ^ (d + 1)) i = σ.symm ((σ.symm ^ d) i) := by
          rw [pow_succ']
          rfl
        rw [h1]
        exact Relation.EqvGen.trans _ _ _ (ih i)
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (σ.apply_symm_apply _)))
    intro i j
    have hreach : (σ.symm ^ (j.val + k - i.val)) i = j := by
      ext
      rw [hpow_inv]
      have hsum : i.val + (j.val + k - i.val) = j.val + k := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    rw [← hreach]
    exact heqv_inv (j.val + k - i.val) i
  have hquot_card : Nat.card (Quot edge) = 1 := by
    haveI : Unique (Quot edge) :=
      { default := Quot.mk edge ⟨0, hk⟩
        uniq := fun q => by
          induction q using Quot.ind with
          | _ i => exact Quot.eq.mpr (heqv_all i ⟨0, hk⟩) }
    exact Nat.card_unique
  have hN_sum : ∀ (x : Fin k → ZMod 2) (i : Fin k), N x i = ∑ j : Fin k, x j := by
    intro x i
    simp only [N]
    have huniv : @Finset.filter (Fin k) (fun j : Fin k => Relation.EqvGen edge i j)
        (fun _ => Classical.propDecidable _) Finset.univ = Finset.univ := by
      ext j
      simp [heqv_all i j]
    rw [huniv]
  have hgood_eq : Nat.card {g : Fin k → ZMod 2 // ∀ x : Fin k → ZMod 2, member (R x + g) ↔ member (x + g)} =
      Nat.card {g : Fin k → ZMod 2 // ∀ x : Fin k → ZMod 2, F (R x + g) = F (x + g)} := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1, fun x => (hF_eq _ _).mpr (g.2 x)⟩
        invFun := fun g => ⟨g.1, fun x => (hF_eq _ _).mp (g.2 x)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hp1_card : Nat.card {g : Fin k → ZMod 2 // ∀ x : Fin k → ZMod 2, F (R x + g) = F (x + g)} =
      2 ^ Nat.card (Quot edge) *
      Nat.card {h : Fin k → ZMod 2 // (∀ x : Fin k → ZMod 2, F (R x + h) = F x) ∧ N h = 0} :=
    hp1.2.2
  change Nat.card {g : Fin k → ZMod 2 // ∀ x : Fin k → ZMod 2, member (R x + g) ↔ member (x + g)} = _
  rw [hgood_eq, hp1_card, hquot_card, pow_one]
  have htrans_char : ∀ h : Fin k → ZMod 2,
      (∀ x : Fin k → ZMod 2, F (R x + h) = F x) ↔ h = flip ∨ h = flip + ones := by
    intro h
    have hiff : (∀ x : Fin k → ZMod 2, F (R x + h) = F x) ↔
        (∀ x : Fin k → ZMod 2, member (x + (flip + h)) ↔ member x) := by
      constructor
      · intro hh x
        have hx := (hF_eq _ _).mp (hh (fun i => (x + flip) (σ.symm i)))
        have hR : R (fun i => (x + flip) (σ.symm i)) = x + flip := by
          ext i; simp [R]
        rw [hR, add_assoc] at hx
        have hmem_x : member (fun i => (x + flip) (σ.symm i)) ↔ member x := by
          have := hmem_trans (fun i => (x + flip) (σ.symm i))
          rw [hR, vec_add_cancel_right] at this
          exact this.symm
        exact hx.trans hmem_x
      · intro hp x
        rw [hF_eq]
        have h1 : R x + h = (R x + flip) + (flip + h) := by
          ext i
          simp only [Pi.add_apply]
          have := zmod2_add_self (flip i)
          calc
            R x i + h i = R x i + h i + 0 := (add_zero _).symm
            _ = R x i + h i + (flip i + flip i) := by rw [this]
            _ = R x i + flip i + (flip i + h i) := by ring
        rw [h1, hp (R x + flip), hmem_trans x]
    rw [hiff, hperiod_iff]
    constructor
    · rintro (h0 | h1)
      · left
        exact (vec_add_eq_zero_iff.mp h0).symm
      · right
        have := congrArg (fun w => flip + w) h1
        simpa [← add_assoc, vec_add_self, zero_add] using this
    · rintro (rfl | rfl)
      · left; exact vec_add_self flip
      · right; rw [← add_assoc, vec_add_self, zero_add]
  have hN_flip : N flip ⟨0, hk⟩ = 1 := by
    rw [hN_sum]
    rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
    · simp [flip]
    · intro j _ hj
      have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [flip, hj0]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hN_ones : N ones ⟨0, hk⟩ = (k : ZMod 2) := by
    rw [hN_sum]
    simp [ones]
  have hN_flip_ne : N flip ≠ 0 := fun h => by
    have := congrFun h ⟨0, hk⟩
    rw [hN_flip] at this
    simp only [Pi.zero_apply] at this
    exact absurd this (by decide)
  have hN_flip_ones : N (flip + ones) = 0 ↔ k % 2 = 1 := by
    have hsum : ∀ i : Fin k, N (flip + ones) i = 1 + (k : ZMod 2) := by
      intro i
      rw [hN_sum]
      have hadd : (∑ j : Fin k, (flip + ones) j) = (∑ j : Fin k, flip j) + (∑ j : Fin k, ones j) :=
        Finset.sum_add_distrib
      rw [hadd, ← hN_sum flip ⟨0, hk⟩, ← hN_sum ones ⟨0, hk⟩, hN_flip, hN_ones]
    constructor
    · intro h0
      have h1 := congrFun h0 ⟨0, hk⟩
      rw [hsum] at h1
      simp only [Pi.zero_apply] at h1
      have hval : ((k % 2 : ℕ) : ZMod 2) = (k : ZMod 2) := ZMod.natCast_mod k 2
      rw [← hval] at h1
      have hlt : k % 2 < 2 := Nat.mod_lt k (by decide)
      interval_cases hm : k % 2
      · exact absurd h1 (by decide)
      · rfl
    · intro hmod
      ext i
      rw [hsum]
      simp only [Pi.zero_apply]
      have hval : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod k 2).symm
      rw [hval, hmod]
      decide
  split_ifs with heven
  · haveI : IsEmpty {h : Fin k → ZMod 2 // (∀ x : Fin k → ZMod 2, F (R x + h) = F x) ∧ N h = 0} := by
      refine ⟨fun ⟨h, hh, hNh⟩ => ?_⟩
      rcases (htrans_char h).mp hh with rfl | rfl
      · exact hN_flip_ne hNh
      · have := hN_flip_ones.mp hNh
        omega
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero, mul_zero]
  · have hodd : k % 2 = 1 := by omega
    have huniq : Unique {h : Fin k → ZMod 2 // (∀ x : Fin k → ZMod 2, F (R x + h) = F x) ∧ N h = 0} :=
      { default := ⟨flip + ones, (htrans_char _).mpr (Or.inr rfl), hN_flip_ones.mpr hodd⟩
        uniq := fun ⟨h, hh, hNh⟩ => by
          ext : 1
          rcases (htrans_char h).mp hh with rfl | rfl
          · exact (hN_flip_ne hNh).elim
          · rfl }
    rw [Nat.card_unique, mul_one]

end PEqualNP.Outside.L_lib_1079_aux

theorem PEqualNP.Outside.L_lib_1079 :
(∀ (k m : Nat) (σ : Equiv.Perm (Fin k))
    (F : (Fin k → ZMod 2) → (Fin m → ZMod 2)),
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let W := Fin k → ZMod 2
  let R := fun (x : W) (i : Fin k) => x (σ i)
  let edge := fun a b : Fin k => σ a = b
  let N := fun (x : W) (i : Fin k) =>
    (Finset.univ.filter (fun j : Fin k => Relation.EqvGen edge i j)).sum x
  let period := fun v : W => ∀ x : W, F (x+v) = F x
  let trans := fun h : W => ∀ x : W, F (R x+h) = F x
  let good := fun g : W => ∀ x : W, F (R x+g) = F (x+g)
  (∀ g : W, good g ↔ trans (g+R g)) ∧
  (∀ h : W, trans h → ((∃ g : W, good g) ↔ ∃ v : W, period v ∧ N v = N h)) ∧
  Nat.card {g : W // good g} =
    2^(Nat.card (Quot edge)) * Nat.card {h : W // trans h ∧ N h = 0}) ∧
(∀ (k : Nat) (hk : 0 < k), 3 ≤ k →
  let W := Fin k → ZMod 2
  let R := fun (x : W) (i : Fin k) => x ⟨(i.val+k-1)%k, Nat.mod_lt _ hk⟩
  let flip : W := fun i => if i.val = 0 then 1 else 0
  let ones : W := fun _ => 1
  let member := fun x : W => ∃ t : Fin (k+1),
    (∀ i : Fin k, x i = (if i.val < t.val then 1 else 0)) ∨
    (∀ i : Fin k, x i = (if t.val ≤ i.val then 1 else 0))
  (∀ x : W, member (R x+flip) ↔ member x) ∧
  (∀ v : W, (∀ x : W, member (x+v) ↔ member x) ↔ v = 0 ∨ v = ones) ∧
  Nat.card {g : W // ∀ x : W, member (R x+g) ↔ member (x+g)} =
    (if k % 2 = 0 then 0 else 2)) :=
  ⟨PEqualNP.Outside.L_lib_1079_aux.part1, PEqualNP.Outside.L_lib_1079_aux.part2⟩

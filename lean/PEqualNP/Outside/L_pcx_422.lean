import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_422_aux

private abbrev F := ZMod 2

private lemma z2_add_self (x : F) : x + x = 0 := by fin_cases x <;> rfl

private lemma z2_mul_self (x : F) : x * x = x := by fin_cases x <;> rfl

private lemma z2_eq_one {x : F} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

private lemma zmod2_line_prod (p q u0 u1 : F) (hne : p ≠ 0 ∨ q ≠ 0) (heq : p * u0 + q * u1 = 0) :
    u0 * u1 = p * q * u0 := by
  revert p q u0 u1 hne heq; decide

private def cOf (q : F) (v : Fin 3 → F) : F :=
  if q ≠ 0 then v 0 else v 1

private lemma cOf_add (q : F) (u v : Fin 3 → F) : cOf q (u + v) = cOf q u + cOf q v := by
  simp only [cOf, Pi.add_apply]; split_ifs <;> rfl

private lemma cOf_smul (q a : F) (u : Fin 3 → F) : cOf q (a • u) = a * cOf q u := by
  simp only [cOf, Pi.smul_apply, smul_eq_mul]; split_ifs <;> rfl

private lemma zmod2_line_coords (p q u0 u1 : F) (hne : p ≠ 0 ∨ q ≠ 0) (heq : p * u0 + q * u1 = 0) :
    u0 = (if q ≠ 0 then u0 else u1) * q ∧ u1 = (if q ≠ 0 then u0 else u1) * p := by
  revert p q u0 u1 hne heq; decide

private lemma zmod2_cOf_mk (p q c : F) (hne : p ≠ 0 ∨ q ≠ 0) :
    (if q ≠ 0 then c * q else c * p) = c := by
  revert p q c hne; decide

private lemma zmod2_line_eq_zero (p q c : F) : p * (c * q) + q * (c * p) = 0 := by
  fin_cases p <;> fin_cases q <;> fin_cases c <;> rfl

private lemma zmod2_exists_pq (P : Submodule F (Fin 2 → F)) (hdim : Module.finrank F P = 1) :
    ∃ p q : F, (p ≠ 0 ∨ q ≠ 0) ∧
      ∀ v : Fin 2 → F, v ∈ P ↔ p * v 0 + q * v 1 = 0 := by
  have hpos : 0 < Module.finrank F P := by omega
  obtain ⟨⟨w, hwP⟩, hne⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := F) (M := P)).mp hpos
  have hw0 : w ≠ 0 := fun h => hne (Subtype.ext h)
  have hwne : w 1 ≠ 0 ∨ w 0 ≠ 0 := by
    by_contra h
    push Not at h
    apply hw0
    funext idx
    fin_cases idx
    · exact h.2
    · exact h.1
  refine ⟨w 1, w 0, hwne, fun v => ?_⟩
  let Q : Submodule F (Fin 2 → F) :=
    { carrier := {x | w 1 * x 0 + w 0 * x 1 = 0}
      zero_mem' := by simp, add_mem' := fun {a b} ha hb => by
        show w 1 * (a 0 + b 0) + w 0 * (a 1 + b 1) = 0
        have ha' : w 1 * a 0 + w 0 * a 1 = 0 := ha
        have hb' : w 1 * b 0 + w 0 * b 1 = 0 := hb
        linear_combination ha' + hb'
      smul_mem' := fun c {x} hx => by
        show w 1 * (c * x 0) + w 0 * (c * x 1) = 0
        have hx' : w 1 * x 0 + w 0 * x 1 = 0 := hx
        linear_combination c * hx' }
  have hPQ : P ≤ Q := by
    have hspan : Submodule.span F ({w} : Set (Fin 2 → F)) = P := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_singleton_le_iff_mem]; exact hwP
      · rw [finrank_span_singleton hw0, hdim]
    rw [← hspan, Submodule.span_singleton_le_iff_mem]
    show w 1 * w 0 + w 0 * w 1 = 0
    rw [mul_comm (w 0) (w 1), z2_add_self]
  have hQdim : Module.finrank F Q = 1 := by
    let φ : (Fin 2 → F) →ₗ[F] F :=
      { toFun := fun x => w 1 * x 0 + w 0 * x 1
        map_add' := fun x y => by simp only [Pi.add_apply]; ring
        map_smul' := fun a x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    have hker : LinearMap.ker φ = Q := by ext x; rfl
    have hsurj : LinearMap.range φ = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro y
      rcases hwne with h1 | h0
      · refine ⟨![y, 0], ?_⟩
        simp [φ, z2_eq_one h1]
      · refine ⟨![0, y], ?_⟩
        simp [φ, z2_eq_one h0]
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    rw [hsurj, hker, finrank_top, Module.finrank_fin_fun, Module.finrank_self] at hrn
    omega
  have hEq : P = Q := Submodule.eq_of_le_of_finrank_eq hPQ (by rw [hdim, hQdim])
  rw [hEq]
  rfl

private def boxSub {r : ℕ} (I J : Finset (Fin r)) (p q : Fin r → F) : Submodule F (Fin r → Fin 3 → F) where
  carrier := {u | (∀ i ∈ I, p i * u i 0 + q i * u i 1 = 0) ∧ (∀ i, i ∉ I → i ∉ J → u i = 0)}
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => rfl⟩; add_mem' := fun {a b} ha hb =>
    ⟨fun i hi => by
      show p i * (a i 0 + b i 0) + q i * (a i 1 + b i 1) = 0
      linear_combination ha.1 i hi + hb.1 i hi,
     fun i hi hj => by
      show a i + b i = 0
      rw [ha.2 i hi hj, hb.2 i hi hj, add_zero]⟩
  smul_mem' := fun c {x} hx =>
    ⟨fun i hi => by
      show p i * (c * x i 0) + q i * (c * x i 1) = 0
      linear_combination c * hx.1 i hi,
     fun i hi hj => by
      show c • x i = 0
      rw [hx.2 i hi hj, smul_zero]⟩

private lemma finrank_boxSub {r : ℕ} (I J : Finset (Fin r)) (p q : Fin r → F)
    (hdisj : Disjoint I J) (hpq : ∀ i ∈ I, p i ≠ 0 ∨ q i ≠ 0) :
    Module.finrank F (boxSub I J p q) = 2 * I.card + 3 * J.card := by
  let e : boxSub I J p q ≃ₗ[F] ((↥I → Fin 2 → F) × (↥J → Fin 3 → F)) :=
    { toFun := fun u =>
        (fun i => ![cOf (q i.1) (u.1 i.1), u.1 i.1 2],
         fun j => u.1 j.1)
      map_add' := fun u v => by
        apply Prod.ext
        · funext i idx
          fin_cases idx
          · exact cOf_add (q i.1) (u.1 i.1) (v.1 i.1)
          · rfl
        · funext j idx; rfl
      map_smul' := fun a u => by
        apply Prod.ext
        · funext i idx
          fin_cases idx
          · exact cOf_smul (q i.1) a (u.1 i.1)
          · rfl
        · funext j idx; rfl
      invFun := fun vw =>
        ⟨fun i =>
          if hi : i ∈ I then ![vw.1 ⟨i, hi⟩ 0 * q i, vw.1 ⟨i, hi⟩ 0 * p i, vw.1 ⟨i, hi⟩ 1]
          else if hj : i ∈ J then vw.2 ⟨i, hj⟩
          else 0,
         ⟨fun i hi => by
            simp only [hi, ↓reduceDIte, Matrix.cons_val_zero, Matrix.cons_val_one]
            exact zmod2_line_eq_zero (p i) (q i) _,
          fun i hi hj => by simp [hi, hj]⟩⟩
      left_inv := fun u => by
        apply Subtype.ext
        funext i idx
        by_cases hi : i ∈ I
        · simp only [hi, ↓reduceDIte]
          have hc := zmod2_line_coords (p i) (q i) (u.1 i 0) (u.1 i 1) (hpq i hi) (u.2.1 i hi)
          fin_cases idx
          · exact hc.1.symm
          · exact hc.2.symm
          · rfl
        · by_cases hj : i ∈ J
          · simp [hi, hj]
          · simp [hi, hj, u.2.2 i hi hj]
      right_inv := fun ⟨v, w⟩ => by
        apply Prod.ext
        · funext ⟨i, hi⟩ idx
          fin_cases idx
          · simp only [hi, ↓reduceDIte, cOf, Matrix.cons_val_zero, Matrix.cons_val_one]
            exact zmod2_cOf_mk (p i) (q i) (v ⟨i, hi⟩ 0) (hpq i hi)
          · simp [hi]
        · funext ⟨j, hj⟩ idx
          have hnotI : j ∉ I := Finset.disjoint_right.mp hdisj hj
          simp [hnotI, hj] }
  rw [e.finrank_eq, Module.finrank_prod]
  have h1 : Module.finrank F (↥I → Fin 2 → F) = 2 * I.card := by
    rw [Module.finrank_pi_fintype]
    simp [mul_comm]
  have h2 : Module.finrank F (↥J → Fin 3 → F) = 3 * J.card := by
    rw [Module.finrank_pi_fintype]
    simp [mul_comm]
  rw [h1, h2]

private lemma exists_inj_subset {r s : ℕ} (T : Finset (Fin r))
    (V : Type*) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hdimV : Module.finrank F V = s) (ψ : Fin r → V →ₗ[F] F)
    (hinj : ∀ v : V, (∀ i ∈ T, ψ i v = 0) → v = 0) :
    ∃ B : Finset (Fin r), B ⊆ T ∧ B.card = s ∧ ∀ v : V, (∀ i ∈ B, ψ i v = 0) → v = 0 := by
  let kerOn : Finset (Fin r) → Submodule F V := fun B =>
    { carrier := {v | ∀ i ∈ B, ψ i v = 0}
      zero_mem' := fun i _ => map_zero (ψ i), add_mem' := fun ha hb i hi => by
        rw [map_add, ha i hi, hb i hi, add_zero]
      smul_mem' := fun a _ hx i hi => by
        rw [map_smul, hx i hi, smul_zero] }
  have hstep : ∀ k ≤ s, ∃ B : Finset (Fin r), B ⊆ T ∧ B.card = k ∧
      Module.finrank F (kerOn B) = s - k := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨∅, Finset.empty_subset T, rfl, ?_⟩
      have htop : kerOn ∅ = ⊤ := by ext v; simp [kerOn]
      rw [htop, finrank_top, hdimV, Nat.sub_zero]
    | succ k ih =>
      obtain ⟨B, hBT, hBcard, hBdim⟩ := ih (by omega)
      have hpos : 0 < Module.finrank F (kerOn B) := by omega
      obtain ⟨⟨w, hwB⟩, hwne⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := F) (M := kerOn B)).mp hpos
      have hw0 : w ≠ 0 := fun h => hwne (Subtype.ext h)
      have hex : ∃ i ∈ T, ψ i w ≠ 0 := by
        by_contra h
        push Not at h
        exact hw0 (hinj w h)
      obtain ⟨i0, hi0T, hi0ne⟩ := hex
      have hi0notB : i0 ∉ B := fun hmem => hi0ne (hwB i0 hmem)
      refine ⟨insert i0 B, Finset.insert_subset_iff.mpr ⟨hi0T, hBT⟩,
        by rw [Finset.card_insert_of_notMem hi0notB, hBcard], ?_⟩
      let φ : kerOn B →ₗ[F] F := (ψ i0).domRestrict (kerOn B)
      have hsurj : LinearMap.range φ = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro y
        refine ⟨y • ⟨w, hwB⟩, ?_⟩
        simp [φ, z2_eq_one hi0ne]
      have hker_eq : (LinearMap.ker φ).map (kerOn B).subtype = kerOn (insert i0 B) := by
        ext v
        simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype]
        constructor
        · rintro ⟨⟨x, hxB⟩, hx0, rfl⟩ i hi
          rcases Finset.mem_insert.mp hi with rfl | hiB
          · exact hx0
          · exact hxB i hiB
        · intro hv
          refine ⟨⟨v, fun i hiB => hv i (Finset.mem_insert_of_mem hiB)⟩,
            hv i0 (Finset.mem_insert_self i0 B), rfl⟩
      have hker_dim : Module.finrank F (LinearMap.ker φ) = Module.finrank F (kerOn (insert i0 B)) := by
        rw [← hker_eq]
        exact (Submodule.finrank_map_subtype_eq (kerOn B) (LinearMap.ker φ)).symm
      have hrn := LinearMap.finrank_range_add_finrank_ker φ
      rw [hsurj, finrank_top, Module.finrank_self, hker_dim, hBdim] at hrn
      omega
  obtain ⟨B, hBT, hBcard, hBdim⟩ := hstep s (le_refl s)
  rw [Nat.sub_self] at hBdim
  refine ⟨B, hBT, hBcard, fun v hv => ?_⟩
  have hbot : kerOn B = ⊥ := Submodule.finrank_eq_zero.mp hBdim
  have hmem : v ∈ kerOn B := hv
  rw [hbot] at hmem
  exact hmem

end PEqualNP.Outside.L_pcx_422_aux

open PEqualNP.Outside.L_pcx_422_aux in
theorem PEqualNP.Outside.L_pcx_422 :
    ∀ (r s t : ℕ) (_ : s+t ≤ r) (_ : t=0 ∨ s+t=r),
      let F := ZMod 2
      let X := Fin r → Fin 3 → F
      let Y := Fin r → F
      let f := fun (x : X) (i : Fin r) => x i 2 + x i 0 * x i 1
      let finish := fun (S : Submodule F X) (e : ℕ) =>
        ∀ a : X, ∃ (ask : X →ₗ[F] (Fin e → F)) (out : (Fin e → F) → Y),
          ∀ u ∈ S, out (ask (a+u)) = f (a+u)
      ∀ (S : Submodule F X) (_ : Module.finrank F S = 2*s+3*t),
        finish S (s+3*t) ↔
        ∃ (I J : Finset (Fin r)) (p q : Fin r → F),
          Disjoint I J ∧ I.card = s ∧ J.card = t ∧
          (∀ i ∈ I, p i ≠ 0 ∨ q i ≠ 0) ∧
          ∀ u : X, u ∈ S ↔
            (∀ i ∈ I, p i * u i 0 + q i * u i 1 = 0) ∧
            (∀ i : Fin r, i ∉ I → i ∉ J → u i = 0) := by
  intro r s t hst hbdry F X Y f finish S hdimS
  classical
  constructor
  · -- (⇒) direction
    intro hfin
    let proj2 : Fin r → S →ₗ[F] (Fin 2 → F) := fun i =>
      { toFun := fun u => ![u.1 i 0, u.1 i 1]
        map_add' := fun u v => by
          funext idx; fin_cases idx <;> rfl
        map_smul' := fun a u => by
          funext idx; fin_cases idx <;> rfl }
    let dOf : Fin r → ℕ := fun i => Module.finrank F (LinearMap.range (proj2 i))
    have hd_le : ∀ i, dOf i ≤ 2 := fun i => by
      have h := Submodule.finrank_le (LinearMap.range (proj2 i))
      simpa [Module.finrank_fin_fun] using h
    let Z : Finset (Fin r) := Finset.univ.filter (fun i => dOf i = 0)
    let I₁ : Finset (Fin r) := Finset.univ.filter (fun i => dOf i = 1)
    let J₂ : Finset (Fin r) := Finset.univ.filter (fun i => dOf i = 2)
    have hZ_zero : ∀ i ∈ Z, ∀ u ∈ S, u i 0 = 0 ∧ u i 1 = 0 := by
      intro i hi u hu
      have hd0 : Module.finrank F (LinearMap.range (proj2 i)) = 0 := (Finset.mem_filter.mp hi).2
      have hbot : LinearMap.range (proj2 i) = ⊥ := Submodule.finrank_eq_zero.mp hd0
      have hmem : proj2 i ⟨u, hu⟩ = 0 := by
        have : proj2 i ⟨u, hu⟩ ∈ LinearMap.range (proj2 i) := LinearMap.mem_range_self _ _
        rwa [hbot] at this
      exact ⟨congrFun hmem 0, congrFun hmem 1⟩
    have hJ₂_surj : ∀ i ∈ J₂, ∀ x y : F, ∃ u ∈ S, u i 0 = x ∧ u i 1 = y := by
      intro i hi x y
      have hd2 : Module.finrank F (LinearMap.range (proj2 i)) = 2 := (Finset.mem_filter.mp hi).2
      have htop : LinearMap.range (proj2 i) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [hd2, Module.finrank_fin_fun])
      have hmem : ![x, y] ∈ LinearMap.range (proj2 i) := by rw [htop]; trivial
      obtain ⟨⟨u, hu⟩, hEq⟩ := hmem
      exact ⟨u, hu, congrFun hEq 0, congrFun hEq 1⟩
    have hI₁_ex : ∀ i ∈ I₁, ∃ p q : F, (p ≠ 0 ∨ q ≠ 0) ∧
        ∀ v : Fin 2 → F, v ∈ LinearMap.range (proj2 i) ↔ p * v 0 + q * v 1 = 0 :=
      fun i hi => zmod2_exists_pq (LinearMap.range (proj2 i)) (Finset.mem_filter.mp hi).2
    let p : Fin r → F := fun i => if h : i ∈ I₁ then (hI₁_ex i h).choose else 0
    let q : Fin r → F := fun i => if h : i ∈ I₁ then (hI₁_ex i h).choose_spec.choose else 0
    have hpq_ne : ∀ i ∈ I₁, p i ≠ 0 ∨ q i ≠ 0 := fun i hi => by
      simp only [p, q, hi, ↓reduceDIte]
      exact (hI₁_ex i hi).choose_spec.choose_spec.1
    have hpq_iff : ∀ i ∈ I₁, ∀ v : Fin 2 → F,
        v ∈ LinearMap.range (proj2 i) ↔ p i * v 0 + q i * v 1 = 0 := fun i hi => by
      simp only [p, q, hi, ↓reduceDIte]
      exact (hI₁_ex i hi).choose_spec.choose_spec.2
    have hI₁_eq : ∀ i ∈ I₁, ∀ u ∈ S, p i * u i 0 + q i * u i 1 = 0 := by
      intro i hi u hu
      exact (hpq_iff i hi ![u i 0, u i 1]).mp ⟨⟨u, hu⟩, rfl⟩
    have hI₁_coords : ∀ i ∈ I₁, ∀ u ∈ S,
        u i 0 = cOf (q i) (u i) * q i ∧ u i 1 = cOf (q i) (u i) * p i := by
      intro i hi u hu
      exact zmod2_line_coords (p i) (q i) (u i 0) (u i 1) (hpq_ne i hi) (hI₁_eq i hi u hu)
    -- Polarization lemma for any shift a : X
    have hKa : ∀ a : X, ∃ K : Submodule F X, K ≤ S ∧ s ≤ Module.finrank F K ∧
        (∀ v ∈ K, (∀ i, i ∉ I₁ → v i = 0) ∧
          (∀ i ∈ I₁, v i 2 = (a i 0 * p i + a i 1 * q i + p i * q i) * cOf (q i) (v i))) := by
      intro a
      obtain ⟨ask, out, hout⟩ := hfin a
      let K : Submodule F X := S ⊓ LinearMap.ker ask
      have hKS : K ≤ S := inf_le_left
      have hKdim : s ≤ Module.finrank F K := by
        let askS : S →ₗ[F] (Fin (s + 3 * t) → F) := ask.domRestrict S
        have hker_eq : (LinearMap.ker askS).map S.subtype = K := by
          ext v
          simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype, K, Submodule.mem_inf]
          constructor
          · rintro ⟨⟨x, hxS⟩, hx0, rfl⟩; exact ⟨hxS, hx0⟩
          · rintro ⟨hvS, hv0⟩; exact ⟨⟨v, hvS⟩, hv0, rfl⟩
        have hker_dim : Module.finrank F (LinearMap.ker askS) = Module.finrank F K := by
          rw [← hker_eq]; exact (Submodule.finrank_map_subtype_eq S (LinearMap.ker askS)).symm
        have hrn := LinearMap.finrank_range_add_finrank_ker askS
        have hrange_le : Module.finrank F (LinearMap.range askS) ≤ s + 3 * t := by
          have := Submodule.finrank_le (LinearMap.range askS)
          simpa [Module.finrank_fin_fun] using this
        rw [hdimS, hker_dim] at hrn
        omega
      have hpol : ∀ v ∈ K, ∀ u ∈ S, f (a + u + v) = f (a + u) := by
        intro v hv u hu
        have hvS : v ∈ S := hv.1
        have hv0 : ask v = 0 := hv.2
        have h1 := hout (u + v) (S.add_mem hu hvS)
        have h2 := hout u hu
        have hask : ask (a + (u + v)) = ask (a + u) := by
          rw [← add_assoc a u v, map_add, hv0, add_zero]
        rw [add_assoc a u v, ← h1, hask, h2]
      refine ⟨K, hKS, hKdim, fun v hv => ?_⟩
      have hB : ∀ i : Fin r, v i 2 = a i 0 * v i 1 + a i 1 * v i 0 + v i 0 * v i 1 := by
        intro i
        have h0 : a i 2 + v i 2 + (a i 0 + v i 0) * (a i 1 + v i 1) = a i 2 + a i 0 * a i 1 := by
          have h1 := congrFun (hpol v hv 0 S.zero_mem) i
          rw [add_zero] at h1
          exact h1
        have hdiff : (a i 2 + v i 2 + (a i 0 + v i 0) * (a i 1 + v i 1)) +
            (a i 2 + a i 0 * a i 1) = 0 := by rw [h0, z2_add_self]
        have ha2 : a i 2 + a i 2 = 0 := z2_add_self _
        have ha01 : a i 0 * a i 1 + a i 0 * a i 1 = 0 := z2_add_self _
        have hsum0 : (a i 0 * v i 1 + a i 1 * v i 0 + v i 0 * v i 1) +
            (a i 0 * v i 1 + a i 1 * v i 0 + v i 0 * v i 1) = 0 := z2_add_self _
        linear_combination hdiff - ha2 - ha01 - hsum0
      have hA : ∀ i : Fin r, ∀ u ∈ S, u i 0 * v i 1 + u i 1 * v i 0 = 0 := by
        intro i u hu
        have hu' : (a i 2 + u i 2 + v i 2) + (a i 0 + u i 0 + v i 0) * (a i 1 + u i 1 + v i 1) =
            (a i 2 + u i 2) + (a i 0 + u i 0) * (a i 1 + u i 1) :=
          congrFun (hpol v hv u hu) i
        have hdiff : ((a i 2 + u i 2 + v i 2) + (a i 0 + u i 0 + v i 0) * (a i 1 + u i 1 + v i 1)) +
            ((a i 2 + u i 2) + (a i 0 + u i 0) * (a i 1 + u i 1)) = 0 := by rw [hu', z2_add_self]
        have hB' : v i 2 + (a i 0 * v i 1 + a i 1 * v i 0 + v i 0 * v i 1) = 0 := by
          rw [hB i, z2_add_self]
        have h2a2 : (a i 2 + u i 2) + (a i 2 + u i 2) = 0 := z2_add_self _
        have h2a01 : (a i 0 + u i 0) * (a i 1 + u i 1) + (a i 0 + u i 0) * (a i 1 + u i 1) = 0 := z2_add_self _
        linear_combination hdiff - hB' - h2a2 - h2a01
      constructor
      · intro i hi
        have h01 : v i 0 = 0 ∧ v i 1 = 0 := by
          have hd_cases : dOf i = 0 ∨ dOf i = 2 := by
            have hle := hd_le i
            have hne1 : dOf i ≠ 1 := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            omega
          rcases hd_cases with hd0 | hd2
          · exact hZ_zero i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd0⟩) v hv.1
          · have hiJ : i ∈ J₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd2⟩
            obtain ⟨u1, hu1, h10, h11⟩ := hJ₂_surj i hiJ 1 0
            obtain ⟨u2, hu2, h20, h21⟩ := hJ₂_surj i hiJ 0 1
            have hv1 : v i 1 = 0 := by
              have := hA i u1 hu1; simp [h10, h11] at this; exact this
            have hv0 : v i 0 = 0 := by
              have := hA i u2 hu2; simp [h20, h21] at this; exact this
            exact ⟨hv0, hv1⟩
        funext idx
        fin_cases idx
        · exact h01.1
        · exact h01.2
        · show v i 2 = 0
          rw [hB i, h01.1, h01.2]; simp
      · intro i hi
        obtain ⟨hv0, hv1⟩ := hI₁_coords i hi v hv.1
        rw [hB i, hv0, hv1]
        have hsq : cOf (q i) (v i) * cOf (q i) (v i) = cOf (q i) (v i) := z2_mul_self _
        calc a i 0 * (cOf (q i) (v i) * p i) + a i 1 * (cOf (q i) (v i) * q i) +
              (cOf (q i) (v i) * q i) * (cOf (q i) (v i) * p i)
            = (a i 0 * p i + a i 1 * q i) * cOf (q i) (v i) +
              p i * q i * (cOf (q i) (v i) * cOf (q i) (v i)) := by ring
          _ = (a i 0 * p i + a i 1 * q i + p i * q i) * cOf (q i) (v i) := by rw [hsq]; ring
    -- First consequence: s ≤ I₁.card
    have hs_le_I1 : s ≤ I₁.card := by
      obtain ⟨K, hKS, hKdim, hKprop⟩ := hKa 0
      let φ : K →ₗ[F] (↥I₁ → F) :=
        { toFun := fun v i => cOf (q i.1) (v.1 i.1)
          map_add' := fun u v => by funext i; exact cOf_add (q i.1) (u.1 i.1) (v.1 i.1)
          map_smul' := fun a u => by funext i; exact cOf_smul (q i.1) a (u.1 i.1) }
      have hinj : Function.Injective φ := by
        rw [injective_iff_map_eq_zero]
        intro v hv
        apply Subtype.ext
        funext i idx
        by_cases hi : i ∈ I₁
        · have hc0 : cOf (q i) (v.1 i) = 0 := congrFun hv ⟨i, hi⟩
          obtain ⟨hv0, hv1⟩ := hI₁_coords i hi v.1 (hKS v.2)
          have hv2 := (hKprop v.1 v.2).2 i hi
          fin_cases idx
          · show v.1 i 0 = 0; simp [hv0, hc0]
          · show v.1 i 1 = 0; simp [hv1, hc0]
          · show v.1 i 2 = 0; simp [hv2, hc0]
        · exact congrFun ((hKprop v.1 v.2).1 i hi) idx
      have hle := LinearMap.finrank_le_finrank_of_injective hinj
      simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
        Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_one] at hle
      omega
    -- Second consequence: 2*s + 3*t ≤ Z.card + 2*I₁.card + 3*J₂.card
    have hdim_upper : 2 * s + 3 * t ≤ Z.card + 2 * I₁.card + 3 * J₂.card := by
      let emb : S →ₗ[F] ((↥Z → F) × (↥I₁ → Fin 2 → F) × (↥J₂ → Fin 3 → F)) :=
        { toFun := fun u =>
            (fun i => u.1 i.1 2,
             fun i => ![cOf (q i.1) (u.1 i.1), u.1 i.1 2],
             fun j => u.1 j.1)
          map_add' := fun u v => by
            apply Prod.ext
            · funext i; rfl
            · apply Prod.ext
              · funext i idx
                fin_cases idx
                · exact cOf_add (q i.1) (u.1 i.1) (v.1 i.1)
                · rfl
              · funext j idx; rfl
          map_smul' := fun a u => by
            apply Prod.ext
            · funext i; rfl
            · apply Prod.ext
              · funext i idx
                fin_cases idx
                · exact cOf_smul (q i.1) a (u.1 i.1)
                · rfl
              · funext j idx; rfl }
      have hinj : Function.Injective emb := by
        rw [injective_iff_map_eq_zero]
        intro u hu
        apply Subtype.ext
        funext i idx
        have hd_cases : dOf i = 0 ∨ dOf i = 1 ∨ dOf i = 2 := by have := hd_le i; omega
        rcases hd_cases with hd0 | hd1 | hd2
        · have hiZ : i ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd0⟩
          obtain ⟨h0, h1⟩ := hZ_zero i hiZ u.1 u.2
          have h2 : u.1 i 2 = 0 := congrFun (congrArg Prod.fst hu) ⟨i, hiZ⟩
          fin_cases idx
          · exact h0
          · exact h1
          · exact h2
        · have hiI : i ∈ I₁ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd1⟩
          have hc0 : cOf (q i) (u.1 i) = 0 := congrFun (congrFun (congrArg (fun x => x.2.1) hu) ⟨i, hiI⟩) 0
          have h2 : u.1 i 2 = 0 := congrFun (congrFun (congrArg (fun x => x.2.1) hu) ⟨i, hiI⟩) 1
          obtain ⟨h0, h1⟩ := hI₁_coords i hiI u.1 u.2
          fin_cases idx
          · show u.1 i 0 = 0; simp [h0, hc0]
          · show u.1 i 1 = 0; simp [h1, hc0]
          · exact h2
        · have hiJ : i ∈ J₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd2⟩
          exact congrFun (congrFun (congrArg (fun x => x.2.2) hu) ⟨i, hiJ⟩) idx
      have hle := LinearMap.finrank_le_finrank_of_injective hinj
      rw [hdimS, Module.finrank_prod, Module.finrank_prod] at hle
      have hZdim : Module.finrank F (↥Z → F) = Z.card := by
        rw [Module.finrank_pi_fintype]; simp
      have hIdim : Module.finrank F (↥I₁ → Fin 2 → F) = 2 * I₁.card := by
        rw [Module.finrank_pi_fintype]; simp [mul_comm]
      have hJdim : Module.finrank F (↥J₂ → Fin 3 → F) = 3 * J₂.card := by
        rw [Module.finrank_pi_fintype]; simp [mul_comm]
      rw [hZdim, hIdim, hJdim] at hle
      omega
    have hpart_card : Z.card + I₁.card + J₂.card = r := by
      have hd1 : Disjoint Z I₁ := Finset.disjoint_filter.mpr fun _ _ h0 h1 => by omega
      have hd2 : Disjoint (Z ∪ I₁) J₂ := Finset.disjoint_left.mpr fun i h1 h2 => by
        simp only [Z, I₁, J₂, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        omega
      have hunion : Z ∪ I₁ ∪ J₂ = Finset.univ := by
        ext i
        simp only [Z, I₁, J₂, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        have := hd_le i; omega
      rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2, hunion]
      simp
    have hdisj_IJ : Disjoint I₁ J₂ := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    rcases hbdry with ht0 | hstr
    · -- Case t = 0
      subst ht0
      simp only [mul_zero, add_zero] at hdimS
      let KOf : (Fin r → F) → Submodule F X := fun μ =>
        { carrier := {v | v ∈ S ∧ (∀ i, i ∉ I₁ → v i = 0) ∧
            (∀ i ∈ I₁, v i 2 = μ i * cOf (q i) (v i))}
          zero_mem' := ⟨S.zero_mem, fun _ _ => rfl, fun i _ => by show (0 : F) = μ i * cOf (q i) 0; simp [cOf]⟩, add_mem' := fun {a b} ha hb =>
            ⟨S.add_mem ha.1 hb.1,
             fun i hi => by show a i + b i = 0; rw [ha.2.1 i hi, hb.2.1 i hi, add_zero],
             fun i hi => by
              show a i 2 + b i 2 = μ i * cOf (q i) (a i + b i)
              rw [ha.2.2 i hi, hb.2.2 i hi, cOf_add]; ring⟩
          smul_mem' := fun c {x} hx =>
            ⟨S.smul_mem c hx.1,
             fun i hi => by show c • x i = 0; rw [hx.2.1 i hi, smul_zero],
             fun i hi => by
              show c * x i 2 = μ i * cOf (q i) (c • x i)
              rw [hx.2.2 i hi, cOf_smul]; ring⟩ }
      have hKOf_dim : ∀ μ : Fin r → F, s ≤ Module.finrank F (KOf μ) := by
        intro μ
        let a : X := fun i =>
          if hi : i ∈ I₁ then
            if p i ≠ 0 then ![μ i + q i, 0, 0] else ![0, μ i, 0]
          else 0
        obtain ⟨K, hKS, hKdim, hKprop⟩ := hKa a
        have hle : K ≤ KOf μ := by
          intro v hv
          refine ⟨hKS hv, (hKprop v hv).1, fun i hi => ?_⟩
          rw [(hKprop v hv).2 i hi]
          congr 1
          have hne := hpq_ne i hi
          by_cases hp : p i = 0
          · have hq1 : q i = 1 := z2_eq_one (hne.resolve_left (not_not.mpr hp))
            simp [a, hi, hp, hq1]
          · have hp1 : p i = 1 := z2_eq_one hp
            simp only [a, hi, hp1, ↓reduceDIte, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, zero_mul, add_zero, one_mul]
            linear_combination z2_add_self (q i)
        exact le_trans hKdim (Submodule.finrank_mono hle)
      let K0 := KOf (fun _ => 0)
      let K1 := KOf (fun _ => 1)
      have hK0_le : K0 ≤ S := fun _ hv => hv.1
      have hK1_le : K1 ≤ S := fun _ hv => hv.1
      have hK01_inf : K0 ⊓ K1 = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        show v = 0
        funext i idx
        by_cases hi : i ∈ I₁
        · have hv2_0 : v i 2 = 0 := by simpa [K0, KOf] using hv.1.2.2 i hi
          have hv2_1 : v i 2 = cOf (q i) (v i) := by simpa [K1, KOf] using hv.2.2.2 i hi
          have hc0 : cOf (q i) (v i) = 0 := by rw [← hv2_1, hv2_0]
          obtain ⟨h0, h1⟩ := hI₁_coords i hi v hv.1.1
          fin_cases idx
          · show v i 0 = 0; simp [h0, hc0]
          · show v i 1 = 0; simp [h1, hc0]
          · exact hv2_0
        · exact congrFun (hv.1.2.1 i hi) idx
      have hK0_ge : s ≤ Module.finrank F K0 := hKOf_dim (fun _ => 0)
      have hK1_ge : s ≤ Module.finrank F K1 := hKOf_dim (fun _ => 1)
      have hsup_eq : K0 ⊔ K1 = S := by
        apply Submodule.eq_of_le_of_finrank_eq (sup_le hK0_le hK1_le)
        have hadd := Submodule.finrank_sup_add_finrank_inf_eq K0 K1
        rw [hK01_inf, finrank_bot, add_zero] at hadd
        have hle := Submodule.finrank_mono (sup_le hK0_le hK1_le)
        omega
      have hK0_dim : Module.finrank F K0 = s := by
        have hadd := Submodule.finrank_sup_add_finrank_inf_eq K0 K1
        rw [hK01_inf, finrank_bot, add_zero, hsup_eq, hdimS] at hadd
        omega
      have hK1_dim : Module.finrank F K1 = s := by
        have hadd := Submodule.finrank_sup_add_finrank_inf_eq K0 K1
        rw [hK01_inf, finrank_bot, add_zero, hsup_eq, hdimS] at hadd
        omega
      have hS_vanish : ∀ u ∈ S, ∀ i, i ∉ I₁ → u i = 0 := by
        intro u hu
        rw [← hsup_eq] at hu
        obtain ⟨w0, hw0, w1, hw1, rfl⟩ := Submodule.mem_sup.mp hu
        intro i hi
        show w0 i + w1 i = 0
        rw [hw0.2.1 i hi, hw1.2.1 i hi, add_zero]
      let cLin : Fin r → X →ₗ[F] F := fun i =>
        { toFun := fun u => cOf (q i) (u i)
          map_add' := fun u v => cOf_add (q i) (u i) (v i)
          map_smul' := fun a u => cOf_smul (q i) a (u i) }
      let subA0 : Finset (Fin r) → Submodule F X := fun B =>
        { carrier := {w0 | w0 ∈ K0 ∧ ∀ i ∈ B, cLin i w0 = 0}
          zero_mem' := ⟨K0.zero_mem, fun i _ => map_zero _⟩, add_mem' := fun ha hb =>
            ⟨K0.add_mem ha.1 hb.1, fun i hi => by rw [map_add, ha.2 i hi, hb.2 i hi, add_zero]⟩
          smul_mem' := fun a _ hx => ⟨K0.smul_mem a hx.1, fun i hi => by rw [map_smul, hx.2 i hi, smul_zero]⟩ }
      let subA1 : Finset (Fin r) → Submodule F X := fun B =>
        { carrier := {w1 | w1 ∈ K1 ∧ ∀ i ∈ I₁ \ B, cLin i w1 = 0}
          zero_mem' := ⟨K1.zero_mem, fun i _ => map_zero _⟩, add_mem' := fun ha hb =>
            ⟨K1.add_mem ha.1 hb.1, fun i hi => by rw [map_add, ha.2 i hi, hb.2 i hi, add_zero]⟩
          smul_mem' := fun a _ hx => ⟨K1.smul_mem a hx.1, fun i hi => by rw [map_smul, hx.2 i hi, smul_zero]⟩ }
      have hKmu_split : ∀ B : Finset (Fin r), s ≤ Module.finrank F (subA0 B) + Module.finrank F (subA1 B) := by
        intro B
        let μ : Fin r → F := fun i => if i ∈ B then 1 else 0
        have hsub : KOf μ ≤ subA0 B ⊔ subA1 B := by
          intro v hv
          have hvS : v ∈ K0 ⊔ K1 := by rw [hsup_eq]; exact hv.1
          obtain ⟨w0, hw0, w1, hw1, rfl⟩ := Submodule.mem_sup.mp hvS
          have hw0A : w0 ∈ subA0 B := by
            refine ⟨hw0, fun i hiB => ?_⟩
            by_cases hiI : i ∈ I₁
            · have hv2 := hv.2.2 i hiI
              have h0 := hw0.2.2 i hiI
              have h1 := hw1.2.2 i hiI
              simp only [μ, hiB, ↓reduceIte, one_mul, zero_mul] at hv2 h0 h1
              have hadd2 : (w0 + w1) i 2 = w0 i 2 + w1 i 2 := rfl
              have haddc : cOf (q i) ((w0 + w1) i) = cOf (q i) (w0 i) + cOf (q i) (w1 i) :=
                cOf_add (q i) (w0 i) (w1 i)
              rw [hadd2, h0, h1, zero_add, haddc] at hv2
              show cOf (q i) (w0 i) = 0
              linear_combination -hv2
            · show cOf (q i) (w0 i) = 0
              rw [hw0.2.1 i hiI]; simp [cOf]
          have hw1A : w1 ∈ subA1 B := by
            refine ⟨hw1, fun i hi => ?_⟩
            obtain ⟨hiI, hiNotB⟩ := Finset.mem_sdiff.mp hi
            have hv2 := hv.2.2 i hiI
            have h0 := hw0.2.2 i hiI
            have h1 := hw1.2.2 i hiI
            simp only [μ, hiNotB, ↓reduceIte, zero_mul, one_mul] at hv2 h0 h1
            have hadd2 : (w0 + w1) i 2 = w0 i 2 + w1 i 2 := rfl
            rw [hadd2, h0, h1, zero_add] at hv2
            exact hv2
          exact Submodule.mem_sup.mpr ⟨w0, hw0A, w1, hw1A, rfl⟩
        have hinf : subA0 B ⊓ subA1 B = ⊥ := by
          rw [eq_bot_iff]
          intro v hv
          have : v ∈ K0 ⊓ K1 := ⟨hv.1.1, hv.2.1⟩
          rwa [hK01_inf] at this
        have hadd := Submodule.finrank_sup_add_finrank_inf_eq (subA0 B) (subA1 B)
        rw [hinf, finrank_bot, add_zero] at hadd
        calc s ≤ Module.finrank F (KOf μ) := hKOf_dim μ
          _ ≤ Module.finrank F ↥(subA0 B ⊔ subA1 B) := Submodule.finrank_mono hsub
          _ = Module.finrank F (subA0 B) + Module.finrank F (subA1 B) := hadd
      have hK0_inj : ∀ w0 : K0, (∀ i ∈ I₁, (cLin i).domRestrict K0 w0 = 0) → w0 = 0 := by
        intro w0 hw0
        apply Subtype.ext
        funext i idx
        by_cases hi : i ∈ I₁
        · have hc0 : cOf (q i) (w0.1 i) = 0 := hw0 i hi
          obtain ⟨h0, h1⟩ := hI₁_coords i hi w0.1 w0.2.1
          have h2 : w0.1 i 2 = 0 := by simpa [K0, KOf] using w0.2.2.2 i hi
          fin_cases idx
          · show w0.1 i 0 = 0; simp [h0, hc0]
          · show w0.1 i 1 = 0; simp [h1, hc0]
          · exact h2
        · exact congrFun (w0.2.2.1 i hi) idx
      have hK1_inj : ∀ w1 : K1, (∀ i ∈ I₁, cLin i w1.1 = 0) → w1 = 0 := by
        intro w1 hw1
        apply Subtype.ext
        funext i idx
        by_cases hi : i ∈ I₁
        · have hc0 : cOf (q i) (w1.1 i) = 0 := hw1 i hi
          obtain ⟨h0, h1⟩ := hI₁_coords i hi w1.1 w1.2.1
          have h2 : w1.1 i 2 = 0 := by
            have := w1.2.2.2 i hi; simp [hc0] at this; exact this
          fin_cases idx
          · show w1.1 i 0 = 0; simp [h0, hc0]
          · show w1.1 i 1 = 0; simp [h1, hc0]
          · exact h2
        · exact congrFun (w1.2.2.1 i hi) idx
      obtain ⟨B, hBI, hBcard, hBinj⟩ := exists_inj_subset I₁ K0 hK0_dim (fun i => (cLin i).domRestrict K0) hK0_inj
      have hK1_offB : ∀ w1 ∈ K1, ∀ i ∈ I₁ \ B, cLin i w1 = 0 := by
        have hsp := hKmu_split B
        have hA0_bot : subA0 B = ⊥ := by
          rw [eq_bot_iff]
          intro w0 hw0
          have := hBinj ⟨w0, hw0.1⟩ (fun i hi => hw0.2 i hi)
          exact congrArg Subtype.val this
        have hA1_le : subA1 B ≤ K1 := fun _ hw => hw.1
        rw [hA0_bot, finrank_bot, zero_add] at hsp
        have hA1_eq : subA1 B = K1 := Submodule.eq_of_le_of_finrank_eq hA1_le
          (le_antisymm (Submodule.finrank_mono hA1_le) (by rw [hK1_dim]; exact hsp))
        intro w1 hw1 i hi
        rw [← hA1_eq] at hw1
        exact hw1.2 i hi
      have hK0_offB : ∀ w0 ∈ K0, ∀ i ∈ I₁ \ B, cLin i w0 = 0 := by
        have hsp := hKmu_split (I₁ \ B)
        have hA1_bot : subA1 (I₁ \ B) = ⊥ := by
          rw [eq_bot_iff]
          intro w1 hw1
          have hall : ∀ i ∈ I₁, cLin i w1 = 0 := by
            intro i hiI
            by_cases hiB : i ∈ B
            · exact hw1.2 i (Finset.mem_sdiff.mpr ⟨hiI, fun h => (Finset.mem_sdiff.mp h).2 hiB⟩)
            · exact hK1_offB w1 hw1.1 i (Finset.mem_sdiff.mpr ⟨hiI, hiB⟩)
          exact congrArg Subtype.val (hK1_inj ⟨w1, hw1.1⟩ hall)
        have hA0_le : subA0 (I₁ \ B) ≤ K0 := fun _ hw => hw.1
        rw [hA1_bot, finrank_bot, add_zero] at hsp
        have hA0_eq : subA0 (I₁ \ B) = K0 := Submodule.eq_of_le_of_finrank_eq hA0_le
          (le_antisymm (Submodule.finrank_mono hA0_le) (by rw [hK0_dim]; exact hsp))
        intro w0 hw0 i hi
        rw [← hA0_eq] at hw0
        exact hw0.2 i hi
      have hI1_eq_B : I₁ = B := by
        apply Finset.Subset.antisymm _ hBI
        intro i hiI
        by_contra hiNotB
        have hiDiff : i ∈ I₁ \ B := Finset.mem_sdiff.mpr ⟨hiI, hiNotB⟩
        have hzero_all : ∀ u ∈ S, cLin i u = 0 := by
          intro u hu
          rw [← hsup_eq] at hu
          obtain ⟨w0, hw0, w1, hw1, rfl⟩ := Submodule.mem_sup.mp hu
          rw [map_add, hK0_offB w0 hw0 i hiDiff, hK1_offB w1 hw1 i hiDiff, add_zero]
        have hrange_bot : LinearMap.range (proj2 i) = ⊥ := by
          rw [eq_bot_iff]
          rintro _ ⟨⟨u, hu⟩, rfl⟩
          have hc0 : cOf (q i) (u i) = 0 := hzero_all u hu
          obtain ⟨h0, h1⟩ := hI₁_coords i hiI u hu
          funext idx
          fin_cases idx
          · show u i 0 = 0; simp [h0, hc0]
          · show u i 1 = 0; simp [h1, hc0]
        have hd1 : dOf i = 1 := (Finset.mem_filter.mp hiI).2
        have hd0 : dOf i = 0 := by simp [dOf, hrange_bot]
        omega
      have hI1_card : I₁.card = s := by rw [hI1_eq_B, hBcard]
      refine ⟨I₁, ∅, p, q, Finset.disjoint_empty_right I₁, hI1_card, rfl, hpq_ne, ?_⟩
      have hS_le : S ≤ boxSub I₁ ∅ p q := fun u hu =>
        ⟨fun i hi => hI₁_eq i hi u hu, fun i hi _ => hS_vanish u hu i hi⟩
      have hbox_dim : Module.finrank F (boxSub I₁ ∅ p q) = 2 * s := by
        rw [finrank_boxSub I₁ ∅ p q (Finset.disjoint_empty_right I₁) hpq_ne, hI1_card]
        simp
      have hS_eq : S = boxSub I₁ ∅ p q :=
        Submodule.eq_of_le_of_finrank_eq hS_le (by rw [hdimS, hbox_dim])
      intro u
      rw [hS_eq]
      rfl
    · -- Case s + t = r
      have hZ0 : Z.card = 0 := by omega
      have hI1_card : I₁.card = s := by omega
      have hJ2_card : J₂.card = t := by omega
      have hZ_empty : Z = ∅ := Finset.card_eq_zero.mp hZ0
      refine ⟨I₁, J₂, p, q, hdisj_IJ, hI1_card, hJ2_card, hpq_ne, ?_⟩
      have hS_le : S ≤ boxSub I₁ J₂ p q := by
        intro u hu
        refine ⟨fun i hi => hI₁_eq i hi u hu, fun i hi hj => ?_⟩
        have hd_cases : dOf i = 0 ∨ dOf i = 1 ∨ dOf i = 2 := by have := hd_le i; omega
        rcases hd_cases with hd0 | hd1 | hd2
        · have hiZ : i ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd0⟩
          rw [hZ_empty] at hiZ
          exact absurd hiZ (Finset.notMem_empty i)
        · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hd1⟩) hi
        · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hd2⟩) hj
      have hbox_dim : Module.finrank F (boxSub I₁ J₂ p q) = 2 * s + 3 * t := by
        rw [finrank_boxSub I₁ J₂ p q hdisj_IJ hpq_ne, hI1_card, hJ2_card]
      have hS_eq : S = boxSub I₁ J₂ p q :=
        Submodule.eq_of_le_of_finrank_eq hS_le (by rw [hdimS, hbox_dim])
      intro u
      rw [hS_eq]
      rfl
  · -- (⇐) direction
    rintro ⟨I, J, p, q, hdisj, hIcard, hJcard, hpq, hS⟩ a
    let eI : ↥I ≃ Fin s := Fintype.equivFinOfCardEq (by simp [hIcard])
    let eJ : ↥J ≃ Fin t := Fintype.equivFinOfCardEq (by simp [hJcard])
    let e3 : (Fin t × Fin 3) ≃ Fin (3 * t) :=
      finProdFinEquiv.trans (finCongr (mul_comm t 3))
    let eTot : (Fin s ⊕ Fin (3 * t)) ≃ Fin (s + 3 * t) := finSumFinEquiv
    let L_a : Fin r → X →ₗ[F] F := fun i =>
      { toFun := fun x => x i 2 + (a i 1 + p i * q i) * x i 0 + a i 0 * x i 1
        map_add' := fun x y => by
          show (x i 2 + y i 2) + (a i 1 + p i * q i) * (x i 0 + y i 0) + a i 0 * (x i 1 + y i 1) =
            (x i 2 + (a i 1 + p i * q i) * x i 0 + a i 0 * x i 1) +
            (y i 2 + (a i 1 + p i * q i) * y i 0 + a i 0 * y i 1)
          ring
        map_smul' := fun c x => by
          show c * x i 2 + (a i 1 + p i * q i) * (c * x i 0) + a i 0 * (c * x i 1) =
            c * (x i 2 + (a i 1 + p i * q i) * x i 0 + a i 0 * x i 1)
          ring }
    let ask : X →ₗ[F] (Fin (s + 3 * t) → F) :=
      { toFun := fun x idx =>
          match eTot.symm idx with
          | Sum.inl k => L_a (eI.symm k).1 x
          | Sum.inr k =>
            let jc := e3.symm k
            x (eJ.symm jc.1).1 jc.2
        map_add' := fun x y => by
          funext idx
          simp only [Pi.add_apply]
          cases h : eTot.symm idx with
          | inl k => exact map_add (L_a (eI.symm k).1) x y
          | inr k => rfl
        map_smul' := fun c x => by
          funext idx
          simp only [Pi.smul_apply, RingHom.id_apply]
          cases h : eTot.symm idx with
          | inl k => exact map_smul (L_a (eI.symm k).1) c x
          | inr k => rfl }
    let out : (Fin (s + 3 * t) → F) → Y := fun v i =>
      if hi : i ∈ I then
        f a i + v (eTot (Sum.inl (eI ⟨i, hi⟩))) + L_a i a
      else if hj : i ∈ J then
        let jt := eJ ⟨i, hj⟩
        v (eTot (Sum.inr (e3 (jt, 2)))) +
        v (eTot (Sum.inr (e3 (jt, 0)))) * v (eTot (Sum.inr (e3 (jt, 1))))
      else f a i
    refine ⟨ask, out, fun u hu => ?_⟩
    obtain ⟨huI, huOut⟩ := (hS u).mp hu
    funext i
    dsimp only [out]
    by_cases hi : i ∈ I
    · simp only [hi, ↓reduceDIte, ask, LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply]
      have hprod := zmod2_line_prod (p i) (q i) (u i 0) (u i 1) (hpq i hi) (huI i hi)
      have hLa : L_a i (a + u) + L_a i a = L_a i u := by
        rw [map_add]
        have hchar : L_a i a + L_a i a = 0 := z2_add_self _
        linear_combination hchar
      calc f a i + L_a i (a + u) + L_a i a
          = f a i + (L_a i (a + u) + L_a i a) := by ring
        _ = f a i + L_a i u := by rw [hLa]
        _ = (a i 2 + u i 2) + (a i 0 + u i 0) * (a i 1 + u i 1) := by
            simp only [f, L_a, LinearMap.coe_mk, AddHom.coe_mk]
            linear_combination -hprod
        _ = f (a + u) i := rfl
    · by_cases hj : i ∈ J
      · simp only [hi, hj, ↓reduceDIte, ask, LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply]
        rfl
      · simp only [hi, hj, ↓reduceDIte]
        have hu0 : u i = 0 := huOut i hi hj
        show a i 2 + a i 0 * a i 1 = (a i 2 + u i 2) + (a i 0 + u i 0) * (a i 1 + u i 1)
        simp [hu0]

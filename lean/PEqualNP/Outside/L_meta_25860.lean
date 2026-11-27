import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25860_aux

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma vec_add_self {k : ℕ} (x : Fin k → ZMod 2) : x + x = 0 :=
  funext fun i => zmod2_add_self (x i)

private lemma vec_sub_eq_add {k : ℕ} (x y : Fin k → ZMod 2) : x - y = x + y :=
  funext fun i => zmod2_sub_eq_add (x i) (y i)

private lemma vec_add_eq_zero_iff {k : ℕ} (x y : Fin k → ZMod 2) : x + y = 0 ↔ y = x := by
  constructor
  · intro h
    have h1 := congrArg (fun z => x + z) h
    rw [add_zero, ← add_assoc, vec_add_self, zero_add] at h1
    exact h1
  · rintro rfl
    exact vec_add_self y

private lemma rot_inv_idx {k : ℕ} (hk : 0 < k) (m i : ℕ) (hi : i < k) :
    ((i + k - (k - m % k) % k) % k + k - m % k) % k = i := by
  set r := m % k
  have hr : r < k := Nat.mod_lt m hk
  by_cases hr0 : r = 0
  · rw [hr0]
    simp only [Nat.sub_zero, Nat.mod_self, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have hkr : k - r < k := by omega
    rw [Nat.mod_eq_of_lt hkr]
    have h1 : i + k - (k - r) = i + r := by omega
    rw [h1]
    have h2 : ((i + r) % k + k - r) % k = ((i + r) % k + (k - r)) % k := by
      congr 1; omega
    rw [h2, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h3 : i + r + (k - r) = i + k := by omega
    rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

private lemma rot_inv_idx' {k : ℕ} (hk : 0 < k) (m i : ℕ) (hi : i < k) :
    ((i + k - m % k) % k + k - (k - m % k) % k) % k = i := by
  set r := m % k
  have hr : r < k := Nat.mod_lt m hk
  by_cases hr0 : r = 0
  · rw [hr0]
    simp only [Nat.sub_zero, Nat.mod_self, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have hkr : k - r < k := by omega
    rw [Nat.mod_eq_of_lt hkr]
    have h1 : ((i + k - r) % k + k - (k - r)) % k = ((i + k - r) % k + r) % k := by
      congr 1; omega
    rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h2 : i + k - r + r = i + k := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

private lemma exists_mul_mod_eq_one {k a : ℕ} (hk : 2 ≤ k) (hcop : Nat.Coprime a k) :
    ∃ m : ℕ, (m * a) % k = 1 := by
  have : NeZero k := ⟨by omega⟩
  have hu : IsUnit ((a : ℕ) : ZMod k) := (ZMod.isUnit_iff_coprime a k).mpr hcop
  let m : ℕ := ((hu.unit⁻¹ : (ZMod k)ˣ) : ZMod k).val
  refine ⟨m, ?_⟩
  have hmul : ((m * a : ℕ) : ZMod k) = 1 := by
    push_cast
    have hm : (m : ZMod k) = ((hu.unit⁻¹ : (ZMod k)ˣ) : ZMod k) := ZMod.natCast_zmod_val _
    rw [hm]
    exact hu.unit.inv_mul
  have hval := congrArg ZMod.val hmul
  have : Fact (1 < k) := ⟨by omega⟩
  rw [ZMod.val_natCast, ZMod.val_one] at hval
  exact hval

private lemma card_fiber_of_add {k : ℕ} (f : (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (hf : ∀ x y, f (x + y) = f x + f y) (z : Fin k → ZMod 2)
    (hne : ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun x => f x = z)).Nonempty) :
    ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun x => f x = z)).card =
      ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun x => f x = 0)).card := by
  rcases hne with ⟨x0, hx0⟩
  have hfx0 : f x0 = z := (Finset.mem_filter.mp hx0).2
  apply Finset.card_bij (fun x _ => x + x0)
  · intro x hx
    have hfx : f x = z := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hf, hfx, hfx0, vec_add_self]
  · intro x1 _ x2 _ heq
    have h1 := congrArg (fun u => u + x0) heq
    simpa [add_assoc, vec_add_self] using h1
  · intro u hu
    have hfu : f u = 0 := (Finset.mem_filter.mp hu).2
    refine ⟨u + x0, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hf, hfu, hfx0, zero_add]
    · simp [add_assoc, vec_add_self]

private lemma card_image_mul_ker {k : ℕ} (f : (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (hf : ∀ x y, f (x + y) = f x + f y) :
    ((Finset.univ : Finset (Fin k → ZMod 2)).image f).card *
      ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun x => f x = 0)).card = 2 ^ k := by
  have htotal : (Finset.univ : Finset (Fin k → ZMod 2)).card = 2 ^ k := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [← htotal]
  have hpart := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ)
    (t := (Finset.univ : Finset (Fin k → ZMod 2)).image f)
    (fun x hx => Finset.mem_image_of_mem f hx)
  rw [hpart]
  have hcongr :
      ∑ z ∈ (Finset.univ : Finset (Fin k → ZMod 2)).image f,
        ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun x => f x = z)).card =
      ∑ _z ∈ (Finset.univ : Finset (Fin k → ZMod 2)).image f,
        ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun x => f x = 0)).card := by
    apply Finset.sum_congr rfl
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, _, rfl⟩
    exact card_fiber_of_add f hf (f x) ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
  rw [hcongr, Finset.sum_const, smul_eq_mul]

private lemma card_sum_zero {k : ℕ} (hk : 0 < k) :
    ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => ∑ j, w j = 0)).card = 2 ^ (k - 1) := by
  let S := (Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => ∑ j, w j = 0)
  let e : ↥S ≃ (Fin (k - 1) → ZMod 2) :=
    { toFun := fun ⟨w, _⟩ j => w ⟨j.val + 1, by omega⟩
      invFun := fun v =>
        ⟨fun i => if h : i.val = 0 then ∑ j : Fin (k - 1), v j else v ⟨i.val - 1, by omega⟩, by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          let i0 : Fin k := ⟨0, hk⟩
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
          have h0 : (if h : i0.val = 0 then ∑ j : Fin (k - 1), v j else v ⟨i0.val - 1, by omega⟩) =
              ∑ j : Fin (k - 1), v j := by simp [i0]
          rw [h0]
          have hsum :
              ∑ x ∈ Finset.univ.erase i0,
                (if h : x.val = 0 then ∑ j : Fin (k - 1), v j else v ⟨x.val - 1, by omega⟩) =
              ∑ j : Fin (k - 1), v j := by
            apply Finset.sum_bij (fun x hx => (⟨x.val - 1, by
              have hne : x ≠ i0 := (Finset.mem_erase.mp hx).1
              have hpos : x.val ≠ 0 := fun hz => hne (Fin.ext hz)
              omega⟩ : Fin (k - 1)))
            · intro _ _; exact Finset.mem_univ _
            · intro x1 hx1 x2 hx2 heq
              have h1 : x1.val ≠ 0 := fun hz => (Finset.mem_erase.mp hx1).1 (Fin.ext hz)
              have h2 : x2.val ≠ 0 := fun hz => (Finset.mem_erase.mp hx2).1 (Fin.ext hz)
              have hv := congrArg Fin.val heq
              dsimp only at hv
              exact Fin.ext (by omega)
            · intro j _
              refine ⟨⟨j.val + 1, by omega⟩, ?_, ?_⟩
              · rw [Finset.mem_erase]
                exact ⟨fun h => by have := congrArg Fin.val h; dsimp only [i0] at this; omega,
                  Finset.mem_univ _⟩
              · exact Fin.ext (by simp)
            · intro x hx
              have hpos : x.val ≠ 0 := fun hz => (Finset.mem_erase.mp hx).1 (Fin.ext hz)
              simp [hpos]
          rw [hsum, zmod2_add_self]⟩
      left_inv := by
        rintro ⟨w, hw⟩
        apply Subtype.ext
        funext i
        have hsum0 : ∑ j : Fin k, w j = 0 := (Finset.mem_filter.mp hw).2
        by_cases hi : i.val = 0
        · simp only [hi, ↓reduceDIte]
          have hi0 : i = ⟨0, hk⟩ := Fin.ext hi
          rw [hi0]
          let i0 : Fin k := ⟨0, hk⟩
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)] at hsum0
          have hrest : ∑ x ∈ Finset.univ.erase i0, w x =
              ∑ j : Fin (k - 1), w ⟨j.val + 1, by omega⟩ := by
            apply Finset.sum_bij (fun x hx => (⟨x.val - 1, by
              have hpos : x.val ≠ 0 := fun hz => (Finset.mem_erase.mp hx).1 (Fin.ext hz)
              omega⟩ : Fin (k - 1)))
            · intro _ _; exact Finset.mem_univ _
            · intro x1 hx1 x2 hx2 heq
              have h1 : x1.val ≠ 0 := fun hz => (Finset.mem_erase.mp hx1).1 (Fin.ext hz)
              have h2 : x2.val ≠ 0 := fun hz => (Finset.mem_erase.mp hx2).1 (Fin.ext hz)
              have hv := congrArg Fin.val heq
              dsimp only at hv
              exact Fin.ext (by omega)
            · intro j _
              refine ⟨⟨j.val + 1, by omega⟩, ?_, Fin.ext (by simp)⟩
              rw [Finset.mem_erase]
              exact ⟨fun h => by have := congrArg Fin.val h; dsimp only [i0] at this; omega,
                Finset.mem_univ _⟩
            · intro x hx
              have hpos : x.val ≠ 0 := fun hz => (Finset.mem_erase.mp hx).1 (Fin.ext hz)
              congr 1
              exact Fin.ext (by dsimp only; omega)
          rw [hrest] at hsum0
          have hadd := congrArg (fun z => z + w i0) hsum0
          rw [zero_add, add_comm (w i0), add_assoc, zmod2_add_self, add_zero] at hadd
          exact hadd
        · simp only [hi, ↓reduceDIte]
          congr 1
          exact Fin.ext (by dsimp only; omega)
      right_inv := by
        intro v
        funext j
        simp }
  have hc := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hc
  exact hc

private lemma ker_hole_u_card {k d : ℕ} (hk11 : 11 ≤ k) (hd : d = 1 ∨ d = 2) :
    let m : Fin k → ZMod 2 := fun t =>
      if t.val = 0 ∨ t.val = d ∨ t.val = k - d then 0 else 1
    let K : Finset (Fin k → ZMod 2) := (Finset.univ : Finset (Fin k → ZMod 2)).filter (fun v =>
      ∀ t : Fin k,
        let t1 : Fin k := ⟨(t.val + 1) % k, Nat.mod_lt _ (by omega)⟩
        v t * m t1 + v t1 * m t = 0)
    K.card = 2 ^ (if d = 1 then 2 else 3) ∧
      (fun t : Fin k => if t.val = 0 ∨ t.val = d ∨ t.val = k - d then (1 : ZMod 2) else 0) ∉ K := by
  intro m K
  have hk : 0 < k := by omega
  rcases hd with rfl | rfl
  · -- d = 1, free = 2
    simp only [↓reduceIte]
    have hK_iff : ∀ v : Fin k → ZMod 2, v ∈ K ↔
        v ⟨k - 1, by omega⟩ = 0 ∧ v ⟨1, by omega⟩ = 0 ∧
        ∀ t : Fin k, 2 ≤ t.val → t.val ≤ k - 2 → v t = v ⟨2, by omega⟩ := by
      intro v
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hv
        have hkm1 : v ⟨k - 1, by omega⟩ = 0 := by
          have h := hv ⟨k - 2, by omega⟩
          have hmod : (k - 2 + 1) % k = k - 1 := by
            rw [show k - 2 + 1 = k - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
          have h1 : (⟨(k - 2 + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨k - 1, by omega⟩ :=
            Fin.ext hmod
          rw [h1] at h
          have hm1 : m ⟨k - 2, by omega⟩ = 1 := by dsimp only [m]; simp [show k - 2 ≠ 0 by omega, show k - 2 ≠ 1 by omega, show k - 2 ≠ k - 1 by omega]
          have hm2 : m ⟨k - 1, by omega⟩ = 0 := by dsimp only [m]; simp
          rw [hm1, hm2] at h
          simpa using h
        have h1v : v ⟨1, by omega⟩ = 0 := by
          have h := hv ⟨1, by omega⟩
          have hmod : (1 + 1) % k = 2 := Nat.mod_eq_of_lt (by omega)
          have h1 : (⟨(1 + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨2, by omega⟩ := Fin.ext hmod
          rw [h1] at h
          have hm1 : m ⟨1, by omega⟩ = 0 := by dsimp only [m]; simp
          have hm2 : m ⟨2, by omega⟩ = 1 := by dsimp only [m]; simp [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, show (2 : ℕ) ≠ k - 1 by omega]
          rw [hm1, hm2] at h
          simpa using h
        have hrun : ∀ n : ℕ, ∀ hn : n < k, 2 ≤ n → n ≤ k - 2 → v ⟨n, hn⟩ = v ⟨2, by omega⟩ := by
          intro n
          induction n with
          | zero => intro _ hge; omega
          | succ n ih =>
            intro hn hge hle
            by_cases hn2 : n + 1 = 2
            · congr 1; exact Fin.ext hn2
            · have hprev := ih (by omega) (by omega) (by omega)
              have h := hv ⟨n, by omega⟩
              have hmod : (n + 1) % k = n + 1 := Nat.mod_eq_of_lt (by omega)
              have h1 : (⟨(n + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨n + 1, hn⟩ :=
                Fin.ext hmod
              rw [h1] at h
              have hm1 : m ⟨n, by omega⟩ = 1 := by
                dsimp only [m]; simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ k - 1 by omega]
              have hm2 : m ⟨n + 1, hn⟩ = 1 := by
                have hne : ¬ (n + 1 = 0 ∨ n + 1 = 1 ∨ n + 1 = k - 1) := by omega
                simp only [m, hne, ↓reduceIte]
              rw [hm1, hm2, mul_one, mul_one] at h
              have heq : v ⟨n + 1, hn⟩ = v ⟨n, by omega⟩ := by
                have hadd := congrArg (fun z => v ⟨n, by omega⟩ + z) h
                rw [add_zero, ← add_assoc, zmod2_add_self, zero_add] at hadd
                exact hadd
              rw [heq, hprev]
        exact ⟨hkm1, h1v, fun t ht1 ht2 => hrun t.val t.isLt ht1 ht2⟩
      · rintro ⟨hkm1, h1v, hrun⟩ t
        set t1 : Fin k := ⟨(t.val + 1) % k, Nat.mod_lt _ hk⟩
        by_cases h0 : t.val = 0
        · have ht : t = ⟨0, by omega⟩ := Fin.ext h0
          have ht1 : t1 = ⟨1, by omega⟩ := Fin.ext (by dsimp only [t1]; rw [h0]; exact Nat.mod_eq_of_lt (by omega))
          rw [ht, ht1]
          have hm0 : m ⟨0, by omega⟩ = 0 := by dsimp only [m]; simp
          have hm1 : m ⟨1, by omega⟩ = 0 := by dsimp only [m]; simp
          rw [hm0, hm1]; simp
        · by_cases h1 : t.val = 1
          · have ht : t = ⟨1, by omega⟩ := Fin.ext h1
            rw [ht, h1v]
            have hm1 : m ⟨1, by omega⟩ = 0 := by dsimp only [m]; simp
            rw [hm1]; simp
          · by_cases hkm2 : t.val = k - 2
            · have ht1 : t1 = ⟨k - 1, by omega⟩ :=
                Fin.ext (by dsimp only [t1]; rw [hkm2, show k - 2 + 1 = k - 1 by omega]; exact Nat.mod_eq_of_lt (by omega))
              rw [ht1, hkm1]
              have hm2 : m ⟨k - 1, by omega⟩ = 0 := by dsimp only [m]; simp
              rw [hm2]; simp
            · by_cases hkm1' : t.val = k - 1
              · have ht : t = ⟨k - 1, by omega⟩ := Fin.ext hkm1'
                have ht1 : t1 = ⟨0, by omega⟩ :=
                  Fin.ext (by dsimp only [t1]; rw [hkm1', show k - 1 + 1 = k by omega, Nat.mod_self])
                rw [ht, ht1]
                have hm1 : m ⟨k - 1, by omega⟩ = 0 := by dsimp only [m]; simp
                have hm0 : m ⟨0, by omega⟩ = 0 := by dsimp only [m]; simp
                rw [hm1, hm0]; simp
              · have ht_lo : 2 ≤ t.val := by omega
                have ht_hi : t.val ≤ k - 3 := by omega
                have ht1_val : t1.val = t.val + 1 := Nat.mod_eq_of_lt (by omega)
                have hv1 : v t = v ⟨2, by omega⟩ := hrun t ht_lo (by omega)
                have hv2 : v t1 = v ⟨2, by omega⟩ := hrun t1 (by omega) (by omega)
                have hm1 : m t = 1 := by
                  dsimp only [m]; simp [show t.val ≠ 0 by omega, show t.val ≠ 1 by omega, show t.val ≠ k - 1 by omega]
                have hm2 : m t1 = 1 := by
                  dsimp only [m]; simp [show t1.val ≠ 0 by omega, show t1.val ≠ 1 by omega, show t1.val ≠ k - 1 by omega]
                rw [hv1, hv2, hm1, hm2]
                simp [zmod2_add_self]
    refine ⟨?_, ?_⟩
    · let e : ↥K ≃ (ZMod 2 × ZMod 2) :=
        { toFun := fun ⟨v, _⟩ => (v ⟨0, by omega⟩, v ⟨2, by omega⟩)
          invFun := fun ab =>
            ⟨fun t => if t.val = 0 then ab.1 else if t.val = 1 ∨ t.val = k - 1 then 0 else ab.2, by
              rw [hK_iff]
              refine ⟨by simp [show k - 1 ≠ 0 by omega], by simp, fun t ht1 ht2 => ?_⟩
              simp [show t.val ≠ 0 by omega, show t.val ≠ 1 by omega, show t.val ≠ k - 1 by omega,
                show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, show (2 : ℕ) ≠ k - 1 by omega]⟩
          left_inv := by
            rintro ⟨v, hv⟩
            obtain ⟨hkm1, h1v, hrun⟩ := (hK_iff v).mp hv
            apply Subtype.ext
            funext t
            dsimp only
            by_cases h0 : t.val = 0
            · have ht : t = ⟨0, by omega⟩ := Fin.ext h0; rw [ht]; simp
            · by_cases h1 : t.val = 1
              · have ht : t = ⟨1, by omega⟩ := Fin.ext h1; rw [ht, h1v]; simp
              · by_cases hkm : t.val = k - 1
                · have ht : t = ⟨k - 1, by omega⟩ := Fin.ext hkm
                  rw [ht, hkm1]; simp [show k - 1 ≠ 0 by omega]
                · simp only [h0, h1, hkm, or_self, ↓reduceIte]
                  exact (hrun t (by omega) (by omega)).symm
          right_inv := by
            rintro ⟨a, b⟩
            apply Prod.ext
            · simp
            · simp [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, show (2 : ℕ) ≠ k - 1 by omega] }
      have hc := Fintype.card_congr e
      rw [Fintype.card_coe, Fintype.card_prod, ZMod.card] at hc
      exact hc
    · intro hmem
      have h1 := ((hK_iff _).mp hmem).2.1
      simp at h1
  · -- d = 2, free = 3
    simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
    have hK_iff : ∀ v : Fin k → ZMod 2, v ∈ K ↔
        v ⟨0, by omega⟩ = 0 ∧ v ⟨2, by omega⟩ = 0 ∧ v ⟨k - 2, by omega⟩ = 0 ∧
        ∀ t : Fin k, 3 ≤ t.val → t.val ≤ k - 3 → v t = v ⟨3, by omega⟩ := by
      intro v
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hv
        have h0v : v ⟨0, by omega⟩ = 0 := by
          have h := hv ⟨0, by omega⟩
          have h1 : (⟨(0 + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨1, by omega⟩ :=
            Fin.ext (Nat.mod_eq_of_lt (by omega))
          rw [h1] at h
          have hm0 : m ⟨0, by omega⟩ = 0 := by dsimp only [m]; simp
          have hm1 : m ⟨1, by omega⟩ = 1 := by
            dsimp only [m]; simp [show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≠ 2 by omega, show (1 : ℕ) ≠ k - 2 by omega]
          rw [hm0, hm1] at h
          simpa using h
        have h2v : v ⟨2, by omega⟩ = 0 := by
          have h := hv ⟨1, by omega⟩
          have h1 : (⟨(1 + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨2, by omega⟩ :=
            Fin.ext (Nat.mod_eq_of_lt (by omega))
          rw [h1] at h
          have hm1 : m ⟨1, by omega⟩ = 1 := by
            dsimp only [m]; simp [show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≠ 2 by omega, show (1 : ℕ) ≠ k - 2 by omega]
          have hm2 : m ⟨2, by omega⟩ = 0 := by dsimp only [m]; simp
          rw [hm1, hm2] at h
          simpa using h
        have hkm2 : v ⟨k - 2, by omega⟩ = 0 := by
          have h := hv ⟨k - 3, by omega⟩
          have h1 : (⟨(k - 3 + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨k - 2, by omega⟩ :=
            Fin.ext (by rw [show k - 3 + 1 = k - 2 by omega]; exact Nat.mod_eq_of_lt (by omega))
          rw [h1] at h
          have hm1 : m ⟨k - 3, by omega⟩ = 1 := by
            dsimp only [m]; simp [show k - 3 ≠ 0 by omega, show k - 3 ≠ 2 by omega, show k - 3 ≠ k - 2 by omega]
          have hm2 : m ⟨k - 2, by omega⟩ = 0 := by dsimp only [m]; simp
          rw [hm1, hm2] at h
          simpa using h
        have hrun : ∀ n : ℕ, ∀ hn : n < k, 3 ≤ n → n ≤ k - 3 → v ⟨n, hn⟩ = v ⟨3, by omega⟩ := by
          intro n
          induction n with
          | zero => intro _ hge; omega
          | succ n ih =>
            intro hn hge hle
            by_cases hn3 : n + 1 = 3
            · congr 1; exact Fin.ext hn3
            · have hprev := ih (by omega) (by omega) (by omega)
              have h := hv ⟨n, by omega⟩
              have h1 : (⟨(n + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨n + 1, hn⟩ :=
                Fin.ext (Nat.mod_eq_of_lt (by omega))
              rw [h1] at h
              have hm1 : m ⟨n, by omega⟩ = 1 := by
                dsimp only [m]; simp [show n ≠ 0 by omega, show n ≠ 2 by omega, show n ≠ k - 2 by omega]
              have hm2 : m ⟨n + 1, hn⟩ = 1 := by
                have hne : ¬ (n + 1 = 0 ∨ n + 1 = 2 ∨ n + 1 = k - 2) := by omega
                simp only [m, hne, ↓reduceIte]
              rw [hm1, hm2, mul_one, mul_one] at h
              have heq : v ⟨n + 1, hn⟩ = v ⟨n, by omega⟩ := by
                have hadd := congrArg (fun z => v ⟨n, by omega⟩ + z) h
                rw [add_zero, ← add_assoc, zmod2_add_self, zero_add] at hadd
                exact hadd
              rw [heq, hprev]
        exact ⟨h0v, h2v, hkm2, fun t ht1 ht2 => hrun t.val t.isLt ht1 ht2⟩
      · rintro ⟨h0v, h2v, hkm2, hrun⟩ t
        set t1 : Fin k := ⟨(t.val + 1) % k, Nat.mod_lt _ hk⟩
        by_cases h0 : t.val = 0
        · have ht : t = ⟨0, by omega⟩ := Fin.ext h0
          rw [ht, h0v]
          have hm0 : m ⟨0, by omega⟩ = 0 := by dsimp only [m]; simp
          rw [hm0]; simp
        · by_cases h1 : t.val = 1
          · have ht1 : t1 = ⟨2, by omega⟩ :=
              Fin.ext (by dsimp only [t1]; rw [h1]; exact Nat.mod_eq_of_lt (by omega))
            rw [ht1, h2v]
            have hm2 : m ⟨2, by omega⟩ = 0 := by dsimp only [m]; simp
            rw [hm2]; simp
          · by_cases h2 : t.val = 2
            · have ht : t = ⟨2, by omega⟩ := Fin.ext h2
              rw [ht, h2v]
              have hm2 : m ⟨2, by omega⟩ = 0 := by dsimp only [m]; simp
              rw [hm2]; simp
            · by_cases hkm3 : t.val = k - 3
              · have ht1 : t1 = ⟨k - 2, by omega⟩ :=
                  Fin.ext (by dsimp only [t1]; rw [hkm3, show k - 3 + 1 = k - 2 by omega]; exact Nat.mod_eq_of_lt (by omega))
                rw [ht1, hkm2]
                have hm2 : m ⟨k - 2, by omega⟩ = 0 := by dsimp only [m]; simp
                rw [hm2]; simp
              · by_cases hkm2' : t.val = k - 2
                · have ht : t = ⟨k - 2, by omega⟩ := Fin.ext hkm2'
                  rw [ht, hkm2]
                  have hm2 : m ⟨k - 2, by omega⟩ = 0 := by dsimp only [m]; simp
                  rw [hm2]; simp
                · by_cases hkm1 : t.val = k - 1
                  · have ht1 : t1 = ⟨0, by omega⟩ :=
                      Fin.ext (by dsimp only [t1]; rw [hkm1, show k - 1 + 1 = k by omega, Nat.mod_self])
                    rw [ht1, h0v]
                    have hm0 : m ⟨0, by omega⟩ = 0 := by dsimp only [m]; simp
                    rw [hm0]; simp
                  · have ht1_val : t1.val = t.val + 1 := Nat.mod_eq_of_lt (by omega)
                    have hv1 : v t = v ⟨3, by omega⟩ := hrun t (by omega) (by omega)
                    have hv2 : v t1 = v ⟨3, by omega⟩ := hrun t1 (by omega) (by omega)
                    have hm1 : m t = 1 := by
                      dsimp only [m]; simp [show t.val ≠ 0 by omega, show t.val ≠ 2 by omega, show t.val ≠ k - 2 by omega]
                    have hm2 : m t1 = 1 := by
                      dsimp only [m]; simp [show t1.val ≠ 0 by omega, show t1.val ≠ 2 by omega, show t1.val ≠ k - 2 by omega]
                    rw [hv1, hv2, hm1, hm2]
                    simp [zmod2_add_self]
    refine ⟨?_, ?_⟩
    · let e : ↥K ≃ (ZMod 2 × ZMod 2 × ZMod 2) :=
        { toFun := fun ⟨v, _⟩ => (v ⟨1, by omega⟩, v ⟨k - 1, by omega⟩, v ⟨3, by omega⟩)
          invFun := fun abc =>
            ⟨fun t =>
              if t.val = 1 then abc.1
              else if t.val = k - 1 then abc.2.1
              else if t.val = 0 ∨ t.val = 2 ∨ t.val = k - 2 then 0
              else abc.2.2, by
              rw [hK_iff]
              refine ⟨by simp [show (0 : ℕ) ≠ 1 by omega, show (0 : ℕ) ≠ k - 1 by omega],
                by simp [show (2 : ℕ) ≠ 1 by omega, show (2 : ℕ) ≠ k - 1 by omega],
                by simp [show k - 2 ≠ 1 by omega, show k - 2 ≠ k - 1 by omega],
                fun t ht1 ht2 => ?_⟩
              simp [show t.val ≠ 0 by omega, show t.val ≠ 1 by omega, show t.val ≠ 2 by omega,
                show t.val ≠ k - 2 by omega, show t.val ≠ k - 1 by omega,
                show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
                show (3 : ℕ) ≠ k - 2 by omega, show (3 : ℕ) ≠ k - 1 by omega]⟩
          left_inv := by
            rintro ⟨v, hv⟩
            obtain ⟨h0v, h2v, hkm2, hrun⟩ := (hK_iff v).mp hv
            apply Subtype.ext
            funext t
            dsimp only
            by_cases h1 : t.val = 1
            · have ht : t = ⟨1, by omega⟩ := Fin.ext h1; rw [ht]; simp
            · by_cases hkm1 : t.val = k - 1
              · have ht : t = ⟨k - 1, by omega⟩ := Fin.ext hkm1
                rw [ht]; simp [show k - 1 ≠ 1 by omega]
              · by_cases h0 : t.val = 0
                · have ht : t = ⟨0, by omega⟩ := Fin.ext h0
                  rw [ht, h0v]; simp [show (0 : ℕ) ≠ k - 1 by omega]
                · by_cases h2 : t.val = 2
                  · have ht : t = ⟨2, by omega⟩ := Fin.ext h2
                    rw [ht, h2v]; simp [show (2 : ℕ) ≠ k - 1 by omega]
                  · by_cases hkm2' : t.val = k - 2
                    · have ht : t = ⟨k - 2, by omega⟩ := Fin.ext hkm2'
                      rw [ht, hkm2]; simp [show k - 2 ≠ 1 by omega, show k - 2 ≠ k - 1 by omega]
                    · simp only [h1, hkm1, h0, h2, hkm2', or_self, ↓reduceIte]
                      exact (hrun t (by omega) (by omega)).symm
          right_inv := by
            rintro ⟨a, b, c⟩
            refine Prod.ext (by simp) (Prod.ext ?_ ?_)
            · simp [show k - 1 ≠ 1 by omega]
            · simp [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
                show (3 : ℕ) ≠ k - 2 by omega, show (3 : ℕ) ≠ k - 1 by omega] }
      have hc := Fintype.card_congr e
      rw [Fintype.card_coe, Fintype.card_prod, Fintype.card_prod, ZMod.card] at hc
      exact hc
    · intro hmem
      have h0 := ((hK_iff _).mp hmem).1
      simp at h0

end PEqualNP.Outside.L_meta_25860_aux

open PEqualNP.Outside.L_meta_25860_aux

theorem PEqualNP.Outside.L_meta_25860 :
    ∀ (k d : ℕ) (hk : 0 < k), 11 ≤ k → Odd k → k % 3 ≠ 0 → (d = 1 ∨ d = 2) →
      let F := ZMod 2
      let W := Fin k → F
      let ix := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
      let rot := fun (n : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - n % k))
      let mix := fun (x : W) (i : Fin k) =>
        x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k))
      let layer := fun (x : W) (i : Fin k) =>
        mix x i + (1 + mix x (ix (i.val + 1))) * mix x (ix (i.val + 2))
      ∀ (start : ℕ) (feed : ℕ → ℕ) (c : ℕ → W),
        let state := fun (sched : ℕ → W) (name key : W) (t : ℕ) =>
          Nat.rec (motive := fun _ => W) (rot start key + name) (fun j x => layer x + rot (feed j) key + sched j) t
        let ones : W := fun _ => 1
        let hole := fun (i j : Fin k) => if j = i then (0 : F) else 1
        let diff := fun (nm w v : W) (j : ℕ) => state c nm (w + v) j - state c nm w j
        let pairs := fun (t : ℕ) (v : W) (i : Fin k) (z : W) =>
          (Finset.univ : Finset (W × W)).filter (fun nw =>
            diff nw.1 nw.2 v t = ones ∧ diff nw.1 nw.2 v (t + 1) = hole i ∧
            diff nw.1 nw.2 v (t + 2) = z)
        let free : ℕ := if d = 1 then 2 else 3
        let cap : ℕ := 2 ^ (free + 1)
        (∀ t v i z, ((pairs t v i z).image Prod.snd).card ≤ cap) ∧
        (∀ i, (Finset.univ.filter (fun z => (pairs 0 ones i z).Nonempty)).card = 2 ^ (k - free) ∧
          ∀ z, (pairs 0 ones i z).Nonempty →
            (pairs 0 ones i z).card = cap ∧ ((pairs 0 ones i z).image Prod.snd).card = cap) := by
  intro k d hk hk11 hkodd hk3 hd F W ix rot mix layer start feed c state
    ones hole diff pairs free cap
  have hd_mod : d % k = d := Nat.mod_eq_of_lt (by omega)
  have hrot_add : ∀ (m : ℕ) (x y : W), rot m (x + y) = rot m x + rot m y := by
    intro m x y; funext i; rfl
  have hrot_ones : ∀ m : ℕ, rot m ones = ones := by
    intro m; funext i; rfl
  have hrot_inv : ∀ (m : ℕ) (z : W), rot (k - m % k) (rot m z) = z := by
    intro m z; funext i
    change z ⟨((i.val + k - (k - m % k) % k) % k + k - m % k) % k, _⟩ = z i
    congr 1; exact Fin.ext (rot_inv_idx hk m i.val i.isLt)
  have hrot_inv' : ∀ (m : ℕ) (z : W), rot m (rot (k - m % k) z) = z := by
    intro m z; funext i
    change z ⟨((i.val + k - m % k) % k + k - (k - m % k) % k) % k, _⟩ = z i
    congr 1; exact Fin.ext (rot_inv_idx' hk m i.val i.isLt)
  have hmix_add : ∀ x y : W, mix (x + y) = mix x + mix y := by
    intro x y; funext i
    change (x i + y i) + (x (ix (i.val + d)) + y (ix (i.val + d))) +
        (x (ix (i.val + k - d % k)) + y (ix (i.val + k - d % k))) =
      (x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k))) +
        (y i + y (ix (i.val + d)) + y (ix (i.val + k - d % k)))
    ring
  have hmix_add_at : ∀ (x y : W) (j : Fin k), mix (x + y) j = mix x j + mix y j :=
    fun x y j => congrFun (hmix_add x y) j
  have hmix_zero : mix 0 = 0 := by
    funext i; change (0 : F) + 0 + 0 = 0; decide
  have hmix_ones : mix ones = ones := by
    funext i; change (1 : F) + 1 + 1 = 1; decide
  have hlayer_ones : layer ones = ones := by
    funext i
    change mix ones i + (1 + mix ones (ix (i.val + 1))) * mix ones (ix (i.val + 2)) = 1
    rw [hmix_ones]
    change (1 : F) + (1 + 1) * 1 = 1
    decide
  let polar : W → W → W := fun x y i =>
    mix x (ix (i.val + 1)) * mix y (ix (i.val + 2)) + mix x (ix (i.val + 2)) * mix y (ix (i.val + 1))
  have hpolar_add_left : ∀ x y z : W, polar (x + y) z = polar x z + polar y z := by
    intro x y z; funext i
    change mix (x + y) (ix (i.val + 1)) * mix z (ix (i.val + 2)) +
        mix (x + y) (ix (i.val + 2)) * mix z (ix (i.val + 1)) =
      (mix x (ix (i.val + 1)) * mix z (ix (i.val + 2)) +
        mix x (ix (i.val + 2)) * mix z (ix (i.val + 1))) +
      (mix y (ix (i.val + 1)) * mix z (ix (i.val + 2)) +
        mix y (ix (i.val + 2)) * mix z (ix (i.val + 1)))
    simp only [hmix_add_at]
    ring
  have hlayer_diff : ∀ z u : W, layer (z + u) - layer z = layer u + polar z u := by
    intro z u; funext i
    change (mix (z + u) i + (1 + mix (z + u) (ix (i.val + 1))) * mix (z + u) (ix (i.val + 2))) -
        (mix z i + (1 + mix z (ix (i.val + 1))) * mix z (ix (i.val + 2))) =
      (mix u i + (1 + mix u (ix (i.val + 1))) * mix u (ix (i.val + 2))) +
      (mix z (ix (i.val + 1)) * mix u (ix (i.val + 2)) +
        mix z (ix (i.val + 2)) * mix u (ix (i.val + 1)))
    simp only [hmix_add_at]
    ring
  -- Step 1: mix is bijective
  have hmix_bij : Function.Bijective mix := by
    rw [← Finite.injective_iff_bijective]
    intro x y hxy
    have hker : mix (x + y) = 0 := by rw [hmix_add, hxy, vec_add_self]
    suffices h0 : ∀ u : W, mix u = 0 → u = 0 by
      exact ((vec_add_eq_zero_iff x y).mp (h0 (x + y) hker)).symm
    intro u hu
    have hstep : ∀ n : ℕ, u (ix (n + 2 * d)) = u (ix n) + u (ix (n + d)) := by
      intro n
      have h1 := congrFun hu (ix (n + d))
      change u (ix (n + d)) + u (ix ((n + d) % k + d)) + u (ix ((n + d) % k + k - d % k)) = 0 at h1
      have ha : ix ((n + d) % k + d) = ix (n + 2 * d) := by
        apply Fin.ext; dsimp only [ix]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; congr 1; omega
      have hb : ix ((n + d) % k + k - d % k) = ix n := by
        apply Fin.ext; dsimp only [ix]; rw [hd_mod]
        have hsub : (n + d) % k + k - d = (n + d) % k + (k - d) := by omega
        rw [hsub, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hadd : n + d + (k - d) = n + k := by omega
        rw [hadd, Nat.add_mod_right]
      rw [ha, hb] at h1
      have hadd := congrArg (fun z => z + u (ix (n + 2 * d))) h1
      rw [zero_add] at hadd
      calc
        u (ix (n + 2 * d)) =
            u (ix (n + d)) + u (ix (n + 2 * d)) + u (ix n) + u (ix (n + 2 * d)) := by
          rw [hadd]
        _ = u (ix n) + u (ix (n + d)) + (u (ix (n + 2 * d)) + u (ix (n + 2 * d))) := by ring
        _ = u (ix n) + u (ix (n + d)) := by rw [zmod2_add_self, add_zero]
    have hper3 : ∀ n : ℕ, u (ix (n + 3 * d)) = u (ix n) := by
      intro n
      have h1 := hstep (n + d)
      have h2 := hstep n
      have ha : n + d + 2 * d = n + 3 * d := by omega
      have hb : n + d + d = n + 2 * d := by omega
      rw [ha, hb, h2] at h1
      calc
        u (ix (n + 3 * d)) = u (ix (n + d)) + (u (ix n) + u (ix (n + d))) := h1
        _ = u (ix n) + (u (ix (n + d)) + u (ix (n + d))) := by ring
        _ = u (ix n) := by rw [zmod2_add_self, add_zero]
    have hperM : ∀ (r n : ℕ), u (ix (n + r * (3 * d))) = u (ix n) := by
      intro r
      induction r with
      | zero => intro n; simp
      | succ r ih =>
        intro n
        have ha : n + (r + 1) * (3 * d) = (n + r * (3 * d)) + 3 * d := by ring
        rw [ha, hper3, ih]
    have hcop3 : Nat.Coprime 3 k :=
      (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr (fun hdvd => hk3 (Nat.mod_eq_zero_of_dvd hdvd))
    have hcop2 : Nat.Coprime 2 k := by
      rcases hkodd with ⟨q, hq⟩
      exact (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr (fun ⟨r, hr⟩ => by omega)
    have hcop3d : Nat.Coprime (3 * d) k := by
      rcases hd with rfl | rfl
      · simpa using hcop3
      · exact hcop3.mul_left hcop2
    obtain ⟨m0, hm0⟩ := exists_mul_mod_eq_one (by omega : 2 ≤ k) hcop3d
    have hstep1 : ∀ n : ℕ, u (ix (n + 1)) = u (ix n) := by
      intro n
      have heq : ix (n + 1) = ix (n + m0 * (3 * d)) := by
        apply Fin.ext; dsimp only [ix]
        rw [Nat.add_mod, Nat.add_mod n (m0 * (3 * d)), hm0, Nat.mod_eq_of_lt (by omega : 1 < k)]
      rw [heq, hperM]
    have hconst : ∀ n : ℕ, u (ix n) = u (ix 0) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [hstep1, ih]
    have hu0 : u (ix 0) = 0 := by
      have h := congrFun hu (ix 0)
      change u (ix 0) + u (ix (0 % k + d)) + u (ix (0 % k + k - d % k)) = 0 at h
      rw [hconst (0 % k + d), hconst (0 % k + k - d % k)] at h
      calc
        u (ix 0) = u (ix 0) + (u (ix 0) + u (ix 0)) := by rw [zmod2_add_self, add_zero]
        _ = u (ix 0) + u (ix 0) + u (ix 0) := by ring
        _ = 0 := h
    funext i
    have hi : ix i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [← hi, hconst, hu0]
    rfl
  -- Step 2: Kernel and image of polar · ones
  have hker_ones :
      (Finset.univ : Finset W).filter (fun x => polar x ones = 0) = {0, ones} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have hstep : ∀ n : ℕ, mix x (ix (n + 1)) = mix x (ix n) := by
        intro n
        have h1 := congrFun h (ix (n + k - 1))
        change mix x (ix ((n + k - 1) % k + 1)) * mix ones (ix ((n + k - 1) % k + 2)) +
            mix x (ix ((n + k - 1) % k + 2)) * mix ones (ix ((n + k - 1) % k + 1)) = 0 at h1
        rw [hmix_ones] at h1
        change mix x (ix ((n + k - 1) % k + 1)) * 1 + mix x (ix ((n + k - 1) % k + 2)) * 1 = 0 at h1
        rw [mul_one, mul_one] at h1
        have ha : ix ((n + k - 1) % k + 1) = ix n := by
          apply Fin.ext; dsimp only [ix]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have : n + k - 1 + 1 = n + k := by omega
          rw [this, Nat.add_mod_right]
        have hb : ix ((n + k - 1) % k + 2) = ix (n + 1) := by
          apply Fin.ext; dsimp only [ix]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have : n + k - 1 + 2 = (n + 1) + k := by omega
          rw [this, Nat.add_mod_right]
        rw [ha, hb] at h1
        have hadd := congrArg (fun z => mix x (ix n) + z) h1
        rw [add_zero, ← add_assoc, zmod2_add_self, zero_add] at hadd
        exact hadd
      have hconst : ∀ n : ℕ, mix x (ix n) = mix x (ix 0) := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [hstep, ih]
      have hcases : mix x (ix 0) = 0 ∨ mix x (ix 0) = 1 := by
        generalize mix x (ix 0) = z
        fin_cases z
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hcases with hc0 | hc1
      · left
        apply hmix_bij.1
        rw [hmix_zero]
        funext i
        have hi : ix i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
        rw [← hi, hconst, hc0]; rfl
      · right
        apply hmix_bij.1
        rw [hmix_ones]
        funext i
        have hi : ix i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
        rw [← hi, hconst, hc1]
    · rintro (rfl | rfl)
      · funext i
        change mix 0 (ix (i.val + 1)) * mix ones (ix (i.val + 2)) +
          mix 0 (ix (i.val + 2)) * mix ones (ix (i.val + 1)) = 0
        rw [hmix_zero]; simp
      · funext i
        change mix ones (ix (i.val + 1)) * mix ones (ix (i.val + 2)) +
          mix ones (ix (i.val + 2)) * mix ones (ix (i.val + 1)) = 0
        rw [hmix_ones]
        change (1 : F) * 1 + 1 * 1 = 0
        decide
  have h0_ne_ones : (0 : W) ≠ ones := by
    intro h
    have h0 := congrFun h ⟨0, hk⟩
    change (0 : F) = 1 at h0
    exact zero_ne_one h0
  have hker_ones_card :
      ((Finset.univ : Finset W).filter (fun x => polar x ones = 0)).card = 2 := by
    rw [hker_ones, Finset.card_pair h0_ne_ones]
  have himg_ones :
      (Finset.univ : Finset W).image (fun x => polar x ones) =
        (Finset.univ : Finset W).filter (fun w => ∑ j, w j = 0) := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      rcases Finset.mem_image.mp hw with ⟨x, _, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hterm : ∀ j : Fin k, polar x ones j =
          mix x (ix (j.val + 1)) + mix x (ix (j.val + 2)) := by
        intro j
        change mix x (ix (j.val + 1)) * mix ones (ix (j.val + 2)) +
          mix x (ix (j.val + 2)) * mix ones (ix (j.val + 1)) = _
        rw [hmix_ones]
        change mix x (ix (j.val + 1)) * 1 + mix x (ix (j.val + 2)) * 1 = _
        rw [mul_one, mul_one]
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
      have hshift : ∀ r : ℕ, ∑ j : Fin k, mix x (ix (j.val + r)) = ∑ j : Fin k, mix x j := by
        intro r
        apply Finset.sum_bij (fun j _ => ix (j.val + r))
        · intro _ _; exact Finset.mem_univ _
        · intro j1 _ j2 _ heq
          have hv := congrArg Fin.val heq
          dsimp only [ix] at hv
          have h1 : (j1.val + r + (k - r % k)) % k = (j2.val + r + (k - r % k)) % k := by
            rw [Nat.add_mod, hv, ← Nat.add_mod]
          have hr : r % k < k := Nat.mod_lt r hk
          have hmul_k : r + (k - r % k) = (r / k + 1) * k := by
            have hdm : k * (r / k) + r % k = r := Nat.div_add_mod r k
            have hle : r % k ≤ k := le_of_lt hr
            zify [hle] at hdm ⊢
            linarith
          have h2 : ∀ a : Fin k, (a.val + r + (k - r % k)) % k = a.val := by
            intro a
            rw [Nat.add_assoc, hmul_k, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]
          rw [h2 j1, h2 j2] at h1
          exact Fin.ext h1
        · intro j _
          refine ⟨ix (j.val + k - r % k), Finset.mem_univ _, ?_⟩
          apply Fin.ext; dsimp only [ix]
          have hr : r % k < k := Nat.mod_lt r hk
          have hmul_k : (k - r % k) + r = (r / k + 1) * k := by
            have hdm : k * (r / k) + r % k = r := Nat.div_add_mod r k
            have hle : r % k ≤ k := le_of_lt hr
            zify [hle] at hdm ⊢
            linarith
          have hsub : (j.val + k - r % k) % k + r = (j.val + (k - r % k)) % k + r := by
            congr 2; omega
          rw [hsub, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc, hmul_k,
            Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
        · intro _ _; rfl
      rw [hshift 1, hshift 2, zmod2_add_self]
    · have h1 := card_image_mul_ker (fun x => polar x ones) (fun x y => hpolar_add_left x y ones)
      rw [hker_ones_card] at h1
      rw [card_sum_zero hk]
      have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
        rw [← Nat.pow_succ]; congr 1; omega
      have hcard_eq : ((Finset.univ : Finset W).image (fun x => polar x ones)).card = 2 ^ (k - 1) :=
        Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2) (by rw [h1, hpow])
      exact le_of_eq hcard_eq.symm
  have hhole_in_img : ∀ i : Fin k, hole i ∈ (Finset.univ : Finset W).image (fun x => polar x ones) := by
    intro i
    rw [himg_ones]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hi0 : hole i i = 0 := by simp [hole]
    have hrest : ∑ x ∈ Finset.univ.erase i, hole i x = ∑ _x ∈ Finset.univ.erase i, (1 : F) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hne : x ≠ i := (Finset.mem_erase.mp hx).1
      simp [hole, hne]
    rw [hi0, zero_add, hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rcases hkodd with ⟨q, hq⟩
    have h2q : k - 1 = 2 * q := by omega
    rw [h2q]
    push_cast
    have h2 : (2 : F) = 0 := by decide
    rw [h2, zero_mul]
  -- Step 3: Kernel of polar · (hole i) has exact card 2^free and excludes unit i
  let unit : Fin k → W := fun i j => if j = i then 1 else 0
  have hhole_eq : ∀ i : Fin k, hole i = ones + unit i := by
    intro i; funext j
    change hole i j = ones j + unit i j
    dsimp only [hole, ones, unit]
    by_cases hj : j = i
    · simp only [hj, ↓reduceIte]; decide
    · simp only [hj, ↓reduceIte, add_zero]
  have hker_hole : ∀ i : Fin k,
      ((Finset.univ : Finset W).filter (fun y => polar y (hole i) = 0)).card = 2 ^ free ∧
      polar (unit i) (hole i) ≠ 0 := by
    intro i
    let pos : Fin k → Fin k := fun t => ix (i.val + t.val)
    have hpos_bij : Function.Bijective pos := by
      rw [← Finite.injective_iff_bijective]
      intro t1 t2 heq
      have hv := congrArg Fin.val heq
      dsimp only [pos, ix] at hv
      have h1 : (i.val + t1.val + (k - i.val)) % k = (i.val + t2.val + (k - i.val)) % k := by
        rw [Nat.add_mod, hv, ← Nat.add_mod]
      have h2 : ∀ t : Fin k, (i.val + t.val + (k - i.val)) % k = t.val := by
        intro t
        have : i.val + t.val + (k - i.val) = t.val + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt t.isLt]
      rw [h2 t1, h2 t2] at h1
      exact Fin.ext h1
    let posEquiv : Fin k ≃ Fin k := Equiv.ofBijective pos hpos_bij
    have hmix_unit_pos : ∀ t : Fin k,
        mix (unit i) (pos t) = if t.val = 0 ∨ t.val = d ∨ t.val = k - d then 1 else 0 := by
      intro t
      change unit i (pos t) + unit i (ix ((pos t).val + d)) +
          unit i (ix ((pos t).val + k - d % k)) = _
      have ha : ∀ u : Fin k, pos u = i ↔ u.val = 0 := by
        intro u
        constructor
        · intro h
          have hv := congrArg Fin.val h
          dsimp only [pos, ix] at hv
          have h1 : ((i.val + u.val) % k + (k - i.val)) % k = (i.val + (k - i.val)) % k := by
            rw [hv]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show i.val + u.val + (k - i.val) = u.val + k by omega,
            show i.val + (k - i.val) = k by omega, Nat.add_mod_right, Nat.mod_self,
            Nat.mod_eq_of_lt u.isLt] at h1
          exact h1
        · intro h
          apply Fin.ext; dsimp only [pos, ix]; rw [h, add_zero, Nat.mod_eq_of_lt i.isLt]
      have hb : ix ((pos t).val + d) = i ↔ t.val = k - d := by
        have hval : ix ((pos t).val + d) = pos ⟨(t.val + d) % k, Nat.mod_lt _ hk⟩ := by
          apply Fin.ext; dsimp only [pos, ix]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            Nat.add_mod i.val ((t.val + d) % k), Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
        rw [hval, ha]
        dsimp only
        constructor
        · intro h
          have h1 : t.val + d = k := by
            have hdlt : d < k := by omega
            have htlt : t.val < k := t.isLt
            have h0 : t.val + d < 2 * k := by omega
            by_cases hlt : t.val + d < k
            · rw [Nat.mod_eq_of_lt hlt] at h; omega
            · have : (t.val + d) % k = t.val + d - k := by
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
              omega
          omega
        · intro h
          rw [h, show k - d + d = k by omega, Nat.mod_self]
      have hc : ix ((pos t).val + k - d % k) = i ↔ t.val = d := by
        have hval : ix ((pos t).val + k - d % k) =
            pos ⟨(t.val + k - d) % k, Nat.mod_lt _ hk⟩ := by
          apply Fin.ext; dsimp only [pos, ix]; rw [hd_mod]
          have h1 : (i.val + t.val) % k + k - d = (i.val + t.val) % k + (k - d) := by omega
          have h2 : t.val + k - d = t.val + (k - d) := by omega
          rw [h1, h2, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            Nat.add_mod i.val ((t.val + (k - d)) % k), Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
        rw [hval, ha]
        dsimp only
        constructor
        · intro h
          have htlt : t.val < k := t.isLt
          by_cases hlt : t.val < d
          · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
          · have : (t.val + k - d) % k = t.val - d := by
              rw [show t.val + k - d = (t.val - d) + k by omega, Nat.add_mod_right,
                Nat.mod_eq_of_lt (by omega)]
            omega
        · intro h
          rw [h, show d + k - d = k by omega, Nat.mod_self]
      dsimp only [unit]
      by_cases h0 : t.val = 0
      · have hnb : ¬ ix ((pos t).val + d) = i := fun h => by have := hb.mp h; omega
        have hnc : ¬ ix ((pos t).val + k - d % k) = i := fun h => by have := hc.mp h; omega
        rw [show (if pos t = i then (1 : F) else 0) = 1 from by simp [(ha t).mpr h0],
          show (if ix ((pos t).val + d) = i then (1 : F) else 0) = 0 from by simp [hnb],
          show (if ix ((pos t).val + k - d % k) = i then (1 : F) else 0) = 0 from by simp [hnc]]
        simp [h0]
      · by_cases hd' : t.val = d
        · have hna : ¬ pos t = i := fun h => h0 ((ha t).mp h)
          have hnb : ¬ ix ((pos t).val + d) = i := fun h => by have := hb.mp h; omega
          rw [show (if pos t = i then (1 : F) else 0) = 0 from by simp [hna],
            show (if ix ((pos t).val + d) = i then (1 : F) else 0) = 0 from by simp [hnb],
            show (if ix ((pos t).val + k - d % k) = i then (1 : F) else 0) = 1 from by simp [hc.mpr hd']]
          simp [hd']
        · by_cases hkd : t.val = k - d
          · have hna : ¬ pos t = i := fun h => h0 ((ha t).mp h)
            have hnc : ¬ ix ((pos t).val + k - d % k) = i := fun h => by have := hc.mp h; omega
            rw [show (if pos t = i then (1 : F) else 0) = 0 from by simp [hna],
              show (if ix ((pos t).val + d) = i then (1 : F) else 0) = 1 from by simp [hb.mpr hkd],
              show (if ix ((pos t).val + k - d % k) = i then (1 : F) else 0) = 0 from by simp [hnc]]
            simp [hkd]
          · have hna : ¬ pos t = i := fun h => h0 ((ha t).mp h)
            have hnb : ¬ ix ((pos t).val + d) = i := fun h => hkd (hb.mp h)
            have hnc : ¬ ix ((pos t).val + k - d % k) = i := fun h => hd' (hc.mp h)
            rw [show (if pos t = i then (1 : F) else 0) = 0 from by simp [hna],
              show (if ix ((pos t).val + d) = i then (1 : F) else 0) = 0 from by simp [hnb],
              show (if ix ((pos t).val + k - d % k) = i then (1 : F) else 0) = 0 from by simp [hnc]]
            simp [h0, hd', hkd]
    have hmix_hole_pos : ∀ t : Fin k,
        mix (hole i) (pos t) = if t.val = 0 ∨ t.val = d ∨ t.val = k - d then 0 else 1 := by
      intro t
      rw [hhole_eq i, hmix_add_at, hmix_ones, hmix_unit_pos t]
      split_ifs <;> decide
    let m : Fin k → ZMod 2 := fun t => if t.val = 0 ∨ t.val = d ∨ t.val = k - d then 0 else 1
    let Ku : Finset (Fin k → ZMod 2) := (Finset.univ : Finset (Fin k → ZMod 2)).filter (fun v =>
      ∀ t : Fin k,
        let t1 : Fin k := ⟨(t.val + 1) % k, Nat.mod_lt _ hk⟩
        v t * m t1 + v t1 * m t = 0)
    have hKu := ker_hole_u_card hk11 hd
    let mixEquiv : W ≃ W := Equiv.ofBijective mix hmix_bij
    let coordY : W ≃ (Fin k → ZMod 2) :=
      { toFun := fun y t => mix y (pos t)
        invFun := fun v => mixEquiv.symm (fun j => v (posEquiv.symm j))
        left_inv := fun y => by
          apply mixEquiv.injective
          rw [mixEquiv.apply_symm_apply]
          funext j
          change mix y (pos (posEquiv.symm j)) = mix y j
          rw [show pos (posEquiv.symm j) = j from posEquiv.apply_symm_apply j]
        right_inv := fun v => by
          funext t
          change mixEquiv (mixEquiv.symm (fun j => v (posEquiv.symm j))) (pos t) = v t
          rw [mixEquiv.apply_symm_apply]
          change v (posEquiv.symm (posEquiv t)) = v t
          rw [posEquiv.symm_apply_apply] }
    have hmem_iff : ∀ y : W, polar y (hole i) = 0 ↔ coordY y ∈ Ku := by
      intro y
      simp only [Ku, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h t
        have ht1 : ix ((pos t).val + 1) = pos ⟨(t.val + 1) % k, Nat.mod_lt _ hk⟩ := by
          apply Fin.ext; dsimp only [pos, ix]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            Nat.add_mod i.val ((t.val + 1) % k), Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
        let j0 : Fin k := ix ((pos t).val + k - 1)
        have hj1 : ix (j0.val + 1) = pos t := by
          apply Fin.ext; dsimp only [j0, ix]
          have h1 : ((pos t).val + k - 1) % k + 1 = ((pos t).val + (k - 1)) % k + 1 := by
            congr 2; omega
          rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show (pos t).val + (k - 1) + 1 = (pos t).val + k by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (pos t).isLt]
        have hj2 : ix (j0.val + 2) = pos ⟨(t.val + 1) % k, Nat.mod_lt _ hk⟩ := by
          rw [← ht1]
          apply Fin.ext; dsimp only [j0, ix]
          have h1 : ((pos t).val + k - 1) % k + 2 = ((pos t).val + (k - 1)) % k + 2 := by
            congr 2; omega
          rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show (pos t).val + (k - 1) + 2 = ((pos t).val + 1) + k by omega,
            Nat.add_mod_right]
        have hj := congrFun h j0
        change mix y (ix (j0.val + 1)) * mix (hole i) (ix (j0.val + 2)) +
            mix y (ix (j0.val + 2)) * mix (hole i) (ix (j0.val + 1)) = 0 at hj
        rw [hj1, hj2, hmix_hole_pos, hmix_hole_pos] at hj
        exact hj
      · intro h
        funext j
        let t : Fin k := posEquiv.symm (ix (j.val + 1))
        have ht0 : pos t = ix (j.val + 1) := posEquiv.apply_symm_apply _
        have ht1 : pos ⟨(t.val + 1) % k, Nat.mod_lt _ hk⟩ = ix (j.val + 2) := by
          have ha : ix ((pos t).val + 1) = pos ⟨(t.val + 1) % k, Nat.mod_lt _ hk⟩ := by
            apply Fin.ext; dsimp only [pos, ix]
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
              Nat.add_mod i.val ((t.val + 1) % k), Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
          rw [← ha, ht0]
          apply Fin.ext; dsimp only [ix]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have ht := h t
        change mix y (pos t) * m ⟨(t.val + 1) % k, Nat.mod_lt _ hk⟩ +
            mix y (pos ⟨(t.val + 1) % k, Nat.mod_lt _ hk⟩) * m t = 0 at ht
        have hm_eq : ∀ u : Fin k, m u = mix (hole i) (pos u) := fun u => (hmix_hole_pos u).symm
        rw [hm_eq, hm_eq, ht0, ht1] at ht
        exact ht
    refine ⟨?_, ?_⟩
    · rw [← hKu.1]
      apply Finset.card_bij (fun y _ => coordY y)
      · intro y hy
        exact (hmem_iff y).mp (Finset.mem_filter.mp hy).2
      · intro y1 _ y2 _ heq; exact coordY.injective heq
      · intro v hv
        refine ⟨coordY.symm v, ?_, coordY.apply_symm_apply v⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hmem_iff, coordY.apply_symm_apply]
        exact hv
    · intro hzero
      have hmem : coordY (unit i) ∈ Ku := (hmem_iff (unit i)).mp hzero
      have hEq : coordY (unit i) =
          (fun t : Fin k => if t.val = 0 ∨ t.val = d ∨ t.val = k - d then (1 : ZMod 2) else 0) :=
        funext hmix_unit_pos
      rw [hEq] at hmem
      exact hKu.2 hmem
  -- Step 4: Difference recurrence for general t, v
  have hdiff_step : ∀ (nm w v : W) (j : ℕ),
      diff nm w v (j + 1) =
        layer (state c nm w j + diff nm w v j) - layer (state c nm w j) + rot (feed j) v := by
    intro nm w v j
    have hst : state c nm (w + v) j = state c nm w j + diff nm w v j := by
      dsimp only [diff]
      rw [vec_sub_eq_add]
      calc
        state c nm (w + v) j =
            state c nm (w + v) j + (state c nm w j + state c nm w j) := by
          rw [vec_add_self, add_zero]
        _ = state c nm w j + (state c nm (w + v) j + state c nm w j) := by abel
    change (layer (state c nm (w + v) j) + rot (feed j) (w + v) + c j) -
        (layer (state c nm w j) + rot (feed j) w + c j) = _
    rw [hst, hrot_add, vec_sub_eq_add, vec_sub_eq_add]
    calc
      layer (state c nm w j + diff nm w v j) + (rot (feed j) w + rot (feed j) v) + c j +
          (layer (state c nm w j) + rot (feed j) w + c j)
        = layer (state c nm w j + diff nm w v j) + layer (state c nm w j) + rot (feed j) v +
          (rot (feed j) w + rot (feed j) w) + (c j + c j) := by abel
      _ = layer (state c nm w j + diff nm w v j) + layer (state c nm w j) + rot (feed j) v := by
        rw [vec_add_self, vec_add_self, add_zero, add_zero]
  -- Conjunct 1: ∀ t v i z, ((pairs t v i z).image Prod.snd).card ≤ cap
  have hconj1 : ∀ t v i z, ((pairs t v i z).image Prod.snd).card ≤ cap := by
    intro t v i z
    let Sx : Finset W := (Finset.univ : Finset W).filter (fun x =>
      polar x ones = hole i + ones + rot (feed t) v)
    let Sy : Finset W := (Finset.univ : Finset W).filter (fun y =>
      polar y (hole i) = z + layer (hole i) + rot (feed (t + 1)) v)
    let recW : W × W → W := fun xy => rot (k - (feed t) % k) (xy.2 + layer xy.1 + c t)
    have hsub : (pairs t v i z).image Prod.snd ⊆ (Sx ×ˢ Sy).image recW := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨⟨nm, w'⟩, hmem, rfl⟩
      simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rcases hmem with ⟨hd0, hd1, hd2⟩
      set x := state c nm w' t
      set y := state c nm w' (t + 1)
      have hx : x ∈ Sx := by
        simp only [Sx, Finset.mem_filter, Finset.mem_univ, true_and]
        have h1 := hdiff_step nm w' v t
        rw [hd0, hd1, hlayer_diff, hlayer_ones] at h1
        have hadd := congrArg (fun u => u + ones + rot (feed t) v) h1
        calc
          polar x ones =
              (ones + polar x ones + rot (feed t) v) + ones + rot (feed t) v := by
            calc
              polar x ones = polar x ones + (ones + ones) + (rot (feed t) v + rot (feed t) v) := by
                rw [vec_add_self, vec_add_self, add_zero, add_zero]
              _ = (ones + polar x ones + rot (feed t) v) + ones + rot (feed t) v := by abel
          _ = hole i + ones + rot (feed t) v := by rw [← hadd]
      have hy : y ∈ Sy := by
        simp only [Sy, Finset.mem_filter, Finset.mem_univ, true_and]
        have h2 := hdiff_step nm w' v (t + 1)
        rw [hd1, hd2, hlayer_diff] at h2
        have hadd := congrArg (fun u => u + layer (hole i) + rot (feed (t + 1)) v) h2
        calc
          polar y (hole i) =
              (layer (hole i) + polar y (hole i) + rot (feed (t + 1)) v) +
                layer (hole i) + rot (feed (t + 1)) v := by
            calc
              polar y (hole i) =
                  polar y (hole i) + (layer (hole i) + layer (hole i)) +
                  (rot (feed (t + 1)) v + rot (feed (t + 1)) v) := by
                rw [vec_add_self, vec_add_self, add_zero, add_zero]
              _ = _ := by abel
          _ = z + layer (hole i) + rot (feed (t + 1)) v := by rw [← hadd]
      have hrec : recW (x, y) = w' := by
        dsimp only [recW]
        have hy_def : y = layer x + rot (feed t) w' + c t := rfl
        have hsum : y + layer x + c t = rot (feed t) w' := by
          rw [hy_def]
          calc
            layer x + rot (feed t) w' + c t + layer x + c t
              = rot (feed t) w' + (layer x + layer x) + (c t + c t) := by abel
            _ = rot (feed t) w' := by rw [vec_add_self, vec_add_self, add_zero, add_zero]
        rw [hsum, hrot_inv]
      exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, hrec⟩
    have hSx_le : Sx.card ≤ 2 := by
      by_cases hne : Sx.Nonempty
      · rw [card_fiber_of_add (fun x => polar x ones) (fun a b => hpolar_add_left a b ones) _ hne,
          hker_ones_card]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; omega
    have hSy_le : Sy.card ≤ 2 ^ free := by
      by_cases hne : Sy.Nonempty
      · rw [card_fiber_of_add (fun y => polar y (hole i)) (fun a b => hpolar_add_left a b (hole i)) _ hne,
          (hker_hole i).1]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; exact Nat.zero_le _
    calc
      ((pairs t v i z).image Prod.snd).card ≤ ((Sx ×ˢ Sy).image recW).card :=
        Finset.card_le_card hsub
      _ ≤ (Sx ×ˢ Sy).card := Finset.card_image_le
      _ = Sx.card * Sy.card := Finset.card_product Sx Sy
      _ ≤ 2 * 2 ^ free := Nat.mul_le_mul hSx_le hSy_le
      _ = cap := by dsimp only [cap]; rw [Nat.pow_succ']
  refine ⟨hconj1, ?_⟩
  -- Conjunct 2: Exact counts at t = 0, v = ones
  intro i
  let inv0 : W → W := rot (k - (feed 0) % k)
  let coordEquiv : (W × W) ≃ (W × W) :=
    { toFun := fun nw =>
        let x := rot start nw.2 + nw.1
        (x, layer x + rot (feed 0) nw.2 + c 0)
      invFun := fun xy =>
        let w := inv0 (xy.2 + layer xy.1 + c 0)
        (xy.1 + rot start w, w)
      left_inv := by
        rintro ⟨nm, w⟩
        dsimp only
        have hsum : layer (rot start w + nm) + rot (feed 0) w + c 0 +
            layer (rot start w + nm) + c 0 = rot (feed 0) w := by
          calc
            layer (rot start w + nm) + rot (feed 0) w + c 0 + layer (rot start w + nm) + c 0
              = rot (feed 0) w + (layer (rot start w + nm) + layer (rot start w + nm)) +
                (c 0 + c 0) := by abel
            _ = rot (feed 0) w := by rw [vec_add_self, vec_add_self, add_zero, add_zero]
        have hw : inv0 (layer (rot start w + nm) + rot (feed 0) w + c 0 +
            layer (rot start w + nm) + c 0) = w := by
          rw [hsum]; exact hrot_inv (feed 0) w
        apply Prod.ext
        · rw [hw]
          calc
            rot start w + nm + rot start w = nm + (rot start w + rot start w) := by abel
            _ = nm := by rw [vec_add_self, add_zero]
        · exact hw
      right_inv := by
        rintro ⟨x, y⟩
        dsimp only
        set w := inv0 (y + layer x + c 0)
        have hx : rot start w + (x + rot start w) = x := by
          calc
            rot start w + (x + rot start w) = x + (rot start w + rot start w) := by abel
            _ = x := by rw [vec_add_self, add_zero]
        have hrot0 : rot (feed 0) w = y + layer x + c 0 := hrot_inv' (feed 0) (y + layer x + c 0)
        apply Prod.ext
        · exact hx
        · rw [hx, hrot0]
          calc
            layer x + (y + layer x + c 0) + c 0
              = y + (layer x + layer x) + (c 0 + c 0) := by abel
            _ = y := by rw [vec_add_self, vec_add_self, add_zero, add_zero] }
  let pool0 : Finset W := (Finset.univ : Finset W).filter (fun x => polar x ones = hole i)
  have hpool0_ne : pool0.Nonempty := by
    rcases Finset.mem_image.mp (hhole_in_img i) with ⟨x0, _, hx0⟩
    exact ⟨x0, Finset.mem_filter.mpr ⟨Finset.mem_univ x0, hx0⟩⟩
  have hpool0_card : pool0.card = 2 := by
    rw [card_fiber_of_add (fun x => polar x ones) (fun a b => hpolar_add_left a b ones) _ hpool0_ne,
      hker_ones_card]
  let gY : W → W := fun y => polar y (hole i) + (layer (hole i) + ones)
  have hmem_pairs0 : ∀ (z : W) (nw : W × W),
      nw ∈ pairs 0 ones i z ↔ (coordEquiv nw).1 ∈ pool0 ∧ gY (coordEquiv nw).2 = z := by
    intro z ⟨nm, w⟩
    simp only [pairs, pool0, Finset.mem_filter, Finset.mem_univ, true_and, zero_add]
    have hd0 : diff nm w ones 0 = ones := by
      change (rot start (w + ones) + nm) - (rot start w + nm) = ones
      rw [hrot_add, hrot_ones start, vec_sub_eq_add]
      calc
        rot start w + ones + nm + (rot start w + nm)
          = ones + (rot start w + rot start w) + (nm + nm) := by abel
        _ = ones := by rw [vec_add_self, vec_add_self, add_zero, add_zero]
    have hd1_eq : diff nm w ones 1 = polar (coordEquiv (nm, w)).1 ones := by
      have h1 : diff nm w ones 1 =
          layer (state c nm w 0 + diff nm w ones 0) - layer (state c nm w 0) + rot (feed 0) ones :=
        hdiff_step nm w ones 0
      rw [hd0, hlayer_diff, hlayer_ones, hrot_ones (feed 0)] at h1
      change diff nm w ones 1 = polar (state c nm w 0) ones
      rw [h1]
      calc
        ones + polar (state c nm w 0) ones + ones
          = polar (state c nm w 0) ones + (ones + ones) := by abel
        _ = polar (state c nm w 0) ones := by rw [vec_add_self, add_zero]
    constructor
    · rintro ⟨_, h1, h2⟩
      have hx : polar (coordEquiv (nm, w)).1 ones = hole i := by rw [← hd1_eq]; exact h1
      refine ⟨hx, ?_⟩
      have hstep2 : diff nm w ones 2 =
          layer (state c nm w 1 + diff nm w ones 1) - layer (state c nm w 1) + rot (feed 1) ones :=
        hdiff_step nm w ones 1
      rw [h1, h2, hlayer_diff, hrot_ones (feed 1)] at hstep2
      dsimp only [gY]
      change polar (state c nm w 1) (hole i) + (layer (hole i) + ones) = z
      rw [hstep2]
      abel
    · rintro ⟨hx, hy⟩
      have h1 : diff nm w ones 1 = hole i := by rw [hd1_eq]; exact hx
      refine ⟨hd0, h1, ?_⟩
      have hstep2 : diff nm w ones 2 =
          layer (state c nm w 1 + diff nm w ones 1) - layer (state c nm w 1) + rot (feed 1) ones :=
        hdiff_step nm w ones 1
      rw [h1, hlayer_diff, hrot_ones (feed 1)] at hstep2
      rw [hstep2, ← hy]
      dsimp only [gY]
      change layer (hole i) + polar (state c nm w 1) (hole i) + ones =
        polar (state c nm w 1) (hole i) + (layer (hole i) + ones)
      abel
  have hne_iff : ∀ z : W, (pairs 0 ones i z).Nonempty ↔ z ∈ (Finset.univ : Finset W).image gY := by
    intro z
    constructor
    · rintro ⟨nw, hnw⟩
      exact Finset.mem_image.mpr ⟨(coordEquiv nw).2, Finset.mem_univ _, ((hmem_pairs0 z nw).mp hnw).2⟩
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨y, _, rfl⟩
      rcases hpool0_ne with ⟨x0, hx0⟩
      refine ⟨coordEquiv.symm (x0, y), (hmem_pairs0 (gY y) _).mpr ?_⟩
      rw [coordEquiv.apply_symm_apply]
      exact ⟨hx0, rfl⟩
  refine ⟨?_, ?_⟩
  · -- Count of nonempty z's = 2^(k - free)
    have hfilt : (Finset.univ : Finset W).filter (fun z => (pairs 0 ones i z).Nonempty) =
        (Finset.univ : Finset W).image gY := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hne_iff z
    rw [hfilt]
    have himg_eq : ((Finset.univ : Finset W).image gY).card =
        ((Finset.univ : Finset W).image (fun y => polar y (hole i))).card := by
      apply Finset.card_bij (fun z _ => z + (layer (hole i) + ones))
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨y, _, rfl⟩
        dsimp only [gY]
        rw [add_assoc, vec_add_self, add_zero]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ y)
      · intro z1 _ z2 _ heq
        have h1 := congrArg (fun u => u + (layer (hole i) + ones)) heq
        simpa [add_assoc, vec_add_self] using h1
      · intro u hu
        rcases Finset.mem_image.mp hu with ⟨y, _, rfl⟩
        refine ⟨gY y, Finset.mem_image_of_mem gY (Finset.mem_univ y), ?_⟩
        dsimp only [gY]
        rw [add_assoc, vec_add_self, add_zero]
    rw [himg_eq]
    have hmul := card_image_mul_ker (fun y => polar y (hole i))
      (fun a b => hpolar_add_left a b (hole i))
    rw [(hker_hole i).1] at hmul
    have hfree_le : free ≤ k := by
      dsimp only [free]; split_ifs <;> omega
    have hpow : 2 ^ k = 2 ^ (k - free) * 2 ^ free := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hpow] at hmul
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos free) hmul
  · -- For each nonempty z, both pairs.card = cap and (pairs.image Prod.snd).card = cap
    intro z hne
    let fibY : Finset W := (Finset.univ : Finset W).filter (fun y => gY y = z)
    have hfibY_ne : fibY.Nonempty := by
      rcases Finset.mem_image.mp ((hne_iff z).mp hne) with ⟨y, _, hy⟩
      exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩⟩
    have hfibY_card : fibY.card = 2 ^ free := by
      have hEq : fibY = (Finset.univ : Finset W).filter (fun y =>
          polar y (hole i) = z + (layer (hole i) + ones)) := by
        ext y
        simp only [fibY, Finset.mem_filter, Finset.mem_univ, true_and, gY]
        constructor
        · intro h; rw [← h, add_assoc, vec_add_self, add_zero]
        · intro h; rw [h, add_assoc, vec_add_self, add_zero]
      rw [hEq,
        card_fiber_of_add (fun y => polar y (hole i)) (fun a b => hpolar_add_left a b (hole i)) _
          (by rw [← hEq]; exact hfibY_ne),
        (hker_hole i).1]
    have hpairs_card : (pairs 0 ones i z).card = cap := by
      have hbij : (pairs 0 ones i z).card = (pool0 ×ˢ fibY).card := by
        apply Finset.card_bij (fun nw _ => coordEquiv nw)
        · intro nw hnw
          have h := (hmem_pairs0 z nw).mp hnw
          exact Finset.mem_product.mpr ⟨h.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩⟩
        · intro nw1 _ nw2 _ heq; exact coordEquiv.injective heq
        · intro xy hxy
          rcases Finset.mem_product.mp hxy with ⟨hx, hy⟩
          refine ⟨coordEquiv.symm xy, (hmem_pairs0 z _).mpr ?_, coordEquiv.apply_symm_apply xy⟩
          rw [coordEquiv.apply_symm_apply]
          exact ⟨hx, (Finset.mem_filter.mp hy).2⟩
      rw [hbij, Finset.card_product, hpool0_card, hfibY_card]
      dsimp only [cap]
      rw [Nat.pow_succ']
    refine ⟨hpairs_card, ?_⟩
    rw [Finset.card_image_of_injOn, hpairs_card]
    intro nw1 hnw1 nw2 hnw2 hw_eq
    have h1 := (hmem_pairs0 z nw1).mp hnw1
    have h2 := (hmem_pairs0 z nw2).mp hnw2
    set x1 := (coordEquiv nw1).1
    set y1 := (coordEquiv nw1).2
    set x2 := (coordEquiv nw2).1
    set y2 := (coordEquiv nw2).2
    have hx_diff : x1 + x2 = 0 ∨ x1 + x2 = ones := by
      have hp1 : polar x1 ones = hole i := (Finset.mem_filter.mp h1.1).2
      have hp2 : polar x2 ones = hole i := (Finset.mem_filter.mp h2.1).2
      have hker : polar (x1 + x2) ones = 0 := by
        rw [hpolar_add_left, hp1, hp2, vec_add_self]
      have hmem : x1 + x2 ∈ (Finset.univ : Finset W).filter (fun x => polar x ones = 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker⟩
      rw [hker_ones, Finset.mem_insert, Finset.mem_singleton] at hmem
      exact hmem
    rcases hx_diff with hx0 | hx1
    · have hxeq : x1 = x2 := ((vec_add_eq_zero_iff x1 x2).mp hx0).symm
      have hyeq : y1 = y2 := by
        change layer x1 + rot (feed 0) nw1.2 + c 0 = layer x2 + rot (feed 0) nw2.2 + c 0
        rw [hxeq, hw_eq]
      exact coordEquiv.injective (Prod.ext hxeq hyeq)
    · exfalso
      have hx2_eq : x2 = x1 + ones := by
        have hadd := congrArg (fun u => x1 + u) hx1
        rw [← add_assoc, vec_add_self, zero_add] at hadd
        exact hadd
      have hy_sum : y1 + y2 = unit i := by
        change (layer x1 + rot (feed 0) nw1.2 + c 0) + (layer x2 + rot (feed 0) nw2.2 + c 0) = unit i
        rw [hw_eq, hx2_eq]
        have hcancel :
            (layer x1 + rot (feed 0) nw2.2 + c 0) +
              (layer (x1 + ones) + rot (feed 0) nw2.2 + c 0) =
            layer (x1 + ones) - layer x1 := by
          rw [vec_sub_eq_add]
          calc
            (layer x1 + rot (feed 0) nw2.2 + c 0) +
                (layer (x1 + ones) + rot (feed 0) nw2.2 + c 0)
              = layer (x1 + ones) + layer x1 +
                (rot (feed 0) nw2.2 + rot (feed 0) nw2.2) + (c 0 + c 0) := by abel
            _ = layer (x1 + ones) + layer x1 := by
              rw [vec_add_self, vec_add_self, add_zero, add_zero]
        rw [hcancel, hlayer_diff, hlayer_ones, (Finset.mem_filter.mp h1.1).2, hhole_eq i,
          ← add_assoc, vec_add_self, zero_add]
      have hpy : polar (y1 + y2) (hole i) = 0 := by
        have hgy : polar y1 (hole i) + (layer (hole i) + ones) =
            polar y2 (hole i) + (layer (hole i) + ones) := h1.2.trans h2.2.symm
        have hpeq : polar y1 (hole i) = polar y2 (hole i) := add_right_cancel hgy
        rw [hpolar_add_left, hpeq, vec_add_self]
      rw [hy_sum] at hpy
      exact (hker_hole i).2 hpy


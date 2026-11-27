import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25651_aux

private theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

private theorem ix_val {k : ℕ} (hk : 0 < k) (s : ℕ) (hs : s < k) :
    (⟨s % k, Nat.mod_lt _ hk⟩ : Fin k).val = s :=
  Nat.mod_eq_of_lt hs

private theorem ix_pred_succ {k : ℕ} (hk : 0 < k) (l : ℕ) :
    (⟨((l + 1) % k + k - 1) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      ⟨l % k, Nat.mod_lt _ hk⟩ := by
  apply Fin.ext
  change ((l + 1) % k + k - 1) % k = l % k
  have hlt : l % k < k := Nat.mod_lt l hk
  have hdiv : k * (l / k) + l % k = l := Nat.div_add_mod l k
  by_cases h : l % k + 1 < k
  · have hl1 : l + 1 = k * (l / k) + (l % k + 1) := by omega
    have h1 : (l + 1) % k = l % k + 1 := by
      rw [hl1, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
    have h2 : (l + 1) % k + k - 1 = l % k + k := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_mod]
  · have heq : l % k + 1 = k := by omega
    have hl1 : l + 1 = k * (l / k + 1) := by
      rw [mul_add, mul_one]
      omega
    have h1 : (l + 1) % k = 0 := by
      rw [hl1, Nat.mul_mod_right]
    rw [h1, zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
    omega

private theorem ix_succ_of_lt {k : ℕ} (hk : 0 < k) (l : ℕ) (hl : l < k) :
    (⟨((⟨l % k, Nat.mod_lt _ hk⟩ : Fin k).val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      ⟨(l + 1) % k, Nat.mod_lt _ hk⟩ := by
  apply Fin.ext
  change (l % k + 1) % k = (l + 1) % k
  rw [Nat.mod_eq_of_lt hl]

private theorem mix_formula {k : ℕ} (hk : 0 < k) (name key : Fin k → ZMod 2)
    (l : ℕ) (hl2 : 2 ≤ l) (hlk : l < k) :
    let ix := fun site : ℕ => (⟨site % k, Nat.mod_lt _ hk⟩ : Fin k)
    let z := fun j : Fin k => key (ix (j.val + k - 1)) + name j
    let mix := fun i : Fin k => z i + z (ix (i.val + 1)) + z (ix (i.val + k - 1))
    mix (ix l) = key (ix (l - 2)) + key (ix (l - 1)) + key (ix l) +
      (name (ix (l - 1)) + name (ix l) + name (ix (l + 1))) := by
  intro ix z mix
  have h1 : ix ((ix l).val + k - 1) = ix (l - 1) := by
    have heq : l = (l - 1) + 1 := by omega
    conv_lhs => rw [heq]
    exact ix_pred_succ hk (l - 1)
  have h2 : ix ((ix l).val + 1) = ix (l + 1) := ix_succ_of_lt hk l hlk
  have h3 : ix ((ix (l + 1)).val + k - 1) = ix l := ix_pred_succ hk l
  have h4 : ix ((ix (l - 1)).val + k - 1) = ix (l - 2) := by
    have heq : l - 1 = (l - 2) + 1 := by omega
    conv_lhs => rw [heq]
    exact ix_pred_succ hk (l - 2)
  change z (ix l) + z (ix ((ix l).val + 1)) + z (ix ((ix l).val + k - 1)) = _
  rw [h2, h1]
  simp only [z, h1, h3, h4]
  ring

private def nameOff {k : ℕ} (hk : 0 < k) (name : Fin k → ZMod 2) (l : ℕ) : ZMod 2 :=
  let ix := fun site : ℕ => (⟨site % k, Nat.mod_lt _ hk⟩ : Fin k)
  name (ix (l - 1)) + name (ix l) + name (ix (l + 1))

private def baseRev {k m : ℕ} (hk : 0 < k) (name c : Fin k → ZMod 2)
    (ca cb cd : Fin m → ZMod 2) : ℕ → ZMod 2
  | 0 => 0
  | 1 => 0
  | r + 2 =>
    let s := 3 * m - 1 - r
    let ix := fun site : ℕ => (⟨site % k, Nat.mod_lt _ hk⟩ : Fin k)
    if h : s / 3 < m then
      let g : Fin m := ⟨s / 3, h⟩
      if s % 3 = 2 then
        baseRev hk name c ca cb cd (r + 1) + baseRev hk name c ca cb cd r +
          nameOff hk name (s + 2) + cd g
      else if s % 3 = 1 then
        1 + baseRev hk name c ca cb cd (r + 1) + baseRev hk name c ca cb cd r +
          nameOff hk name (s + 2) + cb g
      else
        baseRev hk name c ca cb cd (r + 1) +
          nameOff hk name (s + 2) + c (ix (s + 2)) + ca g
    else 0

private def encRev {n m : ℕ} (a b d : Fin m → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)) :
    ℕ → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
  | 0 => 0
  | 1 => 0
  | r + 2 =>
    let s := 3 * m - 1 - r
    if h : s / 3 < m then
      let g : Fin m := ⟨s / 3, h⟩
      if s % 3 = 2 then
        encRev a b d (r + 1) + encRev a b d r + d g
      else if s % 3 = 1 then
        encRev a b d (r + 1) + encRev a b d r + b g
      else
        encRev a b d (r + 1) + a g
    else 0

theorem main_aux (k n m : ℕ) (hk : 0 < k) (hknm : 3 * m + 2 + n ≤ k)
    (name c : Fin k → ZMod 2)
    (a b d : Fin m → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (ca cb cd : Fin m → ZMod 2) :
    let X := Fin n → ZMod 2
    let W := Fin k → ZMod 2
    let ix := fun site : ℕ => (⟨site % k, Nat.mod_lt _ hk⟩ : Fin k)
    let target := fun (x : X) (g : Fin m) =>
      a g x + ca g + (b g x + cb g) * (d g x + cd g)
    let run := fun (key : W) =>
      let z := fun j : Fin k => key (ix (j.val + k - 1)) + name j
      let mix := fun i : Fin k => z i + z (ix (i.val + 1)) + z (ix (i.val + k - 1))
      fun t : Fin k => mix t + (1 + mix (ix (t.val + 1))) * mix (ix (t.val + 2)) + key t + c t
    ∃ (base : W) (enc : X →ₗ[ZMod 2] W),
      let liftKey := fun arg : X => base + enc arg
      (∀ (z : X) (p : Fin n), liftKey z (ix (3 * m + 2 + p.val)) = z p) ∧
      (∀ (z : X) (g : Fin m), run (liftKey z) (ix (3 * g.val + 2)) = target z g) ∧
      ∀ y : Fin m → ZMod 2,
        Nat.card { key : W // key ∈ Set.range liftKey ∧
          ∀ g : Fin m, run key (ix (3 * g.val + 2)) = y g } =
        Nat.card { z : X // ∀ g : Fin m, target z g = y g } := by
  intro X W ix target run
  let B := @baseRev k m hk name c ca cb cd
  let E := @encRev n m a b d
  let base : Fin k → ZMod 2 := fun j => if j.val ≤ 3 * m + 1 then B (3 * m + 1 - j.val) else 0
  let enc : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    { toFun := fun x j =>
        if j.val ≤ 3 * m + 1 then E (3 * m + 1 - j.val) x
        else if h : 3 * m + 2 ≤ j.val ∧ j.val < 3 * m + 2 + n then
          x ⟨j.val - (3 * m + 2), by omega⟩
        else 0
      map_add' := fun x1 x2 => by
        ext j
        change (if j.val ≤ 3 * m + 1 then E (3 * m + 1 - j.val) (x1 + x2)
          else if h : 3 * m + 2 ≤ j.val ∧ j.val < 3 * m + 2 + n then
            (x1 + x2) ⟨j.val - (3 * m + 2), by omega⟩ else 0) =
          (if j.val ≤ 3 * m + 1 then E (3 * m + 1 - j.val) x1
          else if h : 3 * m + 2 ≤ j.val ∧ j.val < 3 * m + 2 + n then
            x1 ⟨j.val - (3 * m + 2), by omega⟩ else 0) +
          (if j.val ≤ 3 * m + 1 then E (3 * m + 1 - j.val) x2
          else if h : 3 * m + 2 ≤ j.val ∧ j.val < 3 * m + 2 + n then
            x2 ⟨j.val - (3 * m + 2), by omega⟩ else 0)
        by_cases h1 : j.val ≤ 3 * m + 1
        · simp [h1, map_add]
        · by_cases h2 : 3 * m + 2 ≤ j.val ∧ j.val < 3 * m + 2 + n
          · simp [h1, h2]
          · simp [h1, h2]
      map_smul' := fun r x => by
        ext j
        change (if j.val ≤ 3 * m + 1 then E (3 * m + 1 - j.val) (r • x)
          else if h : 3 * m + 2 ≤ j.val ∧ j.val < 3 * m + 2 + n then
            (r • x) ⟨j.val - (3 * m + 2), by omega⟩ else 0) =
          r * (if j.val ≤ 3 * m + 1 then E (3 * m + 1 - j.val) x
          else if h : 3 * m + 2 ≤ j.val ∧ j.val < 3 * m + 2 + n then
            x ⟨j.val - (3 * m + 2), by omega⟩ else 0)
        by_cases h1 : j.val ≤ 3 * m + 1
        · simp [h1, map_smul]
        · by_cases h2 : 3 * m + 2 ≤ j.val ∧ j.val < 3 * m + 2 + n
          · simp [h1, h2]
          · simp [h1, h2] }
  let liftKey : (Fin n → ZMod 2) → (Fin k → ZMod 2) := fun arg => base + enc arg
  have hcopy : ∀ (z : X) (p : Fin n), liftKey z (ix (3 * m + 2 + p.val)) = z p := by
    intro z p
    have hlt : 3 * m + 2 + p.val < k := by omega
    have hval : (ix (3 * m + 2 + p.val)).val = 3 * m + 2 + p.val := ix_val hk _ hlt
    have hnot : ¬ (ix (3 * m + 2 + p.val)).val ≤ 3 * m + 1 := by omega
    have hin : 3 * m + 2 ≤ (ix (3 * m + 2 + p.val)).val ∧
        (ix (3 * m + 2 + p.val)).val < 3 * m + 2 + n := by omega
    change base (ix (3 * m + 2 + p.val)) + enc z (ix (3 * m + 2 + p.val)) = z p
    simp only [base, enc, LinearMap.coe_mk, AddHom.coe_mk, hnot, ↓reduceIte,
      hin, ↓reduceDIte, zero_add]
    congr 1
    apply Fin.ext
    simp [hval]
  have hsite : ∀ (z : X) (s : ℕ), s ≤ 3 * m + 1 →
      liftKey z (ix s) = B (3 * m + 1 - s) + E (3 * m + 1 - s) z := by
    intro z s hs
    have hlt : s < k := by omega
    have hval : (ix s).val = s := ix_val hk s hlt
    change base (ix s) + enc z (ix s) = B (3 * m + 1 - s) + E (3 * m + 1 - s) z
    simp only [base, enc, LinearMap.coe_mk, AddHom.coe_mk, hval, hs, ↓reduceIte]
  have hrun : ∀ (z : X) (g : Fin m), run (liftKey z) (ix (3 * g.val + 2)) = target z g := by
    intro z g
    let t := 3 * g.val + 2
    have htk : t + 2 < k := by omega
    have hix1 : ix ((ix t).val + 1) = ix (t + 1) := ix_succ_of_lt hk t (by omega)
    have hix2 : ix ((ix t).val + 2) = ix (t + 2) := by
      apply Fin.ext
      change (t % k + 2) % k = (t + 2) % k
      rw [Nat.mod_eq_of_lt (by omega : t < k)]
    have hmix0 := mix_formula hk name (liftKey z) t (by omega) (by omega)
    have hmix1 := mix_formula hk name (liftKey z) (t + 1) (by omega) (by omega)
    have hmix2 := mix_formula hk name (liftKey z) (t + 2) (by omega) htk
    change (let z0 := fun j : Fin k => liftKey z (ix (j.val + k - 1)) + name j
      let mix := fun i : Fin k => z0 i + z0 (ix (i.val + 1)) + z0 (ix (i.val + k - 1))
      mix (ix t) + (1 + mix (ix ((ix t).val + 1))) * mix (ix ((ix t).val + 2)) +
        liftKey z (ix t) + c (ix t)) = target z g
    rw [hix1, hix2]
    dsimp only [ix] at hmix0 hmix1 hmix2 ⊢
    rw [hmix0, hmix1, hmix2]
    change (liftKey z (ix (t - 2)) + liftKey z (ix (t - 1)) + liftKey z (ix t) +
        (name (ix (t - 1)) + name (ix t) + name (ix (t + 1)))) +
      (1 + (liftKey z (ix (t + 1 - 2)) + liftKey z (ix (t + 1 - 1)) + liftKey z (ix (t + 1)) +
        (name (ix (t + 1 - 1)) + name (ix (t + 1)) + name (ix (t + 1 + 1))))) *
      (liftKey z (ix (t + 2 - 2)) + liftKey z (ix (t + 2 - 1)) + liftKey z (ix (t + 2)) +
        (name (ix (t + 2 - 1)) + name (ix (t + 2)) + name (ix (t + 2 + 1)))) +
      liftKey z (ix t) + c (ix t) = target z g
    let r0 := 3 * m + 1 - (t + 2)
    have hs2 : 3 * m + 1 - (t + 2) = r0 := rfl
    have hs1 : 3 * m + 1 - (t + 1) = r0 + 1 := by omega
    have hs0 : 3 * m + 1 - t = r0 + 2 := by omega
    have hsm1 : 3 * m + 1 - (t - 1) = r0 + 3 := by omega
    have hsm2 : 3 * m + 1 - (t - 2) = r0 + 4 := by omega
    have hk2 : liftKey z (ix (t + 2)) = B r0 + E r0 z := by
      rw [hsite z (t + 2) (by omega), hs2]
    have hk1 : liftKey z (ix (t + 1)) = B (r0 + 1) + E (r0 + 1) z := by
      rw [hsite z (t + 1) (by omega), hs1]
    have hk0 : liftKey z (ix t) = B (r0 + 2) + E (r0 + 2) z := by
      rw [hsite z t (by omega), hs0]
    have hkm1 : liftKey z (ix (t - 1)) = B (r0 + 3) + E (r0 + 3) z := by
      rw [hsite z (t - 1) (by omega), hsm1]
    have hkm2 : liftKey z (ix (t - 2)) = B (r0 + 4) + E (r0 + 4) z := by
      rw [hsite z (t - 2) (by omega), hsm2]
    have hne12 : (1 : ℕ) ≠ 2 := by decide
    have hne02 : (0 : ℕ) ≠ 2 := by decide
    have hne01 : (0 : ℕ) ≠ 1 := by decide
    have hB0 : B (r0 + 2) = B (r0 + 1) + B r0 + nameOff hk name (t + 2) + cd g := by
      have hdiv : (3 * m - 1 - r0) / 3 = g.val := by omega
      have hmod : (3 * m - 1 - r0) % 3 = 2 := by omega
      have hlt : (3 * m - 1 - r0) / 3 < m := by omega
      have hsum : 3 * m - 1 - r0 + 2 = t + 2 := by omega
      have hg : (⟨(3 * m - 1 - r0) / 3, hlt⟩ : Fin m) = g := Fin.ext hdiv
      change baseRev hk name c ca cb cd (r0 + 2) = _
      unfold baseRev
      simp only [hlt, ↓reduceDIte, hmod, ↓reduceIte, hsum, hg]
      rfl
    have hE0 : E (r0 + 2) z = E (r0 + 1) z + E r0 z + d g z := by
      have hdiv : (3 * m - 1 - r0) / 3 = g.val := by omega
      have hmod : (3 * m - 1 - r0) % 3 = 2 := by omega
      have hlt : (3 * m - 1 - r0) / 3 < m := by omega
      have hg : (⟨(3 * m - 1 - r0) / 3, hlt⟩ : Fin m) = g := Fin.ext hdiv
      change encRev a b d (r0 + 2) z = _
      unfold encRev
      simp only [hlt, ↓reduceDIte, hmod, ↓reduceIte, LinearMap.add_apply, hg]
      rfl
    have hB1 : B (r0 + 3) = 1 + B (r0 + 2) + B (r0 + 1) + nameOff hk name (t + 1) + cb g := by
      have hdiv : (3 * m - 1 - (r0 + 1)) / 3 = g.val := by omega
      have hmod : (3 * m - 1 - (r0 + 1)) % 3 = 1 := by omega
      have hlt : (3 * m - 1 - (r0 + 1)) / 3 < m := by omega
      have hsum : 3 * m - 1 - (r0 + 1) + 2 = t + 1 := by omega
      have hg : (⟨(3 * m - 1 - (r0 + 1)) / 3, hlt⟩ : Fin m) = g := Fin.ext hdiv
      change baseRev hk name c ca cb cd ((r0 + 1) + 2) = _
      unfold baseRev
      simp only [hlt, ↓reduceDIte, hmod, hne12, ↓reduceIte, hsum, hg]
      rfl
    have hE1 : E (r0 + 3) z = E (r0 + 2) z + E (r0 + 1) z + b g z := by
      have hdiv : (3 * m - 1 - (r0 + 1)) / 3 = g.val := by omega
      have hmod : (3 * m - 1 - (r0 + 1)) % 3 = 1 := by omega
      have hlt : (3 * m - 1 - (r0 + 1)) / 3 < m := by omega
      have hg : (⟨(3 * m - 1 - (r0 + 1)) / 3, hlt⟩ : Fin m) = g := Fin.ext hdiv
      change encRev a b d ((r0 + 1) + 2) z = _
      unfold encRev
      simp only [hlt, ↓reduceDIte, hmod, hne12, ↓reduceIte, LinearMap.add_apply, hg]
      rfl
    have hB2 : B (r0 + 4) = B (r0 + 3) + nameOff hk name t + c (ix t) + ca g := by
      have hdiv : (3 * m - 1 - (r0 + 2)) / 3 = g.val := by omega
      have hmod : (3 * m - 1 - (r0 + 2)) % 3 = 0 := by omega
      have hlt : (3 * m - 1 - (r0 + 2)) / 3 < m := by omega
      have hsum : 3 * m - 1 - (r0 + 2) + 2 = t := by omega
      have hg : (⟨(3 * m - 1 - (r0 + 2)) / 3, hlt⟩ : Fin m) = g := Fin.ext hdiv
      change baseRev hk name c ca cb cd ((r0 + 2) + 2) = _
      unfold baseRev
      simp only [hlt, ↓reduceDIte, hmod, hne02, hne01, ↓reduceIte, hsum, hg]
      rfl
    have hE2 : E (r0 + 4) z = E (r0 + 3) z + a g z := by
      have hdiv : (3 * m - 1 - (r0 + 2)) / 3 = g.val := by omega
      have hmod : (3 * m - 1 - (r0 + 2)) % 3 = 0 := by omega
      have hlt : (3 * m - 1 - (r0 + 2)) / 3 < m := by omega
      have hg : (⟨(3 * m - 1 - (r0 + 2)) / 3, hlt⟩ : Fin m) = g := Fin.ext hdiv
      change encRev a b d ((r0 + 2) + 2) z = _
      unfold encRev
      simp only [hlt, ↓reduceDIte, hmod, hne02, hne01, ↓reduceIte, LinearMap.add_apply, hg]
      rfl
    have h_eqD : liftKey z (ix (t + 2 - 2)) + liftKey z (ix (t + 2 - 1)) + liftKey z (ix (t + 2)) +
        (name (ix (t + 2 - 1)) + name (ix (t + 2)) + name (ix (t + 2 + 1))) = d g z + cd g := by
      have ha : t + 2 - 2 = t := by omega
      have hb : t + 2 - 1 = t + 1 := by omega
      rw [ha, hb, hk0, hk1, hk2, hB0, hE0]
      change (B (r0 + 1) + B r0 + nameOff hk name (t + 2) + cd g + (E (r0 + 1) z + E r0 z + d g z)) +
        (B (r0 + 1) + E (r0 + 1) z) + (B r0 + E r0 z) + nameOff hk name (t + 2) = d g z + cd g
      calc _ = (d g z + cd g) + (B (r0 + 1) + B (r0 + 1)) + (B r0 + B r0) +
            (E (r0 + 1) z + E (r0 + 1) z) + (E r0 z + E r0 z) +
            (nameOff hk name (t + 2) + nameOff hk name (t + 2)) := by ring
        _ = d g z + cd g := by simp only [zmod2_add_self, add_zero]
    have h_eqB : 1 + (liftKey z (ix (t + 1 - 2)) + liftKey z (ix (t + 1 - 1)) + liftKey z (ix (t + 1)) +
        (name (ix (t + 1 - 1)) + name (ix (t + 1)) + name (ix (t + 1 + 1)))) = b g z + cb g := by
      have ha : t + 1 - 2 = t - 1 := by omega
      have hb : t + 1 - 1 = t := by omega
      rw [ha, hb, hkm1, hk0, hk1, hB1, hE1]
      change 1 + ((1 + B (r0 + 2) + B (r0 + 1) + nameOff hk name (t + 1) + cb g +
        (E (r0 + 2) z + E (r0 + 1) z + b g z)) + (B (r0 + 2) + E (r0 + 2) z) +
        (B (r0 + 1) + E (r0 + 1) z) + nameOff hk name (t + 1)) = b g z + cb g
      calc _ = (b g z + cb g) + (1 + 1) + (B (r0 + 2) + B (r0 + 2)) + (B (r0 + 1) + B (r0 + 1)) +
            (E (r0 + 2) z + E (r0 + 2) z) + (E (r0 + 1) z + E (r0 + 1) z) +
            (nameOff hk name (t + 1) + nameOff hk name (t + 1)) := by ring
        _ = b g z + cb g := by simp only [zmod2_add_self, add_zero]
    have h_eqA : (liftKey z (ix (t - 2)) + liftKey z (ix (t - 1)) + liftKey z (ix t) +
        (name (ix (t - 1)) + name (ix t) + name (ix (t + 1)))) + liftKey z (ix t) + c (ix t) =
        a g z + ca g := by
      rw [hkm2, hkm1, hk0, hB2, hE2]
      change (B (r0 + 3) + nameOff hk name t + c (ix t) + ca g + (E (r0 + 3) z + a g z) +
        (B (r0 + 3) + E (r0 + 3) z) + (B (r0 + 2) + E (r0 + 2) z) + nameOff hk name t) +
        (B (r0 + 2) + E (r0 + 2) z) + c (ix t) = a g z + ca g
      calc _ = (a g z + ca g) + (B (r0 + 3) + B (r0 + 3)) + (E (r0 + 3) z + E (r0 + 3) z) +
            (B (r0 + 2) + B (r0 + 2)) + (E (r0 + 2) z + E (r0 + 2) z) +
            (nameOff hk name t + nameOff hk name t) + (c (ix t) + c (ix t)) := by ring
        _ = a g z + ca g := by simp only [zmod2_add_self, add_zero]
    rw [h_eqD, h_eqB]
    have hrearr : ∀ u v w : ZMod 2, u + v + w = (u + w) + v := fun u v w => by ring
    calc (liftKey z (ix (t - 2)) + liftKey z (ix (t - 1)) + liftKey z (ix t) +
            (name (ix (t - 1)) + name (ix t) + name (ix (t + 1)))) +
          (b g z + cb g) * (d g z + cd g) + liftKey z (ix t) + c (ix t)
        = ((liftKey z (ix (t - 2)) + liftKey z (ix (t - 1)) + liftKey z (ix t) +
            (name (ix (t - 1)) + name (ix t) + name (ix (t + 1)))) +
          liftKey z (ix t) + c (ix t)) + (b g z + cb g) * (d g z + cd g) := by ring
      _ = target z g := by rw [h_eqA]
  refine ⟨base, enc, hcopy, hrun, fun y => ?_⟩
  symm
  refine Nat.card_congr
    { toFun := fun s => ⟨liftKey s.1, ⟨s.1, rfl⟩, fun g => (hrun s.1 g).trans (s.2 g)⟩
      invFun := fun s =>
        ⟨fun p => s.1 (ix (3 * m + 2 + p.val)), fun g => by
          obtain ⟨z, hz⟩ := s.2.1
          change liftKey z = s.1 at hz
          have hzeq : (fun p => s.1 (ix (3 * m + 2 + p.val))) = z := by
            ext p
            rw [← hz]
            exact hcopy z p
          rw [hzeq, ← hrun z g, hz]
          exact s.2.2 g⟩
      left_inv := fun s => by
        apply Subtype.ext
        ext p
        exact hcopy s.1 p
      right_inv := fun s => by
        apply Subtype.ext
        obtain ⟨z, hz⟩ := s.2.1
        change liftKey z = s.1 at hz
        have hzeq : (fun p => s.1 (ix (3 * m + 2 + p.val))) = z := by
          ext p
          rw [← hz]
          exact hcopy z p
        change liftKey (fun p => s.1 (ix (3 * m + 2 + p.val))) = s.1
        rw [hzeq, hz] }

end PEqualNP.Outside.L_meta_25651_aux

theorem PEqualNP.Outside.L_meta_25651 : ∀ (k n m : Nat) (hk : 0 < k), 3*m+2+n ≤ k →
  let X := Fin n → ZMod 2
  let W := Fin k → ZMod 2
  let ix := fun site : Nat => (⟨site % k, Nat.mod_lt _ hk⟩ : Fin k)
  ∀ (name c : W) (a b d : Fin m → (X →ₗ[ZMod 2] ZMod 2))
    (ca cb cd : Fin m → ZMod 2),
    let target := fun (x : X) (g : Fin m) =>
      a g x + ca g + (b g x + cb g) * (d g x + cd g)
    let run := fun (key : W) =>
      let z := fun j : Fin k => key (ix (j.val+k-1)) + name j
      let mix := fun i : Fin k => z i + z (ix (i.val+1)) + z (ix (i.val+k-1))
      fun t : Fin k => mix t + (1+mix (ix (t.val+1))) * mix (ix (t.val+2)) + key t + c t
    ∃ (base : W) (enc : X →ₗ[ZMod 2] W),
      let liftKey := fun arg : X => base + enc arg
      (∀ (z : X) (p : Fin n), liftKey z (ix (3*m+2+p.val)) = z p) ∧
      (∀ (z : X) (g : Fin m), run (liftKey z) (ix (3*g.val+2)) = target z g) ∧
      ∀ y : Fin m → ZMod 2,
        Nat.card { key : W // key ∈ Set.range liftKey ∧
          ∀ g : Fin m, run key (ix (3*g.val+2)) = y g } =
        Nat.card { z : X // ∀ g : Fin m, target z g = y g } := by
  intro k n m hk hknm X W ix name c a b d ca cb cd target run
  exact PEqualNP.Outside.L_meta_25651_aux.main_aux k n m hk hknm name c a b d ca cb cd

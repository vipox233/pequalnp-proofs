import Mathlib

namespace PEqualNP.Outside.L_meta_25627_aux

abbrev W (k : Nat) := Fin k → ZMod 2

def ix {k : Nat} (hk : 0 < k) (i : Nat) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩

def mix {k : Nat} (hk : 0 < k) (d : Nat) (x : W k) (i : Fin k) : ZMod 2 :=
  x i + x (ix hk (i.val + d)) + x (ix hk (i.val + k - d % k))

def step {k : Nat} (hk : 0 < k) (x : W k) (i : Fin k) : ZMod 2 :=
  x i + (1 + x (ix hk (i.val + 1))) * x (ix hk (i.val + 2))

private def permuteLift {k : Nat} [NeZero k] (x : W k) (a : ZMod k) : ZMod 2 :=
  x ⟨a.val, a.val_lt⟩

private theorem permuteLift_nat {k : Nat} [NeZero k] (hk : 0 < k) (x : W k) (n : Nat) :
    permuteLift x (n : ZMod k) = x (ix hk n) := by
  apply congrArg x
  exact Fin.ext (ZMod.val_natCast k n)

private theorem permuteLift_add {k : Nat} [NeZero k] (hk : 0 < k) (x : W k)
    (a : ZMod k) (d : Nat) :
    permuteLift x (a + (d : ZMod k)) = x (ix hk (a.val + d)) := by
  rw [← permuteLift_nat hk x (a.val + d), Nat.cast_add, ZMod.natCast_zmod_val]

-- A shift coprime to the word length reaches every index.
private theorem permute_orbit {k p : Nat} [NeZero k] (hp : Nat.Coprime p k)
    (P : ZMod k → Prop) (hP : ∀ a, P a → P (a + (p : ZMod k)))
    {a : ZMod k} (ha : P a) (b : ZMod k) : P b := by
  have hiter (n : Nat) : P (a + (n : ZMod k) * (p : ZMod k)) := by
    induction n with
    | zero => simpa using ha
    | succ n ih =>
        have hshift : a + ((n + 1 : Nat) : ZMod k) * (p : ZMod k) =
            (a + (n : ZMod k) * (p : ZMod k)) + (p : ZMod k) := by
          push_cast
          ring
        rw [hshift]
        exact hP _ ih
  let u := ZMod.unitOfCoprime p hp
  let c : ZMod k := (b - a) * (↑u⁻¹ : ZMod k)
  have hc : a + (c.val : ZMod k) * (p : ZMod k) = b := by
    rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime p hp]
    change a + ((b - a) * (↑u⁻¹ : ZMod k)) * (↑u : ZMod k) = b
    rw [Units.inv_mul_cancel_right]
    ring
  rw [← hc]
  exact hiter c.val

private theorem permuteLift_inj {k : Nat} [NeZero k] (hk : 0 < k) :
    Function.Injective (permuteLift (k := k)) := by
  intro x y he
  funext i
  simpa only [permuteLift_nat hk, show ix hk i.val = i from Fin.ext (Nat.mod_eq_of_lt i.isLt)]
    using congrFun he (i.val : ZMod k)

private theorem mix_inj {k : Nat} (hk : 0 < k) (d : Nat) (hd : d = 1 ∨ d = 2)
    (ho : Odd k) (h3 : k % 3 ≠ 0) : Function.Injective (mix hk d) := by
  let _ : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hcop : Nat.Coprime (3 * d) k := by
    apply Nat.coprime_mul_iff_left.mpr
    refine ⟨Nat.prime_three.coprime_iff_not_dvd.mpr ?_, ?_⟩
    · exact fun h => h3 (Nat.mod_eq_zero_of_dvd h)
    · rcases hd with rfl | rfl
      · exact Nat.coprime_one_left k
      · exact ho.coprime_two_left
  intro x y he
  let z (a : ZMod k) := permuteLift x a - permuteLift y a
  have hrec (a : ZMod k) : z a + z (a + (d : ZMod k)) + z (a - (d : ZMod k)) = 0 := by
    have hback : a - (d : ZMod k) = ((a.val + k - d % k : Nat) : ZMod k) := by
      have hle : d % k ≤ a.val + k := by have := Nat.mod_lt d hk; omega
      rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_zmod_val,
        ZMod.natCast_self, add_zero, ZMod.natCast_mod]
    have hh := congrFun he (⟨a.val, a.val_lt⟩ : Fin k)
    simp only [mix] at hh
    simp only [z, hback, permuteLift_add hk, permuteLift_nat hk]
    change permuteLift x a + x (ix hk (a.val + d)) + x (ix hk (a.val + k - d % k)) =
      permuteLift y a + y (ix hk (a.val + d)) + y (ix hk (a.val + k - d % k)) at hh
    linear_combination hh
  have hper (a : ZMod k) : z (a + ((3 * d : Nat) : ZMod k)) = z a := by
    have h₁ := hrec (a + (d : ZMod k))
    have h₂ := hrec (a + (d : ZMod k) + (d : ZMod k))
    rw [add_sub_cancel_right] at h₁ h₂
    have hshift : a + ((3 * d : Nat) : ZMod k) = a + (d : ZMod k) + d + d := by
      push_cast
      ring
    rw [hshift]
    linear_combination h₂ - h₁
  apply permuteLift_inj hk
  funext a
  apply sub_eq_zero.mp
  change z a = 0
  have hc (b : ZMod k) : z b = z a :=
    permute_orbit hcop (fun b => z b = z a) (fun b hb => (hper b).trans hb) rfl b
  have hh := hrec a
  rw [hc (a + (d : ZMod k)), hc (a - (d : ZMod k)), CharTwo.add_self_eq_zero, zero_add] at hh
  exact hh

private theorem permute_bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ f : Fin 2, f = 0 ∨ f = 1 := by decide
  exact h a

private theorem permute_bit_annihilate (a : ZMod 2) : (1 + a) * a = 0 := by
  rcases permute_bit_cases a with ha | ha <;> rw [ha] <;> decide

private theorem permute_step_lift {k : Nat} [NeZero k] (hk : 0 < k) (v : W k) (a : ZMod k) :
    permuteLift (step hk v) a = permuteLift v a +
      (1 + permuteLift v (a + 1)) * permuteLift v (a + 2) := by
  have h : permuteLift (step hk v) a = permuteLift v a +
      (1 + permuteLift v (a + ((1 : Nat) : ZMod k))) *
        permuteLift v (a + ((2 : Nat) : ZMod k)) := by
    rw [permuteLift_add hk, permuteLift_add hk]
    rfl
  simpa only [Nat.cast_one, Nat.cast_two] using h

private theorem permute_step_inverse {k : Nat} [NeZero k] (hk : 0 < k) (v : W k) (a : ZMod k) :
    permuteLift v a = permuteLift (step hk v) a +
      (1 + permuteLift (step hk v) (a + 1)) * permuteLift v (a + 2) := by
  rw [permute_step_lift hk v a, permute_step_lift hk v (a + 1)]
  rw [show a + 1 + 1 = a + 2 by ring]
  have htwo : (2 : ZMod 2) = 0 := by decide
  linear_combination
    -permuteLift v (a + 1 + 2) * permute_bit_annihilate (permuteLift v (a + 2)) -
    (1 + permuteLift v (a + 1)) * permuteLift v (a + 2) * htwo

private theorem step_inj {k : Nat} (hk : 0 < k) (ho : Odd k) : Function.Injective (step hk) := by
  let _ : NeZero k := ⟨Nat.ne_of_gt hk⟩
  intro x v he
  let Y := permuteLift (step hk x)
  let z (a : ZMod k) := permuteLift x a - permuteLift v a
  have hy (a : ZMod k) : Y a = permuteLift (step hk v) a :=
    congrArg (fun w : W k => permuteLift w a) he
  have hrec (a : ZMod k) : z a = (1 + Y (a + 1)) * z (a + 2) := by
    have hx := permute_step_inverse hk x a
    have hv := permute_step_inverse hk v a
    rw [← hy a, ← hy (a + 1)] at hv
    change permuteLift x a = Y a + (1 + Y (a + 1)) * permuteLift x (a + 2) at hx
    dsimp only [z]
    linear_combination hx - hv
  apply permuteLift_inj hk
  funext a
  apply sub_eq_zero.mp
  change z a = 0
  by_contra hza
  have hnonzero (b : ZMod k) : z b ≠ 0 := by
    apply permute_orbit ho.coprime_two_left (fun b => z b ≠ 0) ?_ hza b
    intro c hc hz
    apply hc
    have hz' : z (c + 2) = 0 := by simpa only [Nat.cast_two] using hz
    simpa only [hz', mul_zero] using hrec c
  have hy0 (b : ZMod k) : Y b = 0 := by
    have hidx : b - 1 + 1 = b := sub_add_cancel _ _
    rcases permute_bit_cases (Y b) with h | h
    · exact h
    · have hbad := hrec (b - 1)
      rw [hidx, h, show (1 : ZMod 2) + 1 = 0 by decide, zero_mul] at hbad
      exact (hnonzero _ hbad).elim
  have hzero (w : W k) (hw : ∀ b, permuteLift (step hk w) b = 0) (b : ZMod k) :
      permuteLift w b = 0 := by
    have hper (c : ZMod k) : permuteLift w c = permuteLift w (c + 2) := by
      simpa only [hw, add_zero, one_mul, zero_add] using permute_step_inverse hk w c
    have hc (c : ZMod k) : permuteLift w c = permuteLift w b := by
      apply permute_orbit ho.coprime_two_left (fun c => permuteLift w c = permuteLift w b) ?_ rfl c
      intro j hj
      simpa only [Nat.cast_two] using (hper j).symm.trans hj
    have hs := permute_step_lift hk w b
    rw [hw b, hc (b + 1), hc (b + 2), permute_bit_annihilate, add_zero] at hs
    exact hs.symm
  have hv0 (b : ZMod k) : permuteLift (step hk v) b = 0 := (hy b).symm.trans (hy0 b)
  exact hza (sub_eq_zero.mpr ((hzero x hy0 a).trans (hzero v hv0 a).symm))

def run {k : Nat} (hk : 0 < k) (d : Nat) (a : Nat → W k) (x : W k) : Nat → W k
  | 0 => step hk x + a 0
  | n + 1 => step hk (mix hk d (run hk d a x n)) + a (n + 1)

private theorem tri_ix_add {k : Nat} (hk : 0 < k) (b t : Nat) :
    ix hk ((ix hk b).val + t) = ix hk (b + t) := by
  apply Fin.ext
  exact Nat.mod_add_mod b k t

private theorem tri_ix_sub {k : Nat} (hk : 0 < k) (b d : Nat) :
    ix hk ((ix hk (b + d)).val + k - d % k) = ix hk b := by
  apply Fin.ext
  change ((b + d) % k + k - d % k) % k = b % k
  apply Nat.ModEq.add_right_cancel' (d % k)
  change (((b + d) % k + k - d % k) + d % k) % k = (b + d % k) % k
  have hq : d % k ≤ (b + d) % k + k := by have := Nat.mod_lt d hk; omega
  simp only [Nat.sub_add_cancel hq, Nat.add_mod_right, Nat.mod_mod, Nat.add_mod_mod]

private theorem tri_step_at {k : Nat} (hk : 0 < k) (z : W k) (b : Nat) :
    step hk z (ix hk b) =
      z (ix hk b) + (1 + z (ix hk (b + 1))) * z (ix hk (b + 2)) := by
  simp only [step, tri_ix_add]

private theorem tri_mix_at {k : Nat} (hk : 0 < k) (d : Nat) (z : W k) (b : Nat) :
    mix hk d z (ix hk (b + d)) =
      z (ix hk (b + d)) + z (ix hk (b + 2 * d)) + z (ix hk b) := by
  simp only [mix, tri_ix_add, tri_ix_sub]
  rw [show b + d + d = b + 2 * d by omega]

private theorem run_delta {k : Nat} (hk : 0 < k) (d : Nat) (hd : 0 < d)
    (a : Nat → W k) (x y : W k) (n j : Nat)
    (H : ∀ t : Nat, 0 < t → t ≤ 2 + (2 * d + 2) * n →
      x (ix hk (j + t)) = y (ix hk (j + t))) :
    run hk d a x n (ix hk (j + n * d)) - run hk d a y n (ix hk (j + n * d)) =
      x (ix hk j) - y (ix hk j) := by
  induction n generalizing j with
  | zero =>
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero] at H ⊢
    change (step hk x (ix hk j) + a 0 (ix hk j)) -
      (step hk y (ix hk j) + a 0 (ix hk j)) = _
    rw [tri_step_at, tri_step_at, H 1 (by decide) (by decide), H 2 (by decide) (by decide)]
    ring
  | succ n ih =>
    let b := j + n * d
    let u := run hk d a x n
    let v := run hk d a y n
    have hspan : 2 + (2 * d + 2) * (n + 1) = 2 + (2 * d + 2) * n + (2 * d + 2) := by
      rw [Nat.mul_succ, Nat.add_assoc]
    have htail (t : Nat) (ht : 0 < t) (ht' : t ≤ 2 * d + 2) :
        u (ix hk (b + t)) = v (ix hk (b + t)) := by
      have hshift := ih (j + t) (by
        intro s hs hs'
        rw [Nat.add_assoc]
        exact H (t + s) (by omega) (by rw [hspan]; omega))
      have hbit := H t ht (by rw [hspan]; omega)
      rw [show j + t + n * d = b + t by dsimp [b]; omega, hbit] at hshift
      exact sub_eq_zero.mp (hshift.trans (sub_self _))
    have hmix (t : Nat) (ht : 0 < t) (ht' : t ≤ 2) :
        mix hk d u (ix hk (b + d + t)) = mix hk d v (ix hk (b + d + t)) := by
      rw [show b + d + t = b + t + d by omega, tri_mix_at, tri_mix_at]
      simp only [Nat.add_assoc]
      rw [htail (t + d) (by omega) (by omega),
        htail (t + 2 * d) (by omega) (by omega), htail t ht (by omega)]
    have hlead := ih j (by
      intro t ht ht'
      exact H t ht (by rw [hspan]; omega))
    rw [show j + (n + 1) * d = b + d by simp only [b, Nat.succ_mul, Nat.add_assoc]]
    change (step hk (mix hk d u) (ix hk (b + d)) + a (n + 1) (ix hk (b + d))) -
      (step hk (mix hk d v) (ix hk (b + d)) + a (n + 1) (ix hk (b + d))) = _
    rw [tri_step_at, tri_step_at, hmix 1 (by decide) (by decide), hmix 2 (by decide) (by decide),
      tri_mix_at, tri_mix_at, htail d hd (by omega), htail (2 * d) (by omega) (by omega), ← hlead]
    ring

def rot {k : Nat} (hk : 0 < k) (s : Nat) (x : W k) (i : Fin k) : ZMod 2 :=
  x (ix hk (i.val + k - s % k))

def out {k : Nat} (hk : 0 < k) (d r s : Nat) (shift : Nat → Nat) (c : Nat → W k)
    (w name : W k) : W k :=
  (List.range r).foldl (fun state i => step hk (mix hk d state) + rot hk (shift i) w + c i)
    (rot hk s w + name)

private theorem mix_add {k : Nat} (hk : 0 < k) (d : Nat) (x y : W k) :
    mix hk d (x + y) = mix hk d x + mix hk d y := by
  funext i
  simp only [mix, Pi.add_apply]
  abel

private theorem out_inj {k : Nat} (hk : 0 < k) (d r s : Nat) (shift : Nat → Nat)
    (c : Nat → W k) (w : W k) (hm : Function.Injective (mix hk d))
    (hs : Function.Injective (step hk)) : Function.Injective (out hk d r s shift c w) := by
  let f := fun (state : W k) i => step hk (mix hk d state) + rot hk (shift i) w + c i
  have hf (is : List Nat) : Function.Injective (is.foldl f) := by
    induction is with
    | nil => exact fun _ _ eq => eq
    | cons i is ih =>
      intro x y he
      change is.foldl f (f x i) = is.foldl f (f y i) at he
      exact hm (hs (add_right_cancel (add_right_cancel (ih he))))
  exact (hf (List.range r)).comp (fun _ _ he => add_left_cancel he)

private theorem out_succ {k : Nat} (hk : 0 < k) (d n s : Nat) (shift : Nat → Nat)
    (c : Nat → W k) (w x : W k) :
    out hk d (n + 1) s shift c w x = run hk d (fun i => rot hk (shift i) w + c i)
      (mix hk d (rot hk s w + x)) n := by
  induction n with
  | zero => exact add_assoc _ _ _
  | succ n ih =>
    rw [out, List.range_succ, List.foldl_append]
    change step hk (mix hk d (out hk d (n + 1) s shift c w x)) + rot hk (shift (n + 1)) w +
      c (n + 1) = _
    rw [ih]
    exact add_assoc _ _ _

private theorem ix_align {k : Nat} (hk : 0 < k) (start q j : Nat) :
    ix hk (start + k - q % k + j + q) = ix hk (start + j) := by
  apply Fin.ext
  change (start + k - q % k + j + q) % k = (start + j) % k
  rw [← Nat.add_mod_mod (start + k - q % k + j) q k]
  have hq := Nat.mod_lt q hk
  rw [show start + k - q % k + j + q % k = start + j + k by omega, Nat.add_mod_right]

private theorem out_delta {k : Nat} (hk : 0 < k) (d : Nat)
    (hrun : ∀ (a : Nat → W k) (x y : W k) (n j : Nat),
      (∀ t, 0 < t → t ≤ 2 + (2 * d + 2) * n → x (ix hk (j + t)) = y (ix hk (j + t))) →
      run hk d a x n (ix hk (j + n * d)) - run hk d a y n (ix hk (j + n * d)) =
        x (ix hk j) - y (ix hk j))
    (n s : Nat) (shift : Nat → Nat) (c : Nat → W k) (start : Nat)
    (w x y : W k) (j : Nat) :
    let base := start + k - (n * d) % k
    (∀ t, 0 < t → t ≤ 2 + (2 * d + 2) * n →
      mix hk d x (ix hk (base + j + t)) = mix hk d y (ix hk (base + j + t))) →
    out hk d (n + 1) s shift c w x (ix hk (start + j)) -
      out hk d (n + 1) s shift c w y (ix hk (start + j)) =
      mix hk d x (ix hk (base + j)) - mix hk d y (ix hk (base + j)) := by
  dsimp only
  intro htail
  rw [← ix_align hk start (n * d) j, out_succ, out_succ, mix_add, mix_add]
  rw [hrun _ _ _ _ _ (fun t ht hD => by simp only [Pi.add_apply, htail t ht hD])]
  simp only [Pi.add_apply]
  abel

private theorem conflict {K N T U : Type} [Fintype T] [Fintype U]
    (P : K → N → Prop) (tail : N → T) (free : K → N → U) (keys : Finset K)
    (hT : 2 ≤ Fintype.card T)
    (htail : ∀ a b x y, P a x → P a y → tail x = tail y → (P b x ↔ P b y))
    (hfree : ∀ a x y, P a x → P a y → free a x = free a y → x = y)
    (hempty : ¬ ∃ x, ∀ a ∈ keys, P a x) :
    ∃ bad ⊆ keys, bad.card ≤ min (Fintype.card T) (Fintype.card U + 1) ∧
      ¬ ∃ x, ∀ a ∈ bad, P a x := by
  classical
  let Q (n : Nat) := ∃ bad ⊆ keys, (bad : Finset K).card = n ∧ ¬ ∃ x, ∀ a ∈ bad, P a x
  have hex : ∃ n, Q n := ⟨keys.card, keys, Finset.Subset.rfl, rfl, hempty⟩
  obtain ⟨bad, hsub, hcard, hbad⟩ := Nat.find_spec hex
  have hdelete (i : ↥bad) : ∃ x, ∀ a ∈ bad.erase i.val, P a x := by
    by_contra hno
    have hsub' : bad.erase i.val ⊆ keys := (Finset.erase_subset _ _).trans hsub
    have hle := Nat.find_min' hex (show Q (bad.erase i.val).card from
      ⟨bad.erase i.val, hsub', rfl, hno⟩)
    rw [← hcard, Finset.card_erase_of_mem i.property] at hle
    have hpos := Finset.card_pos.mpr ⟨i.val, i.property⟩
    omega
  choose z hz using hdelete
  have hpass (i : ↥bad) (a : K) (ha : a ∈ bad) (hne : a ≠ i.val) : P a (z i) :=
    hz i a (Finset.mem_erase.mpr ⟨hne, ha⟩)
  have hfail (i : ↥bad) : ¬ P i.val (z i) := by
    intro hi
    apply hbad
    refine ⟨z i, fun a ha => ?_⟩
    by_cases hh : a = i.val
    · simpa only [hh] using hi
    · exact hpass i a ha hh
  refine ⟨bad, hsub, le_min ?_ ?_, hbad⟩
  · by_cases hs : bad.card ≤ 2
    · exact hs.trans hT
    · have hinj : Function.Injective (fun i : ↥bad => tail (z i)) := by
        intro i j he
        by_contra hne
        have hij : i.val ≠ j.val := fun h => hne (Subtype.ext h)
        have hj : j.val ∈ bad.erase i.val := Finset.mem_erase.mpr ⟨hij.symm, j.property⟩
        have hthird : ((bad.erase i.val).erase j.val).Nonempty := by
          apply Finset.card_pos.mp
          rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem i.property]
          omega
        obtain ⟨a, ha⟩ := hthird
        obtain ⟨haj, hai⟩ := Finset.mem_erase.mp ha
        obtain ⟨hai, ha⟩ := Finset.mem_erase.mp hai
        exact hfail i ((htail a i.val (z i) (z j) (hpass i a ha hai) (hpass j a ha haj) he).mpr
          (hpass j i.val i.property hij))
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hinj
  · by_cases he : bad.Nonempty
    · obtain ⟨a, ha⟩ := he
      let lift : ↥(bad.erase a) → ↥bad := fun i => ⟨i.val, (Finset.mem_erase.mp i.property).2⟩
      have hinj : Function.Injective (fun i : ↥(bad.erase a) => free a (z (lift i))) := by
        intro i j heq
        have hi : a ≠ (lift i).val := (Finset.mem_erase.mp i.property).1.symm
        have hj : a ≠ (lift j).val := (Finset.mem_erase.mp j.property).1.symm
        have hzij := hfree a (z (lift i)) (z (lift j)) (hpass (lift i) a ha hi)
          (hpass (lift j) a ha hj) heq
        by_contra hne
        have hij : (lift i).val ≠ (lift j).val := fun h => hne (Subtype.ext h)
        exact hfail (lift i) (hzij ▸ hpass (lift j) (lift i).val (lift i).property hij)
      have hc := Fintype.card_le_of_injective _ hinj
      rw [Fintype.card_coe, Finset.card_erase_of_mem ha] at hc
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty]
      exact Nat.zero_le _

private theorem ix_shift_bijective {k : Nat} (hk : 0 < k) (s : Nat) :
    Function.Bijective (fun i : Fin k => ix hk (s + i.val)) := by
  apply Finite.injective_iff_bijective.mp
  intro i j he
  apply Fin.ext
  have hm : s + i.val ≡ s + j.val [MOD k] := congrArg Fin.val he
  have hj : i.val ≡ j.val [MOD k] := Nat.ModEq.add_left_cancel' s hm
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hj

private theorem one_side {k h D : Nat} (hk : 0 < k) (hhk : h ≤ k) (hD : 0 < D)
    (start base : Nat) (g : W k → W k → W k) (τ : W k → W k)
    (hg : ∀ w, Function.Injective (g w))
    (hdelta : ∀ (w x y : W k) (j : Nat),
      (∀ t, 0 < t → t ≤ D → τ x (ix hk (base + j + t)) = τ y (ix hk (base + j + t))) →
      g w x (ix hk (start + j)) - g w y (ix hk (start + j)) =
        τ x (ix hk (base + j)) - τ y (ix hk (base + j)))
    (keys : Finset (W k))
    (hempty : ¬ ∃ x, ∀ w ∈ keys, ∀ j : Fin h, g w x (ix hk (start + j.val)) = 0) :
    ∃ bad ⊆ keys, bad.card ≤ min (2 ^ D) (2 ^ (k - h) + 1) ∧
      ¬ ∃ x, ∀ w ∈ bad, ∀ j : Fin h, g w x (ix hk (start + j.val)) = 0 := by
  let P (w x : W k) := ∀ j : Fin h, g w x (ix hk (start + j.val)) = 0
  let tail (x : W k) (t : Fin D) := τ x (ix hk (base + (h + t.val)))
  let free (w x : W k) (t : Fin (k - h)) := g w x (ix hk (start + (h + t.val)))
  have htail (a b x y : W k) (hax : P a x) (hay : P a y) (ht : tail x = tail y) :
      P b x ↔ P b y := by
    have agree_aux (n j : Nat) (hn : h - j = n) (hj : j < h + D) :
        τ x (ix hk (base + j)) = τ y (ix hk (base + j)) := by
      induction n using Nat.strong_induction_on generalizing j with
      | ind n ih =>
        by_cases hhigh : h ≤ j
        · have he := congrFun ht (⟨j - h, by omega⟩ : Fin D)
          change τ x (ix hk (base + (h + (j - h)))) = τ y (ix hk (base + (h + (j - h)))) at he
          simpa only [Nat.add_sub_of_le hhigh] using he
        · have δ := hdelta a x y j (fun t h0 htd => by
            have he := ih (h - (j + t)) (by omega) (j + t) rfl (by omega)
            simpa only [Nat.add_assoc] using he)
          rw [hax ⟨j, by omega⟩, hay ⟨j, by omega⟩, sub_self] at δ
          exact sub_eq_zero.mp δ.symm
    have agree (j : Fin h) : g b x (ix hk (start + j.val)) = g b y (ix hk (start + j.val)) := by
      apply sub_eq_zero.mp
      rw [hdelta b x y j.val (fun t _ htD => by
          have he := agree_aux (h - (j.val + t)) (j.val + t) rfl (by have := j.isLt; omega)
          simpa only [Nat.add_assoc] using he),
        agree_aux (h - j.val) j.val rfl (by have := j.isLt; omega), sub_self]
    exact ⟨fun hx j => (agree j).symm.trans (hx j), fun hy j => (agree j).trans (hy j)⟩
  have hfree (a x y : W k) (hx : P a x) (hy : P a y) (he : free a x = free a y) : x = y := by
    apply hg a
    funext i
    obtain ⟨j, rfl⟩ := (ix_shift_bijective hk start).2 i
    by_cases hj : j.val < h
    · exact (hx ⟨j.val, hj⟩).trans (hy ⟨j.val, hj⟩).symm
    · have e := congrFun he (⟨j.val - h, by have := j.isLt; omega⟩ : Fin (k - h))
      change g a x (ix hk (start + (h + (j.val - h)))) =
        g a y (ix hk (start + (h + (j.val - h)))) at e
      simpa only [Nat.add_sub_of_le (show h ≤ j.val by omega)] using e
  have hpow : 2 ≤ Fintype.card (Fin D → ZMod 2) := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ D by omega))
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using
    conflict P tail free keys hpow htail hfree hempty

private theorem bounded_side {k h : Nat} (hk : 0 < k) (ho : Odd k) (h3 : k % 3 ≠ 0)
    (hhk : h ≤ k) (d n s start : Nat) (hd : d = 1 ∨ d = 2)
    (shift : Nat → Nat) (c : Nat → W k) (keys : Finset (W k))
    (H : ¬ ∃ x, ∀ w ∈ keys, ∀ j : Fin h,
      out hk d (n + 1) s shift c w x (ix hk (start + j.val)) = 0) :
    ∃ bad ⊆ keys, bad.card ≤ min (2 ^ (2 + (2 * d + 2) * n)) (2 ^ (k - h) + 1) ∧
      ¬ ∃ x, ∀ w ∈ bad, ∀ j : Fin h,
        out hk d (n + 1) s shift c w x (ix hk (start + j.val)) = 0 := by
  have hpos : 0 < d := by omega
  exact one_side hk hhk (by omega) start (start + k - (n * d) % k)
    (out hk d (n + 1) s shift c) (mix hk d)
    (fun w => out_inj hk d (n + 1) s shift c w (mix_inj hk d hd ho h3) (step_inj hk ho))
    (out_delta hk d (run_delta hk d hpos) n s shift c start) keys H

private theorem split_sides {k h : Nat} (hk : 0 < k) (ho : Odd k) (h3 : k % 3 ≠ 0)
    (hhk : h ≤ k) (n start : Nat) (c₁ c₂ : Nat → W k) (keys : Finset (W k)) :
    let row (w x : W k) := ∀ j : Fin h,
      out hk 1 (n + 1) 1 (fun i => 2 * i) c₁ w x (ix hk (start + j.val)) = 0
    let col (w x : W k) := ∀ j : Fin h,
      out hk 2 (n + 1) 3 (fun i => 3 * i + 4) c₂ w x (ix hk (start + j.val)) = 0
    (¬ ∃ u v : W k, ∀ w ∈ keys, row w u ∧ col w v) →
    (∃ bad ⊆ keys, bad.card ≤ min (2 ^ (2 + (2 * 1 + 2) * n)) (2 ^ (k - h) + 1) ∧
      ¬ ∃ u : W k, ∀ w ∈ bad, row w u) ∨
    (∃ bad ⊆ keys, bad.card ≤ min (2 ^ (2 + (2 * 2 + 2) * n)) (2 ^ (k - h) + 1) ∧
      ¬ ∃ v : W k, ∀ w ∈ bad, col w v) := by
  classical
  intro row col H
  by_cases hr : ∃ u : W k, ∀ w ∈ keys, row w u
  · right
    apply bounded_side hk ho h3 hhk 2 n 3 start (Or.inr rfl) (fun i => 3 * i + 4) c₂ keys
    rintro ⟨v, hv⟩
    obtain ⟨u, hu⟩ := hr
    exact H ⟨u, v, fun w hw => ⟨hu w hw, hv w hw⟩⟩
  · exact Or.inl (bounded_side hk ho h3 hhk 1 n 1 start (Or.inl rfl) (fun i => 2 * i) c₁ keys hr)

end PEqualNP.Outside.L_meta_25627_aux

theorem PEqualNP.Outside.L_meta_25627 : ∀ (k r h : Nat) (hk : 0 < k), Odd k → k % 3 ≠ 0 → 0 < r → 0 < h → h ≤ k →
  let W := Fin k → ZMod 2
  let ix := fun i : Nat => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : Nat) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (d : Nat) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  ∀ (start : Nat) (c₁ c₂ : Nat → W),
    let test := fun (d s : Nat) (shift : Nat → Nat) (c : Nat → W) (w name : W) =>
      let out := (List.range r).foldl
        (fun state roundIndex => step (mix d state) + rot (shift roundIndex) w + c roundIndex) (rot s w + name)
      ∀ j : Fin h, out (ix (start + j.val)) = 0
    let row := test 1 1 (fun rowIndex => 2 * rowIndex) c₁
    let col := test 2 3 (fun colIndex => 3 * colIndex + 4) c₂
    let bound := fun D : Nat => min (2 ^ D) (2 ^ (k - h) + 1)
    ∀ keys : Finset W,
      (¬ ∃ u v : W, ∀ w ∈ keys, row w u ∧ col w v) →
      (∃ bad ⊆ keys, bad.card ≤ bound (4 * r - 2) ∧ ¬ ∃ u : W, ∀ w ∈ bad, row w u) ∨
      (∃ bad ⊆ keys, bad.card ≤ bound (6 * r - 4) ∧ ¬ ∃ v : W, ∀ w ∈ bad, col w v) := by
  intro k r h hk ho h3 hr hh hhk
  dsimp only
  intro start c₁ c₂ keys
  cases r with
  | zero => omega
  | succ n =>
    have hrow : 4 * (n + 1) - 2 = 2 + (2 * 1 + 2) * n := by omega
    have hcol : 6 * (n + 1) - 4 = 2 + (2 * 2 + 2) * n := by omega
    simp only [hrow, hcol]
    exact PEqualNP.Outside.L_meta_25627_aux.split_sides hk ho h3 hhk n start c₁ c₂ keys

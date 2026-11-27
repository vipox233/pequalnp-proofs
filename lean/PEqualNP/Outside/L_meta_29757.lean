import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29757

section

variable {s : ℕ} (n : Fin s → Bool → Option (Fin s))

def Absorbs := ∃ c : Fin s → Bool, ∀ i : Fin s,
  (fun x : Option (Fin s) => x.bind (fun j => n j (c j)))^[s] (some i) = none

def Ends (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) (i : Fin s) (b : Bool) : ℝ :=
  (n i b).elim (r i b) x

def Solves (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) : Prop :=
  ∀ i, 2 * x i = Ends n r x i false + Ends n r x i true

theorem minimumLaw (hn : Absorbs n) (x : Fin s → ℝ)
    (h : ∀ i, (n i false).elim 0 x + (n i true).elim 0 x ≤ 2 * x i) :
    ∀ i, 0 ≤ x i := by
  classical
  intro start
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ x ⟨start, Finset.mem_univ _⟩
  have hle (j) : x i ≤ x j := hmin _ (Finset.mem_univ j)
  suffices 0 ≤ x i by exact this.trans (hle start)
  by_contra! hi
  obtain ⟨c, hc⟩ := hn
  let F := fun o : Option (Fin s) => o.bind (fun j => n j (c j))
  have hb (o : Option (Fin s)) : x i ≤ o.elim 0 x := by cases o <;> simp [hi.le, hle]
  have step (o : Option (Fin s)) (ho : o.elim 0 x = x i) : (F o).elim 0 x = x i := by
    cases o with
    | none => exact ho
    | some j =>
      change x j = x i at ho
      have hj := h j
      rw [ho] at hj
      have h₀ := hb (n j false)
      have h₁ := hb (n j true)
      change (n j (c j)).elim 0 x = x i
      cases c j <;> linarith
  have rep (k : ℕ) : (F^[k] (some i)).elim 0 x = x i := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply']; exact step _ ih
  have he := rep s
  rw [show F^[s] (some i) = none from hc i] at he
  exact hi.ne (by simpa using he.symm)

def drift : (Fin s → ℝ) →ₗ[ℝ] (Fin s → ℝ) where
  toFun x i := 2 * x i - (n i false).elim 0 x - (n i true).elim 0 x
  map_add' x y := by
    ext i
    cases h₀ : n i false <;> cases h₁ : n i true <;> simp [h₀, h₁] <;> ring
  map_smul' a x := by
    ext i
    cases h₀ : n i false <;> cases h₁ : n i true <;> simp [h₀, h₁] <;> ring

theorem uniqueDrift (hn : Absorbs n) : Function.Injective (drift n) := by
  apply (LinearMap.ker_eq_bot.mp ?_)
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hz (i) : 2 * x i = (n i false).elim 0 x + (n i true).elim 0 x := by
    have h := congrFun hx i
    change 2 * x i - _ - _ = 0 at h
    linarith
  have hp := minimumLaw n hn x (fun i => (hz i).ge)
  have hm := minimumLaw n hn (fun j => -x j) (fun i => by
    specialize hz i
    cases h₀ : n i false <;> cases h₁ : n i true <;> simp [h₀, h₁] at hz ⊢ <;> linarith)
  ext i
  exact le_antisymm (neg_nonneg.mp (hm i)) (hp i)

def boundary (r : Fin s → Bool → ℝ) (i : Fin s) : ℝ :=
  (n i false).elim (r i false) (fun _ => 0) + (n i true).elim (r i true) (fun _ => 0)

theorem solves_iff (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) :
    Solves n r x ↔ drift n x = boundary n r := by
  constructor
  · intro h
    ext i
    specialize h i
    change 2 * x i - _ - _ = _
    cases h₀ : n i false <;> cases h₁ : n i true <;>
      simp [Ends, boundary, h₀, h₁] at h ⊢ <;> linarith
  · intro h i
    have hh := congrFun h i
    change 2 * x i - _ - _ = _ at hh
    cases h₀ : n i false <;> cases h₁ : n i true <;>
      simp [Ends, boundary, h₀, h₁] at hh ⊢ <;> linarith

noncomputable def mean (hn : Absorbs n) : (Fin s → Bool → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
  (LinearEquiv.ofBijective (drift n)
    ⟨uniqueDrift n hn, LinearMap.surjective_of_injective (uniqueDrift n hn)⟩).symm.toLinearMap.comp
      ({
        toFun := boundary n
        map_add' := by
          intro x y
          ext i
          cases h₀ : n i false <;> cases h₁ : n i true <;> simp [boundary, h₀, h₁] <;> ring
        map_smul' := by
          intro a x
          ext i
          cases h₀ : n i false <;> cases h₁ : n i true <;> simp [boundary, h₀, h₁] <;> ring } :
        (Fin s → Bool → ℝ) →ₗ[ℝ] (Fin s → ℝ))

theorem mean_solves (hn : Absorbs n) (r) : Solves n r (mean n hn r) := by
  rw [solves_iff]
  exact (LinearEquiv.ofBijective (drift n)
    ⟨uniqueDrift n hn, LinearMap.surjective_of_injective (uniqueDrift n hn)⟩).apply_symm_apply _

theorem eqMean (hn : Absorbs n) {r x} (h : Solves n r x) : x = mean n hn r :=
  uniqueDrift n hn (((solves_iff n _ _).mp h).trans ((solves_iff n _ _).mp (mean_solves n hn r)).symm)

theorem mean_const (hn : Absorbs n) (a : ℝ) : mean n hn (fun _ _ => a) = fun _ => a := by
  symm
  apply eqMean
  intro i
  cases h₀ : n i false <;> cases h₁ : n i true <;> simp [Ends, h₀, h₁] <;> ring

theorem mean_nonneg (hn : Absorbs n) (r : Fin s → Bool → ℝ) (hr : ∀ i b, 0 ≤ r i b) :
    ∀ i, 0 ≤ mean n hn r i := by
  apply minimumLaw n hn
  intro i
  rw [mean_solves n hn r i]
  cases h₀ : n i false <;> cases h₁ : n i true <;> simp [Ends, h₀, h₁, hr, add_nonneg]

theorem mean_mono (hn : Absorbs n) {a b : Fin s → Bool → ℝ} (h : a ≤ b) :
    mean n hn a ≤ mean n hn b := by
  have hh := mean_nonneg n hn (b - a) (fun i j => sub_nonneg.mpr (h i j))
  rw [map_sub] at hh
  exact fun i => sub_nonneg.mp (hh i)

end

end PEqualNP.Outside.L_meta_29757

namespace PEqualNP.Outside.L_meta_29757

theorem three_dvd_four (k m : ℕ) :
    3^(k+1) ∣ 4^m - 1 ↔ 3^k ∣ m := by
  have hl := Nat.emultiplicity_pow_sub_pow (p := 3) (x := 4) (y := 1)
    (by decide) (by decide) (by decide) (by decide) m
  have hself : emultiplicity (3 : ℕ) 3 = 1 :=
    (Nat.finiteMultiplicity_iff.mpr ⟨by decide, by decide⟩).emultiplicity_self
  simp only [one_pow, show (4:ℕ)-1 = 3 from rfl, hself] at hl
  rw [pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity, hl]
  rw [Nat.cast_add, Nat.cast_one, add_comm 1, ENat.add_le_add_iff_right (by simp)]

theorem threePeriod {p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hpow : 2^p % 3^k = 1)
    (hmin : ∀ b, 0 < b → b < p → 2^b % 3^k ≠ 1) :
    p = 2*3^(k-1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hq : 1 < 3^(k+1) := one_lt_pow₀ (by decide) (by omega)
  have hcon : 1 ≡ 2^p [MOD 3^(k+1)] := by simpa [Nat.ModEq, Nat.mod_eq_of_lt hq] using hpow.symm
  have h3 : 1 ≡ 2^p [MOD 3] := hcon.of_dvd (by simp [pow_succ])
  have heven : Even p := by
    rcases Nat.even_or_odd p with he | ⟨m, hm⟩
    · exact he
    · exfalso
      have he : (2:ℕ)^(m+m+1) ≡ 2 [MOD 3] := by
        have hh := (show (2:ℕ)^2 ≡ 1 [MOD 3] by decide).pow m
        rw [pow_succ, ← two_mul, pow_mul]
        simpa using hh.mul_right 2
      rw [show p=m+m+1 by omega] at h3
      exact (by decide : ¬ (1 ≡ 2 [MOD 3])) (h3.trans he)
  obtain ⟨m, hm⟩ := heven
  have powers (a : ℕ) : (2:ℕ)^(a+a) = 4^a := by rw [← two_mul, pow_mul]; rfl
  have h4 : 1 ≤ 4^m := Nat.succ_le_of_lt (by positivity)
  have hd := (three_dvd_four k m).mp ((Nat.modEq_iff_dvd' h4).mp (by simpa [hm, powers] using hcon))
  have hle := Nat.le_of_dvd (show 0 < m by omega) hd
  have hreturns : 1 ≡ 4^(3^k) [MOD 3^(k+1)] :=
    (Nat.modEq_iff_dvd' (Nat.succ_le_of_lt (by positivity))).mpr ((three_dvd_four k _).mpr dvd_rfl)
  have hex : 2^(2*3^k) % 3^(k+1) = 1 := by
    simpa [Nat.ModEq, two_mul, powers, Nat.mod_eq_of_lt hq] using hreturns.symm
  have hupper : p ≤ 2*3^k := by
    by_contra! h
    exact hmin _ (by positivity) h hex
  change p = 2*3^k
  omega

theorem distinctRemainders {q E p : ℕ} (hq : 1 < q) (hodd : q % 2 = 1)
    (hcop : q.Coprime E) (hmin : ∀ b, 0 < b → b < p → 2^b % q ≠ 1) :
    Function.Injective (fun b : Fin p => (2^b.val * E) % q) := by
  have h₂ : q.Coprime 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hodd)
  have no (a b : Fin p) (hab : a.val < b.val)
      (he : (2^a.val * E) % q = (2^b.val * E) % q) : False := by
    have h := Nat.ModEq.cancel_right_of_coprime hcop he
    have hc : 2^a.val * 1 ≡ 2^a.val * 2^(b.val-a.val) [MOD q] := by
      simpa [← pow_add, Nat.add_sub_of_le hab.le] using h
    have hret := Nat.ModEq.cancel_left_of_coprime (h₂.pow_right a.val) hc
    apply hmin (b.val-a.val) (by omega) (by omega)
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hq] using hret.symm
  intro a b he
  rcases lt_trichotomy a.val b.val with hab | hab | hab
  · exact (no a b hab he).elim
  · exact Fin.ext hab
  · exact (no b a hab he.symm).elim

end PEqualNP.Outside.L_meta_29757

namespace PEqualNP.Outside.L_meta_29757

open Finset

theorem apportion {ι : Type} [DecidableEq ι] (u : Finset ι) (cap : ι → ℕ) (a : ℕ)
    (ha : a ≤ ∑ j ∈ u, cap j) :
    ∃ v : ι → ℕ, (∀ j, v j ≤ cap j) ∧ ∑ j ∈ u, v j = a := by
  induction u using Finset.induction_on generalizing a with
  | empty => exact ⟨fun _ => 0, by simp, by simpa [eq_comm] using ha⟩
  | @insert i u hi ih =>
    rw [sum_insert hi] at ha
    obtain ⟨v, hv, he⟩ := ih (a-cap i) (by omega)
    refine ⟨Function.update v i (min a (cap i)), ?_, ?_⟩
    · intro j
      by_cases h : j = i <;> simp [Function.update, h, hv]
    · rw [sum_insert hi, Function.update_self, sum_congr rfl (g := v) (by
        intro j hj
        exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) ..), he]
      omega

def remMass (q E b : ℕ) := (2^b*E) % q

theorem carryRule (q E b : ℕ) :
    2 * remMass q E b = q * (2*remMass q E b / q) + remMass q E (b+1) := by
  have hh : remMass q E (b+1) = (2*remMass q E b) % q := by
    simp [remMass, pow_succ', mul_assoc, Nat.mul_mod_mod]
  rw [hh, Nat.div_add_mod]

theorem packStep {q E b : ℕ} (v : Fin q → ℕ)
    (hv : (∑ j, v j) + remMass q E b = E) (hnext : remMass q E (b+1) ≤ E) :
    ∃ u d : Fin q → ℕ, (∑ j, u j) + remMass q E (b+1) = E ∧ (∑ j, d j) = E ∧
      ∀ j, 2 * (q*v j + remMass q E b) = q*d j + (q*u j + remMass q E (b+1)) := by
  let c := 2*remMass q E b / q
  let cap := fun j => 2*v j + c
  have hc : 2*remMass q E b = q*c + remMass q E (b+1) := carryRule q E b
  have hcap : (∑ j, cap j) + remMass q E (b+1) = 2*E := by
    simp only [cap, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    change 2 * (∑ j, v j) + q*c + remMass q E (b+1) = 2*E
    omega
  obtain ⟨u, hu, hsum⟩ := apportion univ cap (E - remMass q E (b+1)) (by omega)
  refine ⟨u, fun j => cap j - u j, by omega, ?_, ?_⟩
  · rw [sum_tsub_distrib univ (fun j _ => hu j)]
    omega
  · intro j
    have h := Nat.sub_add_cancel (hu j)
    change cap j - u j + u j = 2*v j+c at h
    calc
      _ = q*(2*v j) + 2*remMass q E b := by ring
      _ = q*(2*v j+c) + remMass q E (b+1) := by rw [hc]; ring
      _ = _ := by rw [← h]; ring

theorem packCycle {q E p : ℕ} (hq : 1 < q) (hE : E < q) (hp : 0 < p)
    (hpow : 2^p % q = 1) (horb : ∀ b < p, remMass q E b ≤ E) :
    ∃ (v d : ℕ → Fin q → ℕ), (∀ j, v 0 j = E) ∧ (∀ j, v p j = E) ∧
      (∀ b < p, (∑ j, d b j) = E) ∧
      ∀ b < p, ∀ j, 2*v b j = q*d b j + v (b+1) j := by
  classical
  have hzero : remMass q E 0 = E := by simp [remMass, Nat.mod_eq_of_lt hE]
  have hend : remMass q E p = E := by
    rw [remMass, Nat.mul_mod, hpow, one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hE]
  have extBound (b : ℕ) (hb : b ≤ p) : remMass q E b ≤ E := by
    rcases lt_or_eq_of_le hb with h | rfl
    · exact horb _ h
    · exact hend.le
  let shift (v : Fin q → ℕ) (b : ℕ) (j : Fin q) := q*v j + remMass q E b
  have build (k : ℕ) (hk : k ≤ p) :
      ∃ v d : ℕ → Fin q → ℕ, v 0 = 0 ∧ (∑ j, v k j) + remMass q E k = E ∧
        ∀ b < k, (∑ j, d b j) = E ∧ ∀ j, 2*shift (v b) b j =
            q*d b j + shift (v (b+1)) (b+1) j := by
    induction k with
    | zero => exact ⟨0, 0, rfl, by simp [hzero], by simp⟩
    | succ k ih =>
      obtain ⟨v, d, h0, hv, hd⟩ := ih (by omega)
      obtain ⟨u, e, hu, he, hstep⟩ := packStep (v k) hv (extBound _ hk)
      refine ⟨Function.update v (k+1) u, Function.update d k e, ?_, ?_, ?_⟩
      · simpa using h0
      · simpa using hu
      · intro b hb
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with h | rfl
        · simpa [Function.update_of_ne h.ne, Function.update_of_ne (show b ≠ k+1 by omega),
            Function.update_of_ne (show b+1 ≠ k+1 by omega)] using hd b h
        · simpa [shift] using And.intro he hstep
  obtain ⟨v, d, h0, hpv, hd⟩ := build p le_rfl
  have hsum : (∑ j, v p j) = 0 := by omega
  have hvp (j) : v p j = 0 := (sum_eq_zero_iff_of_nonneg (by simp)).mp hsum _ (mem_univ j)
  exact ⟨fun b => shift (v b) b, d, by simp [shift, h0, hzero], by simp [shift, hvp, hend],
    fun b hb => (hd b hb).1, fun b hb => (hd b hb).2⟩

end PEqualNP.Outside.L_meta_29757

namespace PEqualNP.Outside.L_meta_29757

def Dyad (x : ℝ) := ∃ b m : ℕ, 2^b * x = m

theorem dyadNat (m : ℕ) : Dyad (m : ℝ) := ⟨0, m, by simp⟩

theorem dyadMid {x y z : ℝ} (h : 2*z=x+y) (hx : Dyad x) (hy : Dyad y) : Dyad z := by
  obtain ⟨b,m,hm⟩ := hx
  obtain ⟨c,k,hk⟩ := hy
  refine ⟨b+c+1, 2^c*m+2^b*k, ?_⟩
  push_cast
  rw [pow_succ, pow_add]
  linear_combination (2^b*2^c)*h + 2^c*hm + 2^b*hk

theorem nonDyad {q E : ℕ} {x : ℝ} (hq : 1 < q) (hodd : q%2=1)
    (hc : q.Coprime E) (hx : q*x = E) : ¬ Dyad x := by
  rintro ⟨b,m,hm⟩
  have h₂ : q.Coprime 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hodd)
  have eq : (2:ℝ)^b * E = q*m := by
    linear_combination (q:ℝ)*hm - 2^b*hx
  have hd : q ∣ 2^b*E := ⟨m, by exact_mod_cast eq⟩
  have hh := Nat.eq_one_of_dvd_coprimes ((h₂.pow_right b).mul_right hc) dvd_rfl hd
  omega

theorem timePeriod {q E p s : ℕ} (hq : 1 < q) (hodd : q%2=1) (hc : q.Coprime E)
    (hmin : ∀ b, 0 < b → b < p → 2^b % q ≠ 1)
    (n : Fin s → Bool → Option (Fin s)) (hn : Absorbs n)
    (d : Fin s → Bool → Fin q → ℕ) (V : Fin s → Fin q → ℝ)
    (hV : ∀ j, Solves n (fun i b => (d i b j : ℝ)) (fun i => V i j))
    (hnon : ∀ i j, 0 ≤ V i j) (hbudget : ∀ i, (∑ j, V i j) ≤ E)
    (z : Fin s) (hz : ∀ j, (q:ℝ)*V z j = E)
    (T : Fin s → ℝ)
    (hT : ∀ i, 2*T i = 2 + (n i false).elim 0 T + (n i true).elim 0 T) :
    2 ≤ T z ∧ (T z = 2 → (∀ b < p, (2^b*E)%q ≤ E) ∧ p ≤ s) := by
  classical
  have nonT := minimumLaw n hn T (fun i => by linarith [hT i])
  have nonO (o : Option (Fin s)) : 0 ≤ o.elim 0 T := by cases o <;> simp [nonT]
  have oneT (i) : 1 ≤ T i := by linarith [hT i, nonO (n i false), nonO (n i true)]
  let j₀ : Fin q := ⟨0, by omega⟩
  let bad := fun i => ¬Dyad (V i j₀)
  have badZ : bad z := nonDyad hq hodd hc (hz j₀)
  have succBad (i) (hi : bad i) : ∃ b k, n i b = some k ∧ bad k := by
    by_contra! h
    apply hi
    have hh (b) : Dyad (Ends n (fun l c => (d l c j₀ : ℝ)) (fun l => V l j₀) i b) := by
      unfold Ends
      cases he : n i b with
      | none => exact dyadNat _
      | some k => exact not_not.mp (h b k he)
    exact dyadMid (hV j₀ i) (hh false) (hh true)
  let B := Finset.univ.filter bad
  obtain ⟨lo, hlo, hlmin⟩ := B.exists_min_image T ⟨z, by simpa [B] using badZ⟩
  have hminT (k) (hk : bad k) : T lo ≤ T k := hlmin k (by simpa [B] using hk)
  have low : 2 ≤ T lo := by
    obtain ⟨b,k,he,hb⟩ := succBad lo (by simpa [B] using hlo)
    have ht := hT lo
    have hk := hminT k hb
    cases b <;> simp [he] at ht
    · linarith [nonO (n lo true)]
    · linarith [nonO (n lo false)]
  have two (i) (hi : bad i) := low.trans (hminT i hi)
  refine ⟨two z badZ, ?_⟩
  intro ht
  let G := {i : Fin s // bad i ∧ T i = 2}
  have more (i : G) : ∃ (k : G) (e : Bool), ∀ j, 2*V i.val j = d i.val e j + V k.val j := by
    obtain ⟨b,k,he,hb⟩ := succBad i.val i.property.1
    have ht' := hT i.val
    rw [i.property.2] at ht'
    have hk := two k hb
    cases b with
    | false =>
      simp [he] at ht'
      have hk2 : T k = 2 := by linarith [nonO (n i.val true)]
      have hnone : n i.val true = none := by
        cases h' : n i.val true with
        | none => rfl
        | some a => simp [h'] at ht'; linarith [oneT a]
      exact ⟨⟨k,hb,hk2⟩,true,fun j => by simpa [Ends, he, hnone, add_comm] using hV j i.val⟩
    | true =>
      simp [he] at ht'
      have hk2 : T k = 2 := by linarith [nonO (n i.val false)]
      have hnone : n i.val false = none := by
        cases h' : n i.val false with
        | none => rfl
        | some a => simp [h'] at ht'; linarith [oneT a]
      exact ⟨⟨k,hb,hk2⟩,false,fun j => by simpa [Ends, he, hnone] using hV j i.val⟩
  choose step coin hstep using more
  let path (b : ℕ) : G := step^[b] ⟨z,badZ,ht⟩
  have whole (b : ℕ) (j : Fin q) : ∃ m : ℕ,
      (q:ℝ)*V (path b).val j + (q:ℝ)*m = (2:ℝ)^b * E := by
    induction b with
    | zero => exact ⟨0, by simpa [path] using hz j⟩
    | succ b ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨2*m + d (path b).val (coin (path b)) j, ?_⟩
      rw [show path (b+1) = step (path b) from Function.iterate_succ_apply' .., pow_succ]
      push_cast
      linear_combination 2*hm - (q:ℝ)*hstep (path b) j
  have residue (b : ℕ) (j : Fin q) : ∃ a : ℕ, (q:ℝ)*V (path b).val j = a ∧
      a % q = (2^b*E)%q := by
    obtain ⟨m,he⟩ := whole b j
    have hle' : (q:ℝ)*m ≤ 2^b*E := by linarith [mul_nonneg (Nat.cast_nonneg q) (hnon (path b).val j)]
    have hle : q*m ≤ 2^b*E := by exact_mod_cast hle'
    refine ⟨2^b*E-q*m, ?_, ?_⟩
    · rw [Nat.cast_sub hle]; push_cast; linarith
    · let a := 2^b*E-q*m
      have ha : a+q*m = 2^b*E := Nat.sub_add_cancel hle
      exact (show a%q = (a+q*m)%q by simp).trans (congrArg (· % q) ha)
  constructor
  · intro b _
    have lower (j : Fin q) : (((2^b*E)%q : ℕ) : ℝ) ≤ (q:ℝ)*V (path b).val j := by
      obtain ⟨a,ha,hr⟩ := residue b j
      rw [ha, ← hr]
      exact_mod_cast Nat.mod_le a q
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => lower j)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hs
    have hh := le_of_mul_le_mul_left (a := (q:ℝ)) hs (by exact_mod_cast (show 0 < q by omega))
    exact_mod_cast hh.trans (hbudget (path b).val)
  · suffices hinj : Function.Injective (fun b : Fin p => (path b.val).val) by
      simpa using Fintype.card_le_of_injective _ hinj
    intro a b he
    apply distinctRemainders hq hodd hc hmin
    obtain ⟨m,hm,ha⟩ := residue a.val j₀
    obtain ⟨k,hk,hb⟩ := residue b.val j₀
    change (path a.val).val = (path b.val).val at he
    rw [he, hk] at hm
    have hkm : k = m := by exact_mod_cast hm
    exact ha.symm.trans (hkm ▸ hb)

end PEqualNP.Outside.L_meta_29757

namespace PEqualNP.Outside.L_meta_29757

open Finset

section
variable {q N : ℕ}
variable (f : Fin q → Equiv.Perm (Fin N))

def row (j : Fin q) : Finset (Fin N × Fin N) :=
  univ.map ⟨fun x => (x,f j x), fun _ _ h => congrArg Prod.fst h⟩

@[simp] theorem mem_row (x y : Fin N) (j : Fin q) : (x,y) ∈ row f j ↔ f j x = y := by
  rw [row, mem_map]
  change (∃ a ∈ univ, (a,f j a) = (x,y)) ↔ _
  simp

@[simp] theorem card_row (j : Fin q) : (row f j).card = N := by simp [row]

def cost (B H : Fin N → Fin N → Bool) (D : Finset (Fin q)) :=
  (univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠
    xor (B z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))).card

def changed (B H : Fin N → Fin N → Bool) :=
  univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠ B z.1 z.2)

@[simp] theorem cost_empty (B H : Fin N → Fin N → Bool) :
    cost f B H ∅ = (changed B H).card := by simp [cost, changed]

theorem separateRows (hf : ∀ x, Function.Injective (fun j => f j x))
    {j k : Fin q} (hne : j ≠ k) : Disjoint (row f j) (row f k) := by
  rw [disjoint_left]
  rintro ⟨x,y⟩ h1 h2
  exact hne (hf x ((mem_row .. |>.mp h1).trans (mem_row .. |>.mp h2).symm))

theorem overlap (hf : ∀ x, Function.Injective (fun j => f j x)) (S : Finset (Fin N × Fin N))
    (D : Finset (Fin q)) :
    (S ∩ D.biUnion (row f)).card = ∑ j ∈ D, (S ∩ row f j).card := by
  rw [inter_biUnion, card_biUnion]
  intro j _ k _ hne
  exact (separateRows f hf hne).mono (inter_subset_right ..) (inter_subset_right ..)

theorem totalEdits (hf : ∀ x, Function.Injective (fun j => f j x)) (S : Finset (Fin N × Fin N)) :
    (∑ j, (S ∩ row f j).card) ≤ S.card := by
  rw [← overlap f hf]
  exact card_le_card (inter_subset_left ..)

theorem cost_id (hf : ∀ x, Function.Injective (fun j => f j x))
    (B H : Fin N → Fin N → Bool) (D : Finset (Fin q)) :
    cost f B H D + 2*(∑ j ∈ D, (changed B H ∩ row f j).card) =
      (changed B H).card + N*D.card := by
  let S := changed B H
  let U := D.biUnion (row f)
  have hU (x y) : (x,y) ∈ U ↔ y ∈ D.image (fun j => f j x) := by simp [U]
  have hcard : U.card = N*D.card := by
    rw [show U = D.biUnion (row f) from rfl, card_biUnion (fun _ _ _ _ h => separateRows f hf h)]
    simp [Nat.mul_comm]
  have hset : (univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠
      xor (B z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))) =
      (S \ U) ∪ (U \ S) := by
    ext ⟨x,y⟩
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_sdiff, hU, S, changed]
    by_cases h : y ∈ D.image (fun j => f j x) <;> cases H x y <;> cases B x y <;> simp [h]
  have hd : Disjoint (S \ U) (U \ S) := by exact disjoint_left.mpr (fun _ hs hu => (mem_sdiff.mp hs).2 (mem_sdiff.mp hu).1)
  change _ + 2*(∑ j ∈ D, (S ∩ row f j).card) = S.card + _
  unfold cost
  rw [hset, card_union_of_disjoint hd, ← overlap f hf, ← hcard]
  have h₁ := card_sdiff_add_card_inter S U
  have h₂ := card_sdiff_add_card_inter U S
  rw [inter_comm U S] at h₂
  change _ + 2*(S ∩ U).card = _
  omega

def toggled (B : Fin N → Fin N → Bool) (S : Finset (Fin N × Fin N)) (x y : Fin N) :=
  xor (B x y) (decide ((x,y) ∈ S))

@[simp] theorem changed_toggled (B : Fin N → Fin N → Bool) (S : Finset (Fin N × Fin N)) :
    changed B (toggled B S) = S := by
  ext ⟨x,y⟩
  by_cases h : (x,y) ∈ S <;> cases e : B x y <;> simp [changed, toggled, e, h]

theorem editSet (hf : ∀ x, Function.Injective (fun j => f j x))
    (d : Fin q → ℕ) (hN : ∀ j, d j ≤ N) :
    ∃ S : Finset (Fin N × Fin N), S.card = ∑ j, d j ∧ ∀ j, (S ∩ row f j).card = d j := by
  classical
  have ex (j) : ∃ W ⊆ row f j, W.card = d j := exists_subset_card_eq (by simpa using hN j)
  choose W hsub hcard using ex
  refine ⟨univ.biUnion W, ?_, ?_⟩
  · rw [card_biUnion (fun j _ k _ h => (separateRows f hf h).mono (hsub j) (hsub k))]
    simp [hcard]
  · intro j
    suffices he : univ.biUnion W ∩ row f j = W j by rw [he,hcard]
    ext z
    simp only [mem_inter, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨⟨k,hk⟩,hj⟩
      by_cases h : k=j
      · simpa [h] using hk
      · exact (disjoint_left.mp (separateRows f hf h) (hsub _ hk) hj).elim
    · intro h
      exact ⟨⟨j,h⟩, hsub _ h⟩
end

end PEqualNP.Outside.L_meta_29757

namespace PEqualNP.Outside.L_meta_29757

open Finset

theorem smallSet {q t : ℕ} (ht : 0 < t) (htq : t < q) (a : Fin q → ℝ) :
    ∃ D : Finset (Fin q), D.card = t ∧
      (q:ℝ)*(∑ j ∈ D, a j) ≤ (t:ℝ)*∑ j, a j ∧
      ((q:ℝ)*(∑ j ∈ D, a j) = (t:ℝ)*∑ j, a j → ∀ j, (q:ℝ)*a j = ∑ i, a i) := by
  classical
  let sets := univ.powersetCard t (α := Fin q)
  have hmem (D : Finset (Fin q)) : D ∈ sets ↔ D.card = t := by simp [sets]
  have hex : sets.Nonempty := by
    obtain ⟨D,_,hD⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q))) (n := t) (by simpa using htq.le)
    exact ⟨D,(hmem D).mpr hD⟩
  obtain ⟨D,hD,hmin⟩ := sets.exists_min_image (fun d => ∑ j ∈ d, a j) hex
  have hc := (hmem D).mp hD
  have hcmp (i) (hi : i ∈ D) (j) (hj : j ∉ D) : a i ≤ a j := by
    have hje : j ∉ D.erase i := fun e => hj (mem_of_mem_erase e)
    have hsize : (insert j (D.erase i)).card = t := by rw [card_insert_of_notMem hje, card_erase_of_mem hi, hc]; omega
    have he := hmin _ ((hmem _).mpr hsize)
    rw [sum_insert hje] at he
    linarith [sum_erase_add D a hi]
  obtain ⟨m,hm,hmax⟩ := D.exists_max_image a (card_pos.mp (hc ▸ ht))
  let S := ∑ j ∈ D, a j
  let C := ∑ j ∈ Dᶜ, a j
  have hcompl : (Dᶜ.card : ℝ) = q - t := by rw [card_compl, Fintype.card_fin, hc, Nat.cast_sub htq.le]
  have hsum : S+C = ∑ j, a j := sum_add_sum_compl D a
  have hupper := sum_le_sum (s := D) (g := fun _ => a m) hmax
  have hlower := sum_le_sum (s := Dᶜ) (f := fun _ => a m) (fun j hj => hcmp m hm j (mem_compl.mp hj))
  simp only [sum_const, nsmul_eq_mul, hc] at hupper
  simp only [sum_const, nsmul_eq_mul, hcompl] at hlower
  change S ≤ t*a m at hupper
  change ((q:ℝ)-t)*a m ≤ C at hlower
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hqt : (0:ℝ)<q-t := sub_pos.mpr (by exact_mod_cast htq)
  have bound : (q:ℝ)*S ≤ (t:ℝ)*(S+C) := by
    nlinarith [mul_nonneg hqt.le (sub_nonneg.mpr hupper), mul_nonneg ht'.le (sub_nonneg.mpr hlower)]
  refine ⟨D,hc, hsum ▸ bound, ?_⟩
  intro heq
  change (q:ℝ)*S = (t:ℝ)*_ at heq
  rw [← hsum] at heq
  have eS : S = t*a m := by
    by_contra! hn
    have he := lt_of_le_of_ne hupper hn
    nlinarith [mul_pos hqt (sub_pos.mpr he), mul_nonneg ht'.le (sub_nonneg.mpr hlower)]
  have eC : C = ((q:ℝ)-t)*a m := by
    have eq : (t:ℝ)*(C-(q-t)*a m) = 0 := by linear_combination -heq + (q-t)*eS
    exact sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left ht'.ne')
  have all (j) : a j = a m := by
    by_cases hj : j ∈ D
    · exact (sum_eq_sum_iff_of_le hmax).mp (by simpa [sum_const, hc, nsmul_eq_mul] using eS) j hj
    · have k := (sum_eq_sum_iff_of_le (s := Dᶜ) (f := fun _ => a m) (g := a)
          (fun l hl => hcmp m hm l (mem_compl.mp hl))).mp (by simpa [nsmul_eq_mul,hcompl] using eC.symm)
      exact (k j (mem_compl.mpr hj)).symm
  intro j
  simp only [all, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem gameBound {q N t E : ℕ} (hq : 1 < q) (hqN : q ≤ N) (hE : E < q)
    (ht : q < 2*t) (htq : t < q) (e : ℝ) (a : Fin q → ℝ)
    (hes : (∑ j, a j) ≤ e) (heE : e ≤ E)
    (pay : Finset (Fin q) → ℝ)
    (hpay : ∀ D, pay D = e + (N:ℝ)*D.card - 2*∑ j ∈ D, a j) :
    let target := ((q*N*t-(2*t-q)*E : ℕ):ℝ)/(q:ℝ)
    (∃ D, D.card = t ∧ target ≤ pay D) ∧
      ((∀ D : Finset (Fin q), D.card=t → pay D ≤ target) → ∀ j, (q:ℝ)*a j = E) := by
  dsimp only
  have ht0 : 0 < t := by omega
  obtain ⟨D, hD, hlo, hequal⟩ := smallSet ht0 htq a
  have hqt : 2*t-q ≤ t := by omega
  have hn1 : (2*t-q)*E ≤ q*N*t := calc
    _ ≤ t*N := Nat.mul_le_mul hqt (by omega)
    _ ≤ _ := by rw [mul_comm t, mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hq' : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have ht' : 0 < (t:ℝ) := by exact_mod_cast ht0
  have hcoeff : 0 < 2*(t:ℝ)-q := sub_pos.mpr (by exact_mod_cast ht)
  let goal := ((q*N*t-(2*t-q)*E : ℕ):ℝ)/(q:ℝ)
  have hgoal : (q:ℝ)*goal = (q:ℝ)*N*t - (2*(t:ℝ)-q)*E := by
    dsimp [goal]
    rw [Nat.cast_sub hn1]
    push_cast [Nat.cast_sub ht.le]
    field_simp
  have hg : pay D = e + (N:ℝ)*t - 2*∑ j ∈ D, a j := hD ▸ hpay D
  have hgap : (q:ℝ)*(pay D-goal) =
      (2*(t:ℝ)-q)*(E-e) + 2*t*(e-∑ j, a j) +
        2*((t:ℝ)*(∑ j, a j)-q*(∑ j ∈ D, a j)) := by
    rw [mul_sub,hgoal,hg]
    ring
  have h₁ := mul_nonneg hcoeff.le (sub_nonneg.mpr heE)
  have h₂ := mul_nonneg (show 0 ≤ 2*(t:ℝ) by positivity) (sub_nonneg.mpr hes)
  have h₃ := sub_nonneg.mpr hlo
  have low : goal ≤ pay D := by
    apply sub_nonneg.mp
    apply nonneg_of_mul_nonneg_right (a := (q:ℝ)) _ hq'
    linarith
  refine ⟨⟨D,hD,low⟩, ?_⟩
  intro h
  have heq := le_antisymm (h D hD) low
  change pay D = goal at heq
  rw [heq, sub_self, mul_zero] at hgap
  have e₁ : e = E := by
    by_contra! hn
    linarith [mul_pos hcoeff (sub_pos.mpr (lt_of_le_of_ne heE hn))]
  have e₂ : (∑ j, a j) = e := by
    by_contra! hn
    linarith [mul_pos (show 0 < 2*(t:ℝ) by positivity) (sub_pos.mpr (lt_of_le_of_ne hes hn))]
  have e₃ : (q:ℝ)*(∑ j ∈ D, a j) = (t:ℝ)*∑ j, a j := by linarith
  exact fun j => (hequal e₃ j).trans (e₂.trans e₁)

end PEqualNP.Outside.L_meta_29757

namespace PEqualNP.Outside.L_meta_29757

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def gateOK (g : Gate) := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

def legal (N : ℕ) (C : Circuit) := ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
  ∀ g ∈ C.gates, gateOK g

def table {N : ℕ} (C : Circuit) (x y : Fin N) := C.eval (oneEach x y)

def fits {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N)) (E : ℕ) (base C : Circuit) :=
  legal N C ∧ C.gates.take base.size = base.gates ∧ C.size ≤ base.size+2*E+3 ∧
    cost f (table base) (table C) ∅ ≤ E

def atBit {N : ℕ} (C : Circuit) (w : ℕ) (F : Fin N → Fin N → Bool) :=
  w < N+N+C.size ∧ ∀ x y, (C.wires (oneEach x y)).getD w false = F x y

theorem wireLength (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length+C.size := by
  rcases C with ⟨gs,o⟩
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires, Circuit.size]
  | append_singleton gs g ih => simp [Circuit.wires, Circuit.size, List.foldl_append] at ih ⊢; omega

theorem carryBit {N : ℕ} {A B : Circuit} (hab : A.gates <+: B.gates)
    {w : ℕ} {F : Fin N → Fin N → Bool} (h : atBit A w F) : atBit B w F := by
  obtain ⟨s,hs⟩ := hab
  have hle : A.size ≤ B.size := by simp [Circuit.size,← hs]
  refine ⟨by have := h.1; omega, ?_⟩
  intro x y
  rw [← h.2 x y]
  let v := A.wires (oneEach x y)
  have hlen : w < v.length := by simpa [v,wireLength,oneEach] using h.1
  have prop (s : List Gate) : ∀ (l : List Bool), w < l.length →
      (s.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) l).getD w false
      = l.getD w false := by
    induction s with
    | nil => simp
    | cons g s ih =>
      intro l hl
      rw [List.foldl_cons, ih _ (by simp; omega), List.getD_eq_getElem?_getD,
        List.getElem?_append_left hl, ← List.getD_eq_getElem?_getD]
  unfold Circuit.wires
  rw [← hs, List.foldl_append]
  exact prop s v hlen

def snoc (N : ℕ) (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], N+N+C.size⟩

theorem snocLeg {N : ℕ} {C : Circuit} (hc : legal N C) (g : Gate) (hg : gateOK g)
    (hi : ∀ i ∈ g.inputs, i < N+N+C.size) : legal N (snoc N C g) := by
  refine ⟨?_,by simp [snoc,Circuit.size],?_⟩
  · intro j hj i h
    simp only [snoc, List.length_append, List.length_singleton] at hj
    by_cases he : j < C.gates.length
    · apply hc.1 j he i
      simpa [gateAt,snoc,List.getD_eq_getElem?_getD,List.getElem?_append_left he] using h
    · have e : j = C.gates.length := by omega
      subst j
      apply hi
      simpa [gateAt,snoc,List.getD_eq_getElem?_getD] using h
  · intro a ha
    simp only [snoc,List.mem_append,List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hc.2.2 a ha
    · exact hg

theorem snocEval {N : ℕ} (C : Circuit) (g : Gate) (x y : Fin N) :
    table (snoc N C g) x y =
      g.op.eval (g.inputs.map fun i => (C.wires (oneEach x y)).getD i false) := by
  have hlen : (C.wires (oneEach x y)).length = N+N+C.size := by simp [wireLength,oneEach]
  unfold table Circuit.eval
  change (((C.gates++[g]).foldl _ (oneEach x y)).getD (N+N+C.size) false) = _
  rw [← hlen, List.foldl_append]
  change ((C.wires (oneEach x y)) ++ [_]).getD (C.wires (oneEach x y)).length false = _
  simp [List.getD_eq_getElem?_getD, Circuit.wires]

theorem endBit {N : ℕ} {C : Circuit} (hc : legal N C) : atBit C C.output (@table N C) :=
  ⟨hc.2.1, by intros; rfl⟩

theorem addBinary {N : ℕ} {C : Circuit} (hc : legal N C) {a b : ℕ}
    {A B : Fin N → Fin N → Bool} (ha : atBit C a A) (hb : atBit C b B) (isAnd : Bool) :
    ∃ K : Circuit, C.gates <+: K.gates ∧ legal N K ∧ K.size = C.size+1 ∧
      atBit K K.output (fun x y => if isAnd then A x y && B x y else A x y || B x y) := by
  let g : Gate := ⟨if isAnd then .and else .or,[a,b]⟩
  have hgood := snocLeg hc g (by cases isAnd <;> simp [g,gateOK])
    (by intro i hi; simp [g] at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
  refine ⟨snoc N C g, ⟨[g],rfl⟩, hgood, by simp [snoc,Circuit.size], hgood.2.1, ?_⟩
  intro x y
  change table (snoc N C g) x y = _
  rw [snocEval]
  cases isAnd <;> simp [-List.getD_eq_getElem?_getD,g,GateOp.eval,ha.2 x y,hb.2 x y]

theorem addNot {N : ℕ} {C : Circuit} (hc : legal N C) {a : ℕ} {A : Fin N → Fin N → Bool}
    (ha : atBit C a A) : ∃ K : Circuit, C.gates <+: K.gates ∧ legal N K ∧ K.size = C.size+1 ∧
      atBit K K.output (fun x y => !(A x y)) := by
  let g : Gate := ⟨.not,[a]⟩
  have hgood := snocLeg hc g (by simp [g,gateOK])
    (by intro i hi; simp [g] at hi; simpa [hi] using ha.1)
  refine ⟨snoc N C g,⟨[g],rfl⟩,hgood, by simp [snoc,Circuit.size],hgood.2.1,?_⟩
  intro x y
  change table (snoc N C g) x y = _
  simp [-List.getD_eq_getElem?_getD,snocEval,g,GateOp.eval,ha.2 x y]

theorem addCell {N : ℕ} {C : Circuit} (hc : legal N C) (p : Fin N × Fin N) :
    ∃ K : Circuit, C.gates <+: K.gates ∧ legal N K ∧ K.size = C.size+1 ∧
      atBit K K.output (fun x y => decide ((x,y)=p)) := by
  let O : Circuit := ⟨[],0⟩
  have hp : O.gates <+: C.gates := ⟨C.gates,rfl⟩
  have h1 : atBit O p.1.val (fun x _ => decide (p.1=x)) := by
    refine ⟨by have := p.1.isLt; dsimp [O,Circuit.size]; omega,?_⟩
    intro x y
    simp [O,Circuit.wires,oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,p.1.isLt]
  have h2 : atBit O (N+p.2.val) (fun _ y => decide (p.2=y)) := by
    refine ⟨by have := p.2.isLt; dsimp [O,Circuit.size]; omega,?_⟩
    intro x y
    simp [O,Circuit.wires,oneEach,List.getD_eq_getElem?_getD]
  obtain ⟨K,he,hg,hl,hb⟩ := addBinary hc (carryBit hp h1) (carryBit hp h2) true
  exact ⟨K,he,hg,hl,hb.1,fun x y => by simpa [Prod.ext_iff, eq_comm] using hb.2 x y⟩

theorem addCells {N : ℕ} {C : Circuit} (hc : legal N C) (S : Finset (Fin N × Fin N)) (hs : S.Nonempty) :
    ∃ K : Circuit, C.gates <+: K.gates ∧ legal N K ∧ K.size+1 = C.size+2*S.card ∧
      atBit K K.output (fun x y => decide ((x,y)∈S)) := by
  induction S using Finset.induction_on with
  | empty => simp at hs
  | @insert a S ha ih =>
    rw [Finset.card_insert_of_notMem ha]
    rcases S.eq_empty_or_nonempty with rfl | hne
    · obtain ⟨K,he,hg,hl,hb⟩ := addCell hc a
      exact ⟨K,he,hg,by simp [hl],hb.1,fun x y => by simpa using hb.2 x y⟩
    · obtain ⟨K,he,hg,hl,hb⟩ := ih hne
      obtain ⟨A,hA,hgA,hlA,hbA⟩ := addCell hg a
      obtain ⟨B,hB,hgB,hlB,hbB⟩ := addBinary hgA hbA (carryBit hA hb) false
      exact ⟨B,(he.trans hA).trans hB,hgB,by omega,hbB.1,fun x y => by simpa using hbB.2 x y⟩

theorem compileSet {q N E : ℕ} (f : Fin q → Equiv.Perm (Fin N)) {base : Circuit} (hbase : legal N base)
    (S : Finset (Fin N × Fin N)) (hE : S.card = E) (he : 0 < E) :
    ∃ C, fits f E base C ∧ @table N C = toggled (table base) S := by
  obtain ⟨A,hA,gA,lA,bA⟩ := addCells hbase S (Finset.card_pos.mp (hE ▸ he))
  have bb := carryBit hA (endBit hbase)
  obtain ⟨B,hB,gB,lB,bB⟩ := addBinary gA bb bA false
  obtain ⟨K,hK,gK,lK,bK⟩ := addBinary gB (carryBit hB bb) (carryBit hB bA) true
  obtain ⟨L,hL,gL,lL,bL⟩ := addNot gK bK
  obtain ⟨M,hM,gM,lM,bM⟩ := addBinary gL (carryBit (hK.trans hL) bB) bL true
  have eq : @table N M = toggled (table base) S := by
    funext x y
    change (M.wires _).getD M.output false = _
    rw [bM.2 x y]
    change ((_ || _) && !(_ && _)) = xor _ _
    cases table base x y <;> cases decide ((x,y)∈S) <;> rfl
  have htake := (((hA.trans hB).trans hK).trans hL).trans hM
  obtain ⟨tail,htail⟩ := htake
  refine ⟨M, ⟨gM,by simp [← htail,Circuit.size],by omega,?_⟩,eq⟩
  rw [eq,cost_empty,changed_toggled,hE]

end PEqualNP.Outside.L_meta_29757

namespace PEqualNP.Outside.L_meta_29757

open Finset PEqualNP.CircuitLowerBounds

variable {q N s : ℕ}

noncomputable def goalLoss (q N t E : ℕ) := ((q*N*t-(2*t-q)*E : ℕ) : ℝ)/(q : ℝ)

def law (f : Fin q → Equiv.Perm (Fin N)) (B : Fin N → Fin N → Bool)
    (n : Fin s → Bool → Option (Fin s)) (H : Fin s → Bool → Fin N → Fin N → Bool)
    (L : Fin s → Finset (Fin q) → ℝ) (T : Fin s → ℝ) :=
  Absorbs n ∧ (∀ i, 2*T i = 2 + ∑ b : Bool, (n i b).elim 0 T) ∧
    ∀ i D, 2*L i D = ∑ b : Bool, (n i b).elim (cost f B (H i b) D : ℝ) (fun j => L j D)

def realize (f : Fin q → Equiv.Perm (Fin N)) (base : Circuit) (E t s : ℕ) (fast : Bool) :=
  ∃ (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (C : Fin s → Bool → Circuit)
    (L : Fin s → Finset (Fin q) → ℝ) (T : Fin s → ℝ),
    law f (table base) n (fun i b => table (C i b)) L T ∧ (∀ i b, fits f E base (C i b)) ∧
      (∀ D : Finset (Fin q), D.card = t → L z D = goalLoss q N t E) ∧ (fast = true → T z = 2)

theorem boolSum (u : Bool → ℝ) : ∑ b, u b = u false + u true := by simp [Fintype.sum_bool, add_comm]

theorem lowerGame {E p t : ℕ} (hq : 1 < q) (hodd : q % 2 = 1) (hE : E < q)
    (hcop : q.Coprime E) (hmin : ∀ b, 0 < b → b < p → 2^b % q ≠ 1)
    (hqN : q ≤ N) (ht : q < 2*t) (htq : t < q)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (B : Fin N → Fin N → Bool) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
    (H : Fin s → Bool → Fin N → Fin N → Bool) (L : Fin s → Finset (Fin q) → ℝ) (T : Fin s → ℝ)
    (hLaw : law f B n H L T) (herr : ∀ i b, cost f B (H i b) ∅ ≤ E) :
    (∃ D : Finset (Fin q), D.card = t ∧ goalLoss q N t E ≤ L z D) ∧
      ((∀ D : Finset (Fin q), D.card = t → L z D ≤ goalLoss q N t E) →
        2 ≤ T z ∧ (T z = 2 → (∀ b < p, (2^b*E)%q ≤ E) ∧ p ≤ s)) := by
  obtain ⟨hn,hT,hL⟩ := hLaw
  let A := mean n hn
  let marks := fun i b => changed B (H i b)
  let total := fun i b => ((marks i b).card : ℝ)
  let d := fun i b j => (marks i b ∩ row f j).card
  let R := fun (j : Fin q) (i : Fin s) (b : Bool) => (d i b j : ℝ)
  let V := fun (i : Fin s) (j : Fin q) => A (R j) i
  have hnon (i j) : 0 ≤ V i j := mean_nonneg n hn _ (fun _ _ => Nat.cast_nonneg _) i
  have httle : A total ≤ fun _ => (E:ℝ) := by
    rw [← mean_const n hn E]
    apply mean_mono
    intro i b
    change ((marks i b).card : ℝ) ≤ E
    exact_mod_cast (show (marks i b).card ≤ E by simpa [marks] using herr i b)
  have sumBound : (∑ j, R j) ≤ total := by
    intro i b
    change ((∑ j, R j) i b) ≤ _
    simp only [Finset.sum_apply, R, total, d]
    exact_mod_cast totalEdits f hf (marks i b)
  have hvSum (i) : (∑ j, V i j) ≤ A total i := by
    have hh := mean_mono n hn sumBound i
    simpa [V, A, map_sum, Finset.sum_apply] using hh
  have payoff (D : Finset (Fin q)) :
      L z D = A total z + (N:ℝ)*D.card - 2*∑ j ∈ D, V z j := by
    let r := fun i b => (cost f B (H i b) D : ℝ)
    have he := eqMean n hn (r := r) (x := fun i => L i D)
      (fun i => by simpa only [boolSum, Ends, r] using hL i D)
    have idR : r = total + (fun _ _ => (N:ℝ)*D.card) - (2:ℝ) • ∑ j ∈ D, R j := by
      funext i b
      simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,r,total,R,d,marks]
      have hh := cost_id f hf B (H i b) D
      have hc : (cost f B (H i b) D : ℝ) + 2*(∑ j ∈ D, ((changed B (H i b) ∩ row f j).card : ℝ)) =
          ((changed B (H i b)).card : ℝ) + (N:ℝ)*D.card := by exact_mod_cast hh
      linarith
    have val := congrFun he z
    rw [idR, map_sub, map_add, map_smul, map_sum, mean_const] at val
    simpa [A,V, Finset.sum_apply] using val
  obtain ⟨hex,heq⟩ := gameBound hq hqN hE ht htq (A total z) (V z) (hvSum z) (httle z) (L z) payoff
  refine ⟨hex,fun h => ?_⟩
  exact timePeriod hq hodd hcop hmin n hn d V (fun j => mean_solves n hn _) hnon
    (fun i => (hvSum i).trans (httle i)) z (heq h) T
    (fun i => by simpa only [boolSum,add_assoc] using hT i)

theorem compileGame {E t : ℕ} (hq : 1 < q) (he : 0 < E) (hE : E < q) (hqN : q ≤ N)
    (ht : q < 2*t) (htq : t < q)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : Circuit) (hbase : legal N base)
    (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (hn : Absorbs n)
    (d : Fin s → Bool → Fin q → ℕ) (hd : ∀ i b, ∑ j, d i b j = E)
    (V : Fin s → Fin q → ℝ) (hV : ∀ j, Solves n (fun i b => (d i b j : ℝ)) (fun i => V i j))
    (hz : ∀ j, (q:ℝ)*V z j = E) (T : Fin s → ℝ)
    (hT : ∀ i, 2*T i = 2 + (n i false).elim 0 T + (n i true).elim 0 T)
    (fast : Bool) (hfast : fast = true → T z = 2) : realize f base E t s fast := by
  classical
  have hlim (i b j) : d i b j ≤ N := by
    have hh := Finset.single_le_sum (f := d i b) (fun _ _ => Nat.zero_le _) (mem_univ j)
    rw [hd i b] at hh
    omega
  choose S hSc hSj using fun i b => editSet f hf (d i b) (hlim i b)
  choose C hg htable using fun i b => compileSet f hbase (S i b) ((hSc i b).trans (hd i b)) he
  let score (v : Fin q → ℝ) (D : Finset (Fin q)) := (E:ℝ) + N*D.card - 2*∑ j ∈ D, v j
  let L := fun i => score (V i)
  have pay (i b D) : (cost f (table base) (table (C i b)) D : ℝ) = score (fun j => d i b j) D := by
    have hh := cost_id f hf (table base) (table (C i b)) D
    rw [htable, changed_toggled] at hh
    simp only [hSj, hSc,hd] at hh
    have h' : (cost f (table base) (toggled (table base) (S i b)) D : ℝ) + 2*∑ j ∈ D, (d i b j:ℝ) =
        E + (N:ℝ)*D.card := by exact_mod_cast hh
    rw [htable]
    dsimp [score]
    linarith
  refine ⟨z,n,C,L,T, ⟨hn,fun i => by simpa only [boolSum, add_assoc] using hT i,?_⟩,hg,?_,hfast⟩
  · intro i D
    let val := fun b j => (n i b).elim (d i b j:ℝ) (fun k => V k j)
    have hsum : 2*(∑ j ∈ D, V i j) = (∑ j ∈ D, val false j) + ∑ j ∈ D, val true j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => hV j i)
    have hh (b) : (n i b).elim (cost f (table base) (table (C i b)) D : ℝ) (fun j => L j D) =
        score (val b) D := by
      cases hh : n i b <;> simp [L, val, hh, pay]
    rw [boolSum, hh, hh]
    dsimp only [L,score]
    linarith
  · intro D hD
    have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hsum : (q:ℝ)*(∑ j ∈ D, V z j) = t*E := by rw [Finset.mul_sum]; simp [hz,hD,nsmul_eq_mul]
    have hqt : 2*t-q ≤ t := by omega
    have hn1 : (2*t-q)*E ≤ q*N*t := calc
      _ ≤ t*N := Nat.mul_le_mul hqt (by omega)
      _ ≤ _ := by rw [mul_comm t, mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
    dsimp only [L, score, goalLoss]
    rw [hD, Nat.cast_sub hn1]
    push_cast [Nat.cast_sub ht.le]
    apply (eq_div_iff hq').mpr
    linear_combination -2*hsum

end PEqualNP.Outside.L_meta_29757

namespace PEqualNP.Outside.L_meta_29757

open Finset PEqualNP.CircuitLowerBounds

theorem downAbsorbs {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (h : ∀ i j, n i false = some j → j.val < i.val) : Absorbs n := by
  refine ⟨fun _ => false, ?_⟩
  let F := fun x : Option (Fin s) => x.bind (fun i => n i false)
  have fixed (b : ℕ) : F^[b] none = none := Function.iterate_fixed (f := F) rfl b
  have ends (b : ℕ) : ∀ i : Fin s, i.val < b → F^[b] (some i) = none := by
    induction b with
    | zero => simp
    | succ b ih =>
      intro i hi
      rw [Function.iterate_succ_apply]
      change F^[b] (n i false) = none
      cases he : n i false with
      | none => exact fixed _
      | some j => exact ih _ (by have := h _ _ he; omega)
  exact fun i => ends _ i i.isLt

theorem fastGame {q E p N t : ℕ} (hq : 1 < q) (he : 0 < E) (hE : E < q)
    (hp : 0 < p) (hpow : 2^p%q=1) (hqN : q ≤ N) (ht : q < 2*t) (htq : t < q)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : Circuit) (hbase : legal N base) (horb : ∀ b < p, (2^b*E)%q ≤ E) :
    realize f base E t p true := by
  obtain ⟨v,d,h0,hpEnd,hsum,hstep⟩ := packCycle hq hE hp hpow horb
  let z : Fin p := ⟨0,hp⟩
  let succ (i : Fin p) : Fin p := if h : i.val+1 < p then ⟨i.val+1,h⟩ else z
  let n (i : Fin p) (b : Bool) := if b then some (succ i) else none
  let V (i : Fin p) (j : Fin q) := (v i.val j : ℝ)/q
  have hn := downAbsorbs n (by simp [n])
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  refine compileGame hq he hE hqN ht htq f hf base hbase z n hn (fun i _ => d i.val)
    (fun i _ => hsum _ i.isLt) V ?_ ?_ (fun _ => 2) ?_ _ (by simp)
  · intro j i
    have eq : v (succ i).val j = v (i.val+1) j := by
      dsimp only [succ]
      split
      · rfl
      · rename_i h
        have h' : i.val+1=p := by omega
        simp [h',z,h0,hpEnd]
    have hs : 2*(v i.val j:ℝ) = (q:ℝ)*d i.val j + v (i.val+1) j := by exact_mod_cast hstep _ i.isLt j
    simp only [Ends,n,Bool.false_eq_true,ite_false,ite_true,Option.elim_none,Option.elim_some,V,eq]
    field_simp
    linarith
  · intro j
    simp only [V,z,h0]
    field_simp
  · intro i
    norm_num [n]

theorem anyTime {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (hn : Absorbs n) :
    ∃ T : Fin s → ℝ, ∀ i, 2*T i = 2 + (n i false).elim 0 T + (n i true).elim 0 T := by
  obtain ⟨T,hT⟩ := LinearMap.surjective_of_injective (uniqueDrift n hn) (fun _ => 2)
  refine ⟨T,fun i => ?_⟩
  have eq := congrFun hT i
  change 2*T i - _ - _ = 2 at eq
  linarith

theorem shortCoin {q h : ℕ} (hq : 1 < q) (hh : q ≤ 2^h) :
    ∃ (z : Fin h) (n : Fin h → Bool → Option (Fin h)) (r : Fin h → Bool → Bool) (w : Fin h → ℝ),
      Absorbs n ∧ Solves n (fun i b => if r i b then 1 else 0) w ∧ (q:ℝ)*w z = 1 := by
  have hp : 0 < h := by by_contra! h0; simp [show h=0 by omega] at hh; omega
  let z : Fin h := ⟨h-1,by omega⟩
  let m := 2^h-q
  let bit (i : ℕ) := (m/2^i)%2
  let n (i : Fin h) (b : Bool) : Option (Fin h) := if b then
      (if bit i.val = 1 then some z else none)
    else if i.val=0 then none else some ⟨i.val-1,by omega⟩
  let r (i : Fin h) (b : Bool) := !b && decide (i.val=0)
  let W (k : ℕ) : ℝ := (1 + ((m%2^k : ℕ) : ℝ)/q)/2^k
  let w (i : Fin h) := W (i.val+1)
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast (show q≠0 by omega)
  have hroot : w z = 1/(q:ℝ) := by
    have hz : z.val+1=h := by dsimp [z]; omega
    have hm : m < 2^h := by dsimp [m]; omega
    simp only [w,W,hz,Nat.mod_eq_of_lt hm,m,Nat.cast_sub hh,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
    ring
  have hrem (k : ℕ) : m%2^(k+1) = m%2^k + 2^k*bit k := by
    rw [pow_succ]
    exact Nat.mod_mul
  have recW (k : ℕ) : 2*W (k+1) = W k + (bit k:ℝ)/q := by
    unfold W
    rw [hrem k]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_succ]
    field_simp
    ring
  have hn := downAbsorbs n (by
    intro i j he
    simp only [n,Bool.false_eq_true,ite_false] at he
    split at he
    · contradiction
    · cases he; simp; omega)
  refine ⟨z,n,r,w,hn,?_,by rw [hroot]; field_simp⟩
  intro i
  have hl : Ends n (fun i b => if r i b then (1:ℝ) else 0) w i false = W i.val := by
    by_cases hi : i.val=0
    · simp [Ends,n,r,hi,W,Nat.mod_one]
    · have hs : i.val-1+1 = i.val := by omega
      simp [Ends,n,r,hi,w,hs]
  have hr : Ends n (fun i b => if r i b then (1:ℝ) else 0) w i true = (bit i.val:ℝ)/q := by
    have hb : bit i.val < 2 := Nat.mod_lt _ (by decide)
    by_cases h1 : bit i.val=1
    · simp [Ends,n,r,h1,hroot]
    · simp [Ends,n,r,show bit i.val=0 by omega]
  rw [hl,hr]
  exact recW _

theorem slowGame {q E N t h : ℕ} (hq : 1 < q) (he : 0 < E) (hE : E < q)
    (hqN : q ≤ N) (ht : q < 2*t) (htq : t < q)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : Circuit) (hbase : legal N base) (hEq : E+1=q) (hh : q ≤ 2^h) :
    realize f base E t h false := by
  obtain ⟨z,n,r,w,hn,hw,hz⟩ := shortCoin hq hh
  obtain ⟨T,hT⟩ := anyTime n hn
  let j₀ : Fin q := ⟨0,by omega⟩
  let a (j : Fin q) : ℕ := if j=j₀ then E else 0
  let b (j : Fin q) : ℕ := if j=j₀ then 0 else 1
  have ha : (∑ j, a j) = E := by simp [a]
  have hb : (∑ j, b j) = E := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀)]
    have e (j) (hj : j ∈ univ.erase j₀) : b j = 1 := if_neg (ne_of_mem_erase hj)
    rw [Finset.sum_congr rfl e]
    simp [b,Finset.card_erase_of_mem,hEq.symm]
  let d (i : Fin h) (c : Bool) (j : Fin q) := if r i c then a j else b j
  let V (i : Fin h) (j : Fin q) := (b j:ℝ) + ((a j:ℝ)-b j)*w i
  refine compileGame hq he hE hqN ht htq f hf base hbase z n hn d
    (fun i c => by cases h' : r i c <;> simp [d,h',ha,hb]) V ?_ ?_ T hT false (by simp)
  · intro j i
    have es (c) : Ends n (fun i c => (d i c j:ℝ)) (fun k => V k j) i c =
        b j + ((a j:ℝ)-b j)*Ends n (fun i c => if r i c then (1:ℝ) else 0) w i c := by
      cases hn' : n i c <;> cases h' : r i c <;> simp [Ends,hn',h',d,V]
    rw [es,es]
    dsimp only [V]
    linear_combination ((a j:ℝ)-b j)*hw i
  · intro j
    have hEq' : (E:ℝ)+1=q := by exact_mod_cast hEq
    by_cases hj : j=j₀ <;> simp [V,a,b,hj]
    · linear_combination E*hz
    · linear_combination -hz - hEq'

end PEqualNP.Outside.L_meta_29757

theorem PEqualNP.Outside.L_meta_29757 : (∀ (q E p : ℕ), 1 < q → q % 2 = 1 → 0 < E → E < q → Nat.Coprime q E →
  0 < p → 2^p % q = 1 → (∀ b, 0 < b → b < p → 2^b % q ≠ 1) →
  ∀ (N t : ℕ), q ≤ N → q < 2*t → t < q →
  let X := Fin N
  let I := Fin q
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun C : Circ =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
  let table := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  ∀ (base : Circ), legal base → ∀ f : I → Equiv.Perm X,
    (∀ x : X, Function.Injective (fun j => f j x)) →
    let loss := fun (H : X → X → Bool) (D : Finset I) =>
      ((Finset.univ : Finset (X × X)).filter (fun z => H z.1 z.2 ≠
        xor (table base z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))).card
    let fits := fun C : Circ => legal C ∧ C.gates.take base.size = base.gates ∧
      C.size ≤ base.size+2*E+3 ∧ loss (table C) ∅ ≤ E
    let ideal := ((q*N*t-(2*t-q)*E : ℕ) : ℝ)/(q : ℝ)
    let orbit := ∀ b < p, (2^b*E) % q ≤ E
    let law := fun (s : ℕ) (n : Fin s → Bool → Option (Fin s))
        (H : Fin s → Bool → X → X → Bool)
        (L : Fin s → Finset I → ℝ) (T : Fin s → ℝ) =>
      (∃ c : Fin s → Bool, ∀ i : Fin s,
        (fun x : Option (Fin s) => x.bind (fun j => n j (c j)))^[s] (some i) = none) ∧
      (∀ i, 2*T i = 2 + ∑ b : Bool, (n i b).elim 0 T) ∧
      ∀ i D, 2*L i D = ∑ b : Bool, (n i b).elim (loss (H i b) D : ℝ) (fun j => L j D)
    let realize := fun (s : ℕ) (fast : Bool) =>
      ∃ (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (C : Fin s → Bool → Circ)
        (L : Fin s → Finset I → ℝ) (T : Fin s → ℝ),
        law s n (fun i b => table (C i b)) L T ∧ (∀ i b, fits (C i b)) ∧
        (∀ D : Finset I, D.card = t → L z D = ideal) ∧ (fast = true → T z = 2)
    (∀ (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
        (H : Fin s → Bool → X → X → Bool) (L : Fin s → Finset I → ℝ) (T : Fin s → ℝ),
      law s n H L T → (∀ i b, loss (H i b) ∅ ≤ E) →
      (∃ D : Finset I, D.card = t ∧ ideal ≤ L z D) ∧
      ((∀ D : Finset I, D.card = t → L z D ≤ ideal) →
        2 ≤ T z ∧ (T z = 2 → orbit ∧ p ≤ s))) ∧
    (orbit → realize p true) ∧
    (E+1 = q → ∀ h : ℕ, q ≤ 2^h → ∃ s ≤ 2*h, realize s false) ∧
    (∀ k : ℕ, 0 < k → q = 3^k → p = 2*3^(k-1))) := by
  intro q E p hq hodd he hE hcop hp hpow hmin N t hqN ht htq
  intro X I Circ legal' table' base hbase f hf
  intro loss' fits' ideal orbit law' realize'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s z n H L T hLaw herr
    exact PEqualNP.Outside.L_meta_29757.lowerGame hq hodd hE hcop hmin hqN ht htq f hf
      (PEqualNP.Outside.L_meta_29757.table base) z n H L T hLaw herr
  · exact PEqualNP.Outside.L_meta_29757.fastGame hq he hE hp hpow hqN ht htq f hf base hbase
  · intro hEq h hh
    exact ⟨h, by omega, PEqualNP.Outside.L_meta_29757.slowGame hq he hE hqN ht htq f hf base hbase hEq hh⟩
  · intro k hk hqk
    subst q
    exact PEqualNP.Outside.L_meta_29757.threePeriod hp hk hpow hmin

import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PEqualNP.Outside.L_pcx_268_aux

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

lemma zmod2_add_cancel_right (a b : ZMod 2) : a + b + b = a := by
  fin_cases a <;> fin_cases b <;> rfl

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma zmod2_nsmul_even {n : ℕ} (hn : Even n) (a : ZMod 2) : n • a = 0 := by
  rcases hn with ⟨m, rfl⟩
  rw [add_nsmul]
  exact zmod2_add_self (m • a)

lemma vec_add_self {α : Type*} (u : α → ZMod 2) : u + u = 0 := by
  ext i
  exact zmod2_add_self (u i)

lemma vec_add_cancel_right {α : Type*} (u v : α → ZMod 2) : u + v + v = u := by
  ext i
  exact zmod2_add_cancel_right (u i) (v i)

lemma list_ofFn_getD {n : ℕ} {α : Type*} (u : Fin n → α) (i : ℕ) (hi : i < n) (d : α) :
    (List.ofFn u).getD i d = u ⟨i, hi⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]

lemma le_two_pow_sub_two {ℓ : ℕ} (h : 2 ≤ ℓ) : ℓ ≤ 2 ^ ℓ - 2 := by
  induction ℓ with
  | zero => omega
  | succ m ih =>
    by_cases hm : 2 ≤ m
    · have ihm := ih hm
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
      have hge4 : 4 ≤ 2 ^ m := by
        calc
          4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
      omega
    · have hm1 : m = 1 := by omega
      subst hm1
      decide

def evalF {k : ℕ} (u : Fin k → ZMod 2) (z : Fin (k - 1) → ZMod 2) : ZMod 2 :=
  (List.ofFn u).getD (k - 1) 0 + ∑ i : Fin (k - 1), (List.ofFn u).getD i.val 0 * z i

def parityPortF {k : ℕ} (w : (Fin k → ZMod 2) × (Fin (k - 1) → ZMod 2)) (j : Fin k) : ZMod 2 :=
  if j.val = k - 1 then evalF w.1 w.2 else (List.ofFn w.2).getD j.val 0

lemma evalF_eq {k : ℕ} (hk : 0 < k) (u : Fin k → ZMod 2) (z : Fin (k - 1) → ZMod 2) :
    evalF u z = u ⟨k - 1, by omega⟩ + ∑ i : Fin (k - 1), u ⟨i.val, by omega⟩ * z i := by
  unfold evalF
  rw [list_ofFn_getD u (k - 1) (by omega) 0]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [list_ofFn_getD u i.val (by omega) 0]

lemma parityPort_in_family {k : ℕ} (hk : 0 < k) (u : Fin k → ZMod 2) :
    ∃ (A : (Fin (k - 1) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (v : Fin k → ZMod 2),
      ∀ z : Fin (k - 1) → ZMod 2, parityPortF (u, z) = A z + v := by
  let A : (Fin (k - 1) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    { toFun := fun z j =>
        if hj : j.val < k - 1 then z ⟨j.val, hj⟩
        else ∑ i : Fin (k - 1), u ⟨i.val, by omega⟩ * z i
      map_add' := fun z1 z2 => by
        ext j
        simp only [Pi.add_apply]
        split_ifs with hj
        · rfl
        · simp only [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r z => by
        ext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs with hj
        · rfl
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← mul_assoc, mul_comm (u ⟨i.val, by omega⟩) r, mul_assoc] }
  let v : Fin k → ZMod 2 := fun j => if j.val = k - 1 then u ⟨k - 1, by omega⟩ else 0
  refine ⟨A, v, fun z => ?_⟩
  ext j
  by_cases hj : j.val = k - 1
  · simp only [parityPortF, evalF_eq hk, hj, ↓reduceIte, Pi.add_apply, A, v,
      LinearMap.coe_mk, AddHom.coe_mk, lt_irrefl, ↓reduceDIte]
    exact add_comm _ _
  · have hlt : j.val < k - 1 := by omega
    simp only [parityPortF, hj, ↓reduceIte, Pi.add_apply, A, v,
      LinearMap.coe_mk, AddHom.coe_mk, hlt, ↓reduceDIte, add_zero]
    exact list_ofFn_getD z j.val hlt 0

lemma ok_parityPort_of_eval {k : ℕ} (hk : 0 < k) {α : Type*}
    (tag : ((Fin k → ZMod 2) × (Fin (k - 1) → ZMod 2)) → α)
    (huniq : ∀ a t : (Fin k → ZMod 2) × (Fin (k - 1) → ZMod 2),
      tag t = tag a → evalF a.1 t.2 = evalF t.1 t.2 → a = t) :
    ∀ a b t : (Fin k → ZMod 2) × (Fin (k - 1) → ZMod 2),
      a.1 = b.1 → parityPortF b = parityPortF t → tag t = tag a → a = b ∧ b = t := by
  intro a b t hab hsend htag
  have hbz : b.2 = t.2 := by
    ext i
    have hcon := congrFun hsend ⟨i.val, by omega⟩
    have hne : i.val ≠ k - 1 := by omega
    simp only [parityPortF, hne, ↓reduceIte] at hcon
    rw [list_ofFn_getD b.2 i.val i.isLt 0, list_ofFn_getD t.2 i.val i.isLt 0] at hcon
    exact hcon
  have heval : evalF a.1 t.2 = evalF t.1 t.2 := by
    have hcon := congrFun hsend ⟨k - 1, by omega⟩
    simp only [parityPortF, ↓reduceIte] at hcon
    rw [hbz] at hcon
    rw [hab]
    exact hcon
  have hat : a = t := huniq a t htag heval
  have hab_eq : a = b := by
    apply Prod.ext hab
    rw [hbz]
    exact congrArg Prod.snd hat
  exact ⟨hab_eq, hab_eq.symm.trans hat⟩

lemma linear_apply_eq_sum {k : ℕ} (L : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (y : Fin k → ZMod 2) :
    ∑ j : Fin k, L (Pi.single (M := fun _ => ZMod 2) j 1) * y j = L y := by
  have hy : y = ∑ j : Fin k, y j • Pi.single (M := fun _ => ZMod 2) j 1 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [Pi.single_eq_of_ne (Ne.symm hj')]
    · intro h
      exact absurd (Finset.mem_univ j) h
  conv_rhs => rw [hy]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

lemma lower_bound {k c : ℕ} (hk : 0 < k)
    (send : ((Fin k → ZMod 2) × (Fin (k - 1) → ZMod 2)) → (Fin k → ZMod 2))
    (tag : ((Fin k → ZMod 2) × (Fin (k - 1) → ZMod 2)) → Fin c → Bool)
    (hfam : ∀ u : Fin k → ZMod 2,
      ∃ (A : (Fin (k - 1) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (v : Fin k → ZMod 2),
        ∀ z : Fin (k - 1) → ZMod 2, send (u, z) = A z + v)
    (hok : ∀ a b t : (Fin k → ZMod 2) × (Fin (k - 1) → ZMod 2),
      a.1 = b.1 → send b = send t → tag t = tag a → a = b ∧ b = t) :
    2 * k - 1 ≤ c + Nat.log2 (k + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := ZMod 2
  let X := Fin k → F
  let Z := Fin (k - 1) → F
  let W := X × Z
  have hinj_all : ∀ u : X, ∃ (A : Z →ₗ[F] X) (v : X),
      Function.Injective A ∧ ∀ z : Z, send (u, z) = A z + v := by
    intro u
    rcases hfam u with ⟨A, v, hAv⟩
    refine ⟨A, v, ?_, hAv⟩
    intro z1 z2 hAeq
    have hsend : send (u, z2) = send (u, z1) := by rw [hAv z2, hAv z1, hAeq]
    have hres := hok (u, z1) (u, z2) (u, z1) rfl hsend rfl
    exact congrArg Prod.snd hres.1
  choose A v hAinj hAv using hinj_all
  have hL_exists : ∀ u : X, ∃ L : X →ₗ[F] F, LinearMap.ker L = LinearMap.range (A u) := by
    intro u
    let R := LinearMap.range (A u)
    have hrR : Module.finrank F R = k - 1 := by
      have hr := LinearMap.finrank_range_add_finrank_ker (A u)
      rw [LinearMap.ker_eq_bot.mpr (hAinj u), finrank_bot, add_zero] at hr
      simpa [R, Z, F] using hr
    have hdimQ : Module.finrank F (X ⧸ R) = 1 := by
      have hq := Submodule.finrank_quotient_add_finrank R
      have hX : Module.finrank F X = k := by simp [X, F]
      rw [hX, hrR] at hq
      omega
    let bQ := Module.finBasisOfFinrankEq F (X ⧸ R) hdimQ
    let L : X →ₗ[F] F := (LinearMap.proj (0 : Fin 1)).comp (bQ.equivFun.toLinearMap.comp R.mkQ)
    refine ⟨L, ?_⟩
    ext x
    simp only [LinearMap.mem_ker, L, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe]
    constructor
    · intro h0
      have hfun : bQ.equivFun (R.mkQ x) = 0 := by
        ext i
        fin_cases i
        exact h0
      exact (Submodule.Quotient.mk_eq_zero R).mp (bQ.equivFun.map_eq_zero_iff.mp hfun)
    · intro hx
      have hq0 : R.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero R).mpr hx
      simp [hq0]
  choose L hkerL using hL_exists
  have hfiber : ∀ h : Fin c → Bool,
      (Finset.univ.filter (fun w : W => tag w = h)).card ≤ k + 1 := by
    intro h
    let H := Finset.univ.filter (fun w : W => tag w = h)
    let vec : ↥H → (Option (Fin k) → F) := fun a x =>
      match x with
      | none => 1 + L a.1.1 (v a.1.1)
      | some j => L a.1.1 (Pi.single (M := fun _ => ZMod 2) j 1)
    let evalVec : ↥H → (Option (Fin k) → F) := fun t x =>
      match x with
      | none => 1
      | some j => send t.1 j
    have hdelta : ∀ a t : ↥H,
        ∑ x : Option (Fin k), vec a x * evalVec t x = if a = t then 1 else 0 := by
      intro a t
      rw [Fintype.sum_option]
      simp only [vec, evalVec, mul_one]
      rw [linear_apply_eq_sum (L a.1.1) (send t.1)]
      have hsum : (1 + L a.1.1 (v a.1.1)) + L a.1.1 (send t.1) =
          1 + L a.1.1 (send t.1 + v a.1.1) := by
        rw [map_add, add_assoc, add_comm (L a.1.1 (v a.1.1))]
      rw [hsum]
      by_cases hat : a = t
      · subst hat
        simp only [↓reduceIte]
        have hmem : send a.1 + v a.1.1 ∈ LinearMap.ker (L a.1.1) := by
          rw [hkerL a.1.1]
          refine ⟨a.1.2, ?_⟩
          have hsend : send a.1 = A a.1.1 a.1.2 + v a.1.1 := hAv a.1.1 a.1.2
          rw [hsend, vec_add_cancel_right]
        rw [LinearMap.mem_ker.mp hmem, add_zero]
      · simp only [hat, ↓reduceIte]
        have hne : L a.1.1 (send t.1 + v a.1.1) ≠ 0 := by
          intro hzero
          have hmem : send t.1 + v a.1.1 ∈ LinearMap.range (A a.1.1) := by
            rw [← hkerL a.1.1]
            exact hzero
          rcases hmem with ⟨z, hz⟩
          have hsend : send (a.1.1, z) = send t.1 := by
            rw [hAv a.1.1 z, hz, vec_add_cancel_right]
          have hta : tag t.1 = tag a.1 := by
            have ha := (Finset.mem_filter.mp a.2).2
            have ht := (Finset.mem_filter.mp t.2).2
            rw [ht, ha]
          have hres := hok a.1 (a.1.1, z) t.1 rfl hsend hta
          exact hat (Subtype.ext (hres.1.trans hres.2))
        rw [zmod2_eq_one_of_ne_zero hne]
        exact zmod2_add_self 1
    have hli : LinearIndependent F vec := by
      rw [Fintype.linearIndependent_iff]
      intro g hg t
      have h0 : ∑ x : Option (Fin k), (∑ a : ↥H, g a • vec a) x * evalVec t x = 0 := by
        rw [hg]
        simp
      have h1 : ∑ x : Option (Fin k), (∑ a : ↥H, g a • vec a) x * evalVec t x =
          ∑ a : ↥H, g a * ∑ x : Option (Fin k), vec a x * evalVec t x := by
        simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => mul_assoc _ _ _
      rw [h1] at h0
      simp_rw [hdelta] at h0
      rw [Finset.sum_eq_single t] at h0
      · simpa using h0
      · intro a _ hat
        simp [hat]
      · intro hmem
        exact absurd (Finset.mem_univ t) hmem
    have hcard_le : Fintype.card ↥H ≤ Module.finrank F (Option (Fin k) → F) :=
      hli.fintype_card_le_finrank
    have hdim : Module.finrank F (Option (Fin k) → F) = k + 1 := by simp [F]
    have hHcard : Fintype.card ↥H = H.card := Fintype.card_coe H
    rw [hHcard, hdim] at hcard_le
    exact hcard_le
  have hcardW : Fintype.card W = 2 ^ (2 * k - 1) := by
    have h1 : Fintype.card W = 2 ^ k * 2 ^ (k - 1) := by
      simp [W, X, Z, F]
    rw [h1, ← pow_add]
    congr 1
    omega
  have hsum_part : Fintype.card W =
      ∑ h : Fin c → Bool, (Finset.univ.filter (fun w : W => tag w = h)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun w _ => Finset.mem_univ (tag w)
  have hle : Fintype.card W ≤ 2 ^ c * (k + 1) := by
    rw [hsum_part]
    calc
      ∑ h : Fin c → Bool, (Finset.univ.filter (fun w : W => tag w = h)).card ≤
          ∑ _h : Fin c → Bool, (k + 1) := Finset.sum_le_sum fun h _ => hfiber h
      _ = 2 ^ c * (k + 1) := by simp
  rw [hcardW] at hle
  have hlt_log : k + 1 < 2 ^ (Nat.log2 (k + 1) + 1) := Nat.lt_log2_self
  have hlt : 2 ^ (2 * k - 1) < 2 ^ (c + (Nat.log2 (k + 1) + 1)) := by
    calc
      2 ^ (2 * k - 1) ≤ 2 ^ c * (k + 1) := hle
      _ < 2 ^ c * 2 ^ (Nat.log2 (k + 1) + 1) :=
        Nat.mul_lt_mul_of_pos_left hlt_log (pow_pos (by omega : 0 < 2) c)
      _ = 2 ^ (c + (Nat.log2 (k + 1) + 1)) := (pow_add 2 c _).symm
  have hlt_exp : 2 * k - 1 < c + (Nat.log2 (k + 1) + 1) :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlt
  omega

def allOnes (ℓ : ℕ) : Fin ℓ → ZMod 2 := fun _ => 1

lemma allOnes_ne_zero {ℓ : ℕ} (hℓ : 2 ≤ ℓ) : allOnes ℓ ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, by omega⟩
  exact (by decide : (1 : ZMod 2) ≠ 0) h0

lemma sum_all_vecs_eq_zero {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∑ x : Fin ℓ → ZMod 2, x = 0 := by
  ext j
  rw [Finset.sum_apply, Pi.zero_apply]
  let j' : Fin ℓ := if j.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hjj' : j' ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    by_cases hj0 : j.val = 0
    · simp only [j', hj0, ↓reduceIte] at hv
      omega
    · simp only [j', hj0, ↓reduceIte] at hv
      exact hj0 hv.symm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Fin ℓ → ZMod 2 => x j' = 0)]
  have heq : ∑ x ∈ Finset.univ.filter (fun x : Fin ℓ → ZMod 2 => x j' = 0), x j =
      ∑ x ∈ Finset.univ.filter (fun x : Fin ℓ → ZMod 2 => ¬ x j' = 0), x j := by
    refine Finset.sum_bij (fun x _ => x + Pi.single (M := fun _ => ZMod 2) j' 1) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      simp only [Pi.add_apply, Pi.single_eq_same, hx, zero_add]
      decide
    · intro x1 _ x2 _ h
      exact add_right_cancel h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨y + Pi.single (M := fun _ => ZMod 2) j' 1, ?_, vec_add_cancel_right y _⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Pi.single_eq_same]
      rw [zmod2_eq_one_of_ne_zero hy]
      exact zmod2_add_self 1
    · intro x _
      simp only [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hjj'), add_zero]
  rw [heq]
  exact zmod2_add_self _

lemma card_mid_eq {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    Fintype.card {x : Fin ℓ → ZMod 2 // x ≠ 0 ∧ x ≠ allOnes ℓ} = 2 ^ ℓ - 2 := by
  rw [Fintype.card_subtype]
  have hfilt : Finset.univ.filter (fun x : Fin ℓ → ZMod 2 => x ≠ 0 ∧ x ≠ allOnes ℓ) =
      (Finset.univ.erase (0 : Fin ℓ → ZMod 2)).erase (allOnes ℓ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_comm]
  rw [hfilt]
  have hmem : allOnes ℓ ∈ Finset.univ.erase (0 : Fin ℓ → ZMod 2) :=
    Finset.mem_erase.mpr ⟨allOnes_ne_zero hℓ, Finset.mem_univ _⟩
  rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  omega

lemma card_nonzero_eq (ℓ : ℕ) :
    Fintype.card {x : Fin ℓ → ZMod 2 // x ≠ 0} = 2 ^ ℓ - 1 := by
  rw [Fintype.card_subtype]
  have hfilt : Finset.univ.filter (fun x : Fin ℓ → ZMod 2 => x ≠ 0) =
      Finset.univ.erase (0 : Fin ℓ → ZMod 2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]

lemma sum_split_fin {n d : ℕ} (hd : d ≤ n) (f : Fin n → ZMod 2) :
    ∑ i : Fin n, f i =
      (∑ i : Fin d, f ⟨i.val, by omega⟩) +
      ∑ j : Fin (n - d), f ⟨d + j.val, by omega⟩ := by
  let e : Fin d ⊕ Fin (n - d) ≃ Fin n :=
    { toFun := fun s =>
        match s with
        | Sum.inl i => ⟨i.val, by omega⟩
        | Sum.inr j => ⟨d + j.val, by omega⟩
      invFun := fun i =>
        if h : i.val < d then Sum.inl ⟨i.val, h⟩
        else Sum.inr ⟨i.val - d, by omega⟩
      left_inv := fun s => by
        cases s with
        | inl i => simp [i.isLt]
        | inr j =>
          have hnot : ¬ (d + j.val < d) := by omega
          simp only [hnot, ↓reduceDIte]
          congr 1
          apply Fin.ext
          dsimp only
          omega
      right_inv := fun i => by
        dsimp only
        split_ifs with h
        · rfl
        · apply Fin.ext
          dsimp only
          omega }
  rw [← Fintype.sum_equiv e (fun s => f (e s)) f (fun _ => rfl), Fintype.sum_sum_type]
  rfl

def tagWordF {ℓ d : ℕ} (syn : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin ℓ → ZMod 2))
    (shape : (Fin ℓ → ZMod 2) → (Fin d → ZMod 2))
    (s : Fin d → ZMod 2) (b : ZMod 2) (z : Fin d → ZMod 2) (x : Fin ℓ → ZMod 2) : ZMod 2 :=
  (b + ∑ i : Fin d, s i * ((z + shape (syn z)) i + shape x i)) +
    if x = syn z then 0 else 1

lemma inner_unique_of_syndrome {ℓ d : ℕ}
    (syn : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin ℓ → ZMod 2))
    (shape : (Fin ℓ → ZMod 2) → (Fin d → ZMod 2))
    (col : Fin d → (Fin ℓ → ZMod 2))
    (hshape_zero : shape 0 = 0)
    (hshape_col : ∀ i : Fin d, shape (col i) = Pi.single (M := fun _ => ZMod 2) i 1)
    (hsum_tagWord : ∀ s b z, ∑ x : Fin ℓ → ZMod 2, tagWordF syn shape s b z x = 1)
    (s1 s2 : Fin d → ZMod 2) (b1 b2 : ZMod 2) (z1 z2 : Fin d → ZMod 2)
    (ht0_eq : z1 + shape (syn z1) = z2 + shape (syn z2))
    (htw_nz : ∀ x : Fin ℓ → ZMod 2, x ≠ 0 →
      tagWordF syn shape s1 b1 z1 x = tagWordF syn shape s2 b2 z2 x)
    (heval : b1 + ∑ i : Fin d, s1 i * z2 i = b2 + ∑ i : Fin d, s2 i * z2 i) :
    s1 = s2 ∧ b1 = b2 ∧ z1 = z2 := by
  have htw_eq : tagWordF syn shape s1 b1 z1 = tagWordF syn shape s2 b2 z2 := by
    ext x
    by_cases hx : x = 0
    · subst hx
      have hs1 := hsum_tagWord s1 b1 z1
      have hs2 := hsum_tagWord s2 b2 z2
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin ℓ → ZMod 2))] at hs1 hs2
      have hsum_eq : ∑ y ∈ Finset.univ.erase (0 : Fin ℓ → ZMod 2),
          tagWordF syn shape s1 b1 z1 y =
          ∑ y ∈ Finset.univ.erase (0 : Fin ℓ → ZMod 2),
          tagWordF syn shape s2 b2 z2 y :=
        Finset.sum_congr rfl fun y hy => htw_nz y (Finset.mem_erase.mp hy).1
      rw [hsum_eq] at hs1
      exact add_right_cancel (hs1.trans hs2.symm)
    · exact htw_nz x hx
  have hz2_eq : ∀ i : Fin d, (z1 + shape (syn z1)) i + shape (syn z2) i = z2 i := by
    intro i
    rw [ht0_eq]
    exact congrFun (vec_add_cancel_right z2 (shape (syn z2))) i
  have hq_eq : syn z2 = syn z1 := by
    have hcon := congrFun htw_eq (syn z2)
    simp only [tagWordF, ↓reduceIte, add_zero] at hcon
    have hlhs : ∑ i : Fin d, s1 i * ((z1 + shape (syn z1)) i + shape (syn z2) i) =
        ∑ i : Fin d, s1 i * z2 i :=
      Finset.sum_congr rfl fun i _ => by rw [hz2_eq i]
    have hrhs : ∑ i : Fin d, s2 i * ((z2 + shape (syn z2)) i + shape (syn z2) i) =
        ∑ i : Fin d, s2 i * z2 i :=
      Finset.sum_congr rfl fun i _ => by rw [← ht0_eq, hz2_eq i]
    rw [hlhs, hrhs, heval] at hcon
    have hind0 : (if syn z2 = syn z1 then (0 : ZMod 2) else 1) = 0 := by
      exact add_left_cancel (hcon.trans (add_zero _).symm)
    by_contra hne
    simp only [hne, ↓reduceIte] at hind0
    exact (by decide : (1 : ZMod 2) ≠ 0) hind0
  have hz_eq : z1 = z2 := by
    calc
      z1 = (z1 + shape (syn z1)) + shape (syn z1) := (vec_add_cancel_right z1 _).symm
      _ = (z2 + shape (syn z2)) + shape (syn z2) := by rw [ht0_eq, hq_eq]
      _ = z2 := vec_add_cancel_right z2 _
  have hval_all : ∀ x : Fin ℓ → ZMod 2,
      b1 + ∑ i : Fin d, s1 i * ((z1 + shape (syn z1)) i + shape x i) =
        b2 + ∑ i : Fin d, s2 i * ((z1 + shape (syn z1)) i + shape x i) := by
    intro x
    have hcon := congrFun htw_eq x
    simp only [tagWordF] at hcon
    rw [← ht0_eq] at hcon
    rw [hq_eq] at hcon
    exact add_right_cancel hcon
  have hval0 : b1 + ∑ i : Fin d, s1 i * (z1 + shape (syn z1)) i =
      b2 + ∑ i : Fin d, s2 i * (z1 + shape (syn z1)) i := by
    have h0 := hval_all 0
    simpa [hshape_zero] using h0
  have hstep : ∀ (s : Fin d → ZMod 2) (b : ZMod 2) (j : Fin d),
      b + ∑ i : Fin d, s i * ((z1 + shape (syn z1)) i + shape (col j) i) =
        (b + ∑ i : Fin d, s i * (z1 + shape (syn z1)) i) + s j := by
    intro s b j
    simp_rw [mul_add, Finset.sum_add_distrib, ← add_assoc]
    congr 1
    rw [hshape_col j, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Pi.single_eq_of_ne hij]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hs_eq : s1 = s2 := by
    ext j
    have hj := hval_all (col j)
    rw [hstep s1 b1 j, hstep s2 b2 j, hval0] at hj
    exact add_left_cancel hj
  have hb_eq : b1 = b2 := by
    rw [hs_eq] at hval0
    exact add_right_cancel hval0
  exact ⟨hs_eq, hb_eq, hz_eq⟩

lemma inner_tiling_exists {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    let d := 2 ^ ℓ - 2
    ∃ (T : Type) (_ : Fintype T)
      (innerTag : (Fin d → ZMod 2) → ZMod 2 → (Fin d → ZMod 2) → T),
      Fintype.card T = 2 ^ (2 * d + 1 - ℓ) ∧
      ∀ (s1 s2 : Fin d → ZMod 2) (b1 b2 : ZMod 2) (z1 z2 : Fin d → ZMod 2),
        innerTag s1 b1 z1 = innerTag s2 b2 z2 →
        b1 + ∑ i : Fin d, s1 i * z2 i = b2 + ∑ i : Fin d, s2 i * z2 i →
        s1 = s2 ∧ b1 = b2 ∧ z1 = z2 := by
  intro d
  classical
  have hℓd : ℓ ≤ d := le_two_pow_sub_two hℓ
  have h2pow : 4 ≤ 2 ^ ℓ := by
    calc
      4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by omega) hℓ
  have heven_pow : Even (2 ^ ℓ) := by
    refine ⟨2 ^ (ℓ - 1), ?_⟩
    have h1 : ℓ = (ℓ - 1) + 1 := by omega
    conv_lhs => rw [h1, pow_succ, mul_two]
  let Mid := {x : Fin ℓ → ZMod 2 // x ≠ 0 ∧ x ≠ allOnes ℓ}
  let eMid : Fin d ≃ Mid := (Fintype.equivFinOfCardEq (card_mid_eq hℓ)).symm
  let col : Fin d → (Fin ℓ → ZMod 2) := fun i => (eMid i).1
  let syn : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin ℓ → ZMod 2) :=
    { toFun := fun v => ∑ i : Fin d, v i • col i
      map_add' := fun v1 v2 => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r v => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hsyn_single : ∀ i : Fin d, syn (Pi.single (M := fun _ => ZMod 2) i 1) = col i := by
    intro i
    change ∑ j : Fin d, (Pi.single (M := fun _ => ZMod 2) i 1 j) • col j = col i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hmem_erase : ∀ x : Fin ℓ → ZMod 2,
      x ∈ (Finset.univ.erase (0 : Fin ℓ → ZMod 2)).erase (allOnes ℓ) ↔
        x ≠ 0 ∧ x ≠ allOnes ℓ := by
    intro x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact and_comm
  have hsum_col : ∑ i : Fin d, col i = allOnes ℓ := by
    have hbij : ∑ i : Fin d, col i =
        ∑ x ∈ (Finset.univ.erase (0 : Fin ℓ → ZMod 2)).erase (allOnes ℓ), x := by
      have h1 : ∑ i : Fin d, col i = ∑ m : Mid, m.1 :=
        Fintype.sum_equiv eMid col (fun m => m.1) (fun _ => rfl)
      rw [h1]
      exact (Finset.sum_subtype ((Finset.univ.erase (0 : Fin ℓ → ZMod 2)).erase (allOnes ℓ))
        hmem_erase (fun x => x)).symm
    have hmem : allOnes ℓ ∈ Finset.univ.erase (0 : Fin ℓ → ZMod 2) :=
      Finset.mem_erase.mpr ⟨allOnes_ne_zero hℓ, Finset.mem_univ _⟩
    have htot := sum_all_vecs_eq_zero hℓ
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin ℓ → ZMod 2)), zero_add,
      ← Finset.add_sum_erase _ _ hmem] at htot
    rw [hbij]
    calc
      ∑ x ∈ (Finset.univ.erase (0 : Fin ℓ → ZMod 2)).erase (allOnes ℓ), x
          = allOnes ℓ + (allOnes ℓ +
              ∑ x ∈ (Finset.univ.erase (0 : Fin ℓ → ZMod 2)).erase (allOnes ℓ), x) := by
            rw [← add_assoc, vec_add_self, zero_add]
      _ = allOnes ℓ + 0 := by rw [htot]
      _ = allOnes ℓ := add_zero _
  have hsyn_allOnes : syn (fun _ => 1) = allOnes ℓ := by
    change ∑ i : Fin d, (1 : ZMod 2) • col i = allOnes ℓ
    simp only [one_smul]
    exact hsum_col
  let shape : (Fin ℓ → ZMod 2) → (Fin d → ZMod 2) := fun x =>
    if h0 : x = 0 then 0
    else if h1 : x = allOnes ℓ then (fun _ => 1)
    else Pi.single (M := fun _ => ZMod 2) (eMid.symm ⟨x, h0, h1⟩) 1
  have hshape_zero : shape 0 = 0 := by simp [shape]
  have hshape_allOnes : shape (allOnes ℓ) = fun _ => 1 := by
    simp [shape, allOnes_ne_zero hℓ]
  have hshape_col : ∀ i : Fin d, shape (col i) = Pi.single (M := fun _ => ZMod 2) i 1 := by
    intro i
    have hne0 : col i ≠ 0 := (eMid i).2.1
    have hne1 : col i ≠ allOnes ℓ := (eMid i).2.2
    simp only [shape, hne0, ↓reduceDIte, hne1]
    have hsub : (⟨col i, hne0, hne1⟩ : Mid) = eMid i := Subtype.ext rfl
    rw [hsub, Equiv.symm_apply_apply]
  have hsyn_shape : ∀ x : Fin ℓ → ZMod 2, syn (shape x) = x := by
    intro x
    by_cases h0 : x = 0
    · subst h0
      rw [hshape_zero, map_zero]
    · by_cases h1 : x = allOnes ℓ
      · subst h1
        rw [hshape_allOnes, hsyn_allOnes]
      · simp only [shape, h0, ↓reduceDIte, h1]
        rw [hsyn_single]
        exact congrArg Subtype.val (Equiv.apply_symm_apply eMid ⟨x, h0, h1⟩)
  let tileEquiv : (↥(LinearMap.ker syn) × (Fin ℓ → ZMod 2)) ≃ (Fin d → ZMod 2) :=
    { toFun := fun p => p.1.1 + shape p.2
      invFun := fun z =>
        (⟨z + shape (syn z), by
          rw [LinearMap.mem_ker, map_add, hsyn_shape, vec_add_self]⟩, syn z)
      left_inv := fun p => by
        rcases p with ⟨⟨t0, ht0⟩, x⟩
        have hsyn_eq : syn (t0 + shape x) = x := by
          rw [map_add, LinearMap.mem_ker.mp ht0, zero_add, hsyn_shape]
        apply Prod.ext
        · apply Subtype.ext
          dsimp only
          rw [hsyn_eq]
          exact vec_add_cancel_right t0 (shape x)
        · exact hsyn_eq
      right_inv := fun z => vec_add_cancel_right z (shape (syn z)) }
  have hcardKer : Fintype.card ↥(LinearMap.ker syn) = 2 ^ (d - ℓ) := by
    have hcard := Fintype.card_congr tileEquiv
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card] at hcard
    have hpow : 2 ^ d = 2 ^ (d - ℓ) * 2 ^ ℓ := by
      rw [← pow_add, Nat.sub_add_cancel hℓd]
    rw [hpow] at hcard
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by omega : 0 < 2) ℓ) hcard
  have hsum_affine : ∀ (s : Fin d → ZMod 2) (b : ZMod 2) (t0 : Fin d → ZMod 2),
      ∑ x : Fin ℓ → ZMod 2, (b + ∑ i : Fin d, s i * (t0 i + shape x i)) = 0 := by
    intro s b t0
    have hrewrite : ∀ x : Fin ℓ → ZMod 2,
        b + ∑ i : Fin d, s i * (t0 i + shape x i) =
          (b + ∑ i : Fin d, s i * t0 i) + ∑ i : Fin d, s i * shape x i := by
      intro x
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [add_assoc]
    simp_rw [hrewrite]
    rw [Finset.sum_add_distrib]
    have hconst : ∑ _x : Fin ℓ → ZMod 2, (b + ∑ i : Fin d, s i * t0 i) = 0 := by
      rw [Finset.sum_const, Finset.card_univ]
      have hcard : Fintype.card (Fin ℓ → ZMod 2) = 2 ^ ℓ := by simp
      rw [hcard]
      exact zmod2_nsmul_even heven_pow _
    rw [hconst, zero_add]
    have hmem : allOnes ℓ ∈ Finset.univ.erase (0 : Fin ℓ → ZMod 2) :=
      Finset.mem_erase.mpr ⟨allOnes_ne_zero hℓ, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin ℓ → ZMod 2)),
      ← Finset.add_sum_erase _ _ hmem]
    have hterm0 : ∑ i : Fin d, s i * shape 0 i = 0 := by
      simp [hshape_zero]
    have hterm1 : ∑ i : Fin d, s i * shape (allOnes ℓ) i = ∑ i : Fin d, s i := by
      simp [hshape_allOnes]
    have hrest : ∑ x ∈ (Finset.univ.erase (0 : Fin ℓ → ZMod 2)).erase (allOnes ℓ),
        ∑ i : Fin d, s i * shape x i = ∑ i : Fin d, s i := by
      have hsub : ∑ x ∈ (Finset.univ.erase (0 : Fin ℓ → ZMod 2)).erase (allOnes ℓ),
          ∑ i : Fin d, s i * shape x i =
          ∑ m : Mid, ∑ i : Fin d, s i * shape m.1 i :=
        Finset.sum_subtype ((Finset.univ.erase (0 : Fin ℓ → ZMod 2)).erase (allOnes ℓ))
          hmem_erase (fun x => ∑ i : Fin d, s i * shape x i)
      rw [hsub]
      rw [← Fintype.sum_equiv eMid (fun i => ∑ j : Fin d, s j * shape (col i) j)
        (fun m : Mid => ∑ j : Fin d, s j * shape m.1 j) (fun _ => rfl)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hshape_col i]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hterm0, hterm1, hrest, zero_add]
    exact zmod2_add_self _
  have hsum_tagWord : ∀ s b z, ∑ x : Fin ℓ → ZMod 2, tagWordF syn shape s b z x = 1 := by
    intro s b z
    simp only [tagWordF]
    rw [Finset.sum_add_distrib, hsum_affine, zero_add]
    have hind : ∀ x : Fin ℓ → ZMod 2,
        (if x = syn z then (0 : ZMod 2) else 1) = 1 + if x = syn z then 1 else 0 := by
      intro x
      split_ifs
      · exact (zmod2_add_self 1).symm
      · exact (add_zero 1).symm
    simp_rw [hind]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ _x : Fin ℓ → ZMod 2, (1 : ZMod 2) = 0 := by
      rw [Finset.sum_const, Finset.card_univ]
      have hcard : Fintype.card (Fin ℓ → ZMod 2) = 2 ^ ℓ := by simp
      rw [hcard]
      exact zmod2_nsmul_even heven_pow 1
    rw [h1, zero_add]
    simp
  let T := ↥(LinearMap.ker syn) × ({x : Fin ℓ → ZMod 2 // x ≠ 0} → ZMod 2)
  let innerTag : (Fin d → ZMod 2) → ZMod 2 → (Fin d → ZMod 2) → T := fun s b z =>
    (⟨z + shape (syn z), by
      rw [LinearMap.mem_ker, map_add, hsyn_shape, vec_add_self]⟩,
     fun x => tagWordF syn shape s b z x.1)
  refine ⟨T, inferInstance, innerTag, ?_, ?_⟩
  · have hcardT : Fintype.card T = 2 ^ (d - ℓ) * 2 ^ (2 ^ ℓ - 1) := by
      simp only [T, Fintype.card_prod, hcardKer, Fintype.card_fun, card_nonzero_eq, ZMod.card]
    rw [hcardT, ← pow_add]
    congr 1
    omega
  · intro s1 s2 b1 b2 z1 z2 htag heval
    have ht0_eq : z1 + shape (syn z1) = z2 + shape (syn z2) :=
      congrArg Subtype.val (congrArg Prod.fst htag)
    have htw_nz : ∀ x : Fin ℓ → ZMod 2, x ≠ 0 →
        tagWordF syn shape s1 b1 z1 x = tagWordF syn shape s2 b2 z2 x := fun x hx =>
      congrFun (congrArg Prod.snd htag) ⟨x, hx⟩
    exact inner_unique_of_syndrome syn shape col hshape_zero hshape_col hsum_tagWord
      s1 s2 b1 b2 z1 z2 ht0_eq htw_nz heval

lemma upper_bound {k c : ℕ} (hk : 0 < k) (hc : 2 * k - 1 ≤ c + Nat.log2 (k + 1)) :
    ∃ tag : ((Fin k → ZMod 2) × (Fin (k - 1) → ZMod 2)) → Fin c → Bool,
      ∀ a b t : (Fin k → ZMod 2) × (Fin (k - 1) → ZMod 2),
        a.1 = b.1 → parityPortF b = parityPortF t → tag t = tag a → a = b ∧ b = t := by
  let ℓ := Nat.log2 (k + 1)
  have hℓ_pos : 1 ≤ ℓ := (Nat.le_log2 (by omega)).mpr (by omega)
  by_cases hℓ : ℓ < 2
  · have hℓ1 : ℓ = 1 := by omega
    have hc' : 2 * (k - 1) ≤ c := by omega
    let T := (Fin (k - 1) → ZMod 2) × (Fin (k - 1) → ZMod 2)
    have hcard : Fintype.card T ≤ Fintype.card (Fin c → Bool) := by
      simp only [T, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card,
        Fintype.card_bool]
      rw [← pow_add]
      have hexp : (k - 1) + (k - 1) ≤ c := by omega
      exact Nat.pow_le_pow_right (by omega) hexp
    rcases Function.Embedding.nonempty_of_card_le hcard with ⟨e⟩
    let tag0 : ((Fin k → ZMod 2) × (Fin (k - 1) → ZMod 2)) → T := fun w =>
      (fun i : Fin (k - 1) => w.1 ⟨i.val, by omega⟩, w.2)
    refine ⟨fun w => e (tag0 w), ok_parityPort_of_eval hk (fun w => e (tag0 w)) ?_⟩
    intro a t htag heval
    have htag0 : tag0 t = tag0 a := e.injective htag
    have hs : ∀ i : Fin (k - 1), t.1 ⟨i.val, by omega⟩ = a.1 ⟨i.val, by omega⟩ := fun i =>
      congrFun (congrArg (Prod.fst : T → _) htag0) i
    have hz : t.2 = a.2 := congrArg (Prod.snd : T → _) htag0
    rw [evalF_eq hk, evalF_eq hk] at heval
    have hsum : ∑ i : Fin (k - 1), a.1 ⟨i.val, by omega⟩ * t.2 i =
        ∑ i : Fin (k - 1), t.1 ⟨i.val, by omega⟩ * t.2 i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hs i]
    rw [hsum] at heval
    have hb : a.1 ⟨k - 1, by omega⟩ = t.1 ⟨k - 1, by omega⟩ := add_right_cancel heval
    have hu : a.1 = t.1 := by
      ext j
      by_cases hj : j.val = k - 1
      · have hjeq : j = ⟨k - 1, by omega⟩ := Fin.ext hj
        rw [hjeq, hb]
      · have hlt : j.val < k - 1 := by omega
        exact (hs ⟨j.val, hlt⟩).symm
    exact Prod.ext hu hz.symm
  · have hℓ2 : 2 ≤ ℓ := by omega
    have hpow_le : 2 ^ ℓ ≤ k + 1 := Nat.log2_self_le (by omega)
    let d := 2 ^ ℓ - 2
    have hd : d ≤ k - 1 := by omega
    have hℓd : ℓ ≤ d := le_two_pow_sub_two hℓ2
    let r := k - 1 - d
    rcases inner_tiling_exists hℓ2 with ⟨T0, instT0, innerTag, hcardT0, hinner⟩
    let _ : Fintype T0 := instT0
    let TagSpace := (Fin r → ZMod 2) × (Fin r → ZMod 2) × T0
    have hcard : Fintype.card TagSpace ≤ Fintype.card (Fin c → Bool) := by
      simp only [TagSpace, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card,
        Fintype.card_bool, hcardT0]
      rw [← pow_add, ← pow_add]
      have hexp : r + (r + (2 * d + 1 - ℓ)) ≤ c := by omega
      exact Nat.pow_le_pow_right (by omega) hexp
    rcases Function.Embedding.nonempty_of_card_le hcard with ⟨e⟩
    let s1Of : (Fin k → ZMod 2) → (Fin d → ZMod 2) := fun u i => u ⟨i.val, by omega⟩
    let s2Of : (Fin k → ZMod 2) → (Fin r → ZMod 2) := fun u j => u ⟨d + j.val, by omega⟩
    let bOf : (Fin k → ZMod 2) → ZMod 2 := fun u => u ⟨k - 1, by omega⟩
    let z1Of : (Fin (k - 1) → ZMod 2) → (Fin d → ZMod 2) := fun z i => z ⟨i.val, by omega⟩
    let z2Of : (Fin (k - 1) → ZMod 2) → (Fin r → ZMod 2) := fun z j => z ⟨d + j.val, by omega⟩
    let tag0 : ((Fin k → ZMod 2) × (Fin (k - 1) → ZMod 2)) → TagSpace := fun w =>
      (s2Of w.1, z2Of w.2, innerTag (s1Of w.1) (bOf w.1) (z1Of w.2))
    refine ⟨fun w => e (tag0 w), ok_parityPort_of_eval hk (fun w => e (tag0 w)) ?_⟩
    intro a t htag heval
    have htag0 : tag0 t = tag0 a := e.injective htag
    have hs2 : s2Of t.1 = s2Of a.1 := congrArg (Prod.fst : TagSpace → _) htag0
    have hz2 : z2Of t.2 = z2Of a.2 := congrArg (fun p : TagSpace => p.2.1) htag0
    have hti : innerTag (s1Of a.1) (bOf a.1) (z1Of a.2) =
        innerTag (s1Of t.1) (bOf t.1) (z1Of t.2) :=
      (congrArg (fun p : TagSpace => p.2.2) htag0).symm
    have heval_split : ∀ u z, evalF u z =
        (bOf u + ∑ i : Fin d, s1Of u i * z1Of z i) + ∑ j : Fin r, s2Of u j * z2Of z j := by
      intro u z
      rw [evalF_eq hk, sum_split_fin hd (fun i => u ⟨i.val, by omega⟩ * z i), add_assoc]
    rw [heval_split a.1 t.2, heval_split t.1 t.2, hs2] at heval
    have heval1 : bOf a.1 + ∑ i : Fin d, s1Of a.1 i * z1Of t.2 i =
        bOf t.1 + ∑ i : Fin d, s1Of t.1 i * z1Of t.2 i := add_right_cancel heval
    rcases hinner (s1Of a.1) (s1Of t.1) (bOf a.1) (bOf t.1) (z1Of a.2) (z1Of t.2) hti heval1 with
      ⟨hs1, hb, hz1⟩
    have hu : a.1 = t.1 := by
      ext m
      by_cases hm1 : m.val < d
      · exact congrFun hs1 ⟨m.val, hm1⟩
      · by_cases hm2 : m.val = k - 1
        · have hmeq : m = ⟨k - 1, by omega⟩ := Fin.ext hm2
          rw [hmeq]
          exact hb
        · have hlt : m.val - d < r := by omega
          have hcon := (congrFun hs2 ⟨m.val - d, hlt⟩).symm
          have hmeq : (⟨d + (m.val - d), by omega⟩ : Fin k) = m := by
            apply Fin.ext
            dsimp only
            omega
          simpa [s2Of, hmeq] using hcon
    have hz : a.2 = t.2 := by
      ext m
      by_cases hm1 : m.val < d
      · exact congrFun hz1 ⟨m.val, hm1⟩
      · have hlt : m.val - d < r := by omega
        have hcon := (congrFun hz2 ⟨m.val - d, hlt⟩).symm
        have hmeq : (⟨d + (m.val - d), by omega⟩ : Fin (k - 1)) = m := by
          apply Fin.ext
          dsimp only
          omega
        simpa [z2Of, hmeq] using hcon
    exact Prod.ext hu hz

end PEqualNP.Outside.L_pcx_268_aux

theorem PEqualNP.Outside.L_pcx_268 : ∀ k c : ℕ, 0 < k →
  let F := ZMod 2
  let X := Fin k → F
  let Z := Fin (k-1) → F
  let W := X × Z
  let ok := fun (send : W → X) (tag : W → Fin c → Bool) =>
    ∀ a b t : W, a.1 = b.1 → send b = send t → tag t = tag a → a = b ∧ b = t
  let family := fun send : W → X => ∀ u : X, ∃ (A : Z →ₗ[F] X) (v : X),
    ∀ z : Z, send (u,z) = A z + v
  let eval := fun (u : X) (z : Z) =>
    (List.ofFn u).getD (k-1) 0 + ∑ i : Fin (k-1), (List.ofFn u).getD i.val 0 * z i
  let parityPort := fun (w : W) (j : Fin k) =>
    if j.val = k-1 then eval w.1 w.2 else (List.ofFn w.2).getD j.val 0
  ((∃ (send : W → X) (tag : W → Fin c → Bool), family send ∧ ok send tag) ↔
    2*k-1 ≤ c + Nat.log2 (k+1)) ∧
  (2*k-1 ≤ c + Nat.log2 (k+1) → ∃ tag : W → Fin c → Bool, ok parityPort tag) := by
  intro k c hk F X Z W ok family eval parityPort
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨send, tag, hfam, hok⟩
    exact PEqualNP.Outside.L_pcx_268_aux.lower_bound hk send tag hfam hok
  · intro hc
    rcases PEqualNP.Outside.L_pcx_268_aux.upper_bound hk hc with ⟨tag, hok⟩
    exact ⟨parityPort, tag, PEqualNP.Outside.L_pcx_268_aux.parityPort_in_family hk, hok⟩
  · intro hc
    exact PEqualNP.Outside.L_pcx_268_aux.upper_bound hk hc

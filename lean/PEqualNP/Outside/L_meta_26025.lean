import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26025
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

def tau (r c i : ℕ) : ℕ := if r ≤ i ∧ i < 2 * r then r + (i - r + c) % r else i

def bp (k r c x : ℕ) : ℕ := Nat.ofBits (fun i : Fin k => x.testBit (tau r c i.val))

lemma cancel {r n c c' : ℕ} (hn : n < r) (hc : c + c' = r) : ((n + c) % r + c') % r = n := by
  rw [Nat.mod_add_mod, add_assoc, hc, Nat.add_mod_right, Nat.mod_eq_of_lt hn]

lemma tau_lt {k r c i : ℕ} (hk : 2 * r ≤ k) (hi : i < k) : tau r c i < k := by
  unfold tau
  split_ifs with h
  · have := Nat.mod_lt (i - r + c) (show 0 < r by omega)
    omega
  · exact hi

lemma tau_tau {r c c' i : ℕ} (hc : c + c' = r) : tau r c' (tau r c i) = i := by
  unfold tau
  by_cases h : r ≤ i ∧ i < 2 * r
  · have hr : 0 < r := by omega
    have hm := Nat.mod_lt (i - r + c) hr
    rw [if_pos h, if_pos (by omega), Nat.add_sub_cancel_left, cancel (by omega) hc]
    omega
  · rw [if_neg h, if_neg h]

lemma tau_low {r c i : ℕ} (hi : i < r) : tau r c i = i := by
  unfold tau
  rw [if_neg (by omega)]

lemma tau_eq {r s j i : ℕ} (hj : j < r) (hs : s ≤ r) :
    (r + (j + s) % r = tau r s i) ↔ r + j = i := by
  have hr : 0 < r := by omega
  have c2 := cancel (r := r) (c := s) (c' := r - s) hj (by omega)
  unfold tau
  by_cases h : r ≤ i ∧ i < 2 * r
  · rw [if_pos h]
    have c1 := cancel (r := r) (n := i - r) (c := s) (c' := r - s) (by omega) (by omega)
    constructor
    · intro he
      have he' : (j + s) % r = (i - r + s) % r := by omega
      rw [← he', c2] at c1
      omega
    · intro he
      subst he
      rw [Nat.add_sub_cancel_left]
  · rw [if_neg h]
    have hm := Nat.mod_lt (j + s) hr
    constructor
    · intro he
      omega
    · intro he
      omega

lemma bp_lt (k r c x : ℕ) : bp k r c x < 2 ^ k := Nat.ofBits_lt_two_pow _

lemma bp_testBit {k r c x i : ℕ} (hi : i < k) :
    (bp k r c x).testBit i = x.testBit (tau r c i) := by
  unfold bp
  rw [Nat.testBit_ofBits_lt _ _ hi]

lemma tb_ge {k x i : ℕ} (hx : x < 2 ^ k) (hi : ¬ i < k) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right two_pos (not_lt.mp hi)))

lemma bp_bp {k r c c' x : ℕ} (hk : 2 * r ≤ k) (hc : c + c' = r) (hx : x < 2 ^ k) :
    bp k r c' (bp k r c x) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · rw [bp_testBit hi, bp_testBit (tau_lt hk hi), tau_tau (by omega)]
  · rw [tb_ge (bp_lt _ _ _ _) hi, tb_ge hx hi]

lemma bp_xor (k r c x y : ℕ) : bp k r c (x ^^^ y) = bp k r c x ^^^ bp k r c y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · rw [bp_testBit hi, Nat.testBit_xor, Nat.testBit_xor, bp_testBit hi, bp_testBit hi]
  · rw [tb_ge (bp_lt _ _ _ _) hi, tb_ge (Nat.xor_lt_two_pow (bp_lt _ _ _ _) (bp_lt _ _ _ _)) hi]

lemma bp_pow {k r s j : ℕ} (hk : 2 * r ≤ k) (hj : j < r) (hs : s ≤ r) :
    bp k r s (2 ^ (r + (j + s) % r)) = 2 ^ (r + j) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · rw [bp_testBit hi, Nat.testBit_two_pow, Nat.testBit_two_pow]
    exact decide_eq_decide.mpr (tau_eq hj hs)
  · rw [tb_ge (bp_lt _ _ _ _) hi, tb_ge (Nat.pow_lt_pow_right (by norm_num) (by omega)) hi]

lemma bp_mod {k r c a x : ℕ} (ha : a < r) (hk : 2 * r ≤ k) :
    bp k r c x % 2 ^ a = x % 2 ^ a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < a
  · rw [bp_testBit (by omega), tau_low (by omega)]
  · simp [hi]

def tgt (a : ℕ) (D : Finset (Fin (2 ^ a))) (x y : ℕ) : Bool :=
  xor (x.testBit (y % 2 ^ a))
    (decide (Nat.xor x y ∈ D.image (fun j : Fin (2 ^ a) => 2 ^ (2 ^ a + j.val))))

lemma tgt_bp {a k : ℕ} (hk : 2 * 2 ^ a ≤ k) (s : Fin (2 ^ a)) (D : Finset (Fin (2 ^ a)))
    {x y : ℕ} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    tgt a D (bp k (2 ^ a) s.val x) (bp k (2 ^ a) s.val y) =
      tgt a (D.image (fun j => j + s)) x y := by
  have ha : a < 2 ^ a := Nat.lt_two_pow_self
  have hxy : x ^^^ y < 2 ^ k := Nat.xor_lt_two_pow hx hy
  have hsr : s.val + (2 ^ a - s.val) = 2 ^ a := by omega
  unfold tgt
  congr 1
  · rw [bp_mod ha hk, bp_testBit (by have := Nat.mod_lt y (show 0 < 2 ^ a by positivity); omega),
      tau_low (Nat.mod_lt _ (by positivity))]
  · apply decide_eq_decide.mpr
    change (bp k (2 ^ a) s.val x ^^^ bp k (2 ^ a) s.val y ∈ _) ↔ (x ^^^ y ∈ _)
    rw [← bp_xor]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨j, hj, e⟩
      refine ⟨j + s, ⟨j, hj, rfl⟩, ?_⟩
      have h1 := bp_pow (k := k) hk j.2 (le_of_lt s.2)
      rw [← Fin.val_add, e] at h1
      have h2 := congrArg (bp k (2 ^ a) (2 ^ a - s.val)) h1
      rw [bp_bp hk hsr (Nat.pow_lt_pow_right (by norm_num) (by omega)), bp_bp hk hsr hxy] at h2
      exact h2
    · rintro ⟨_, ⟨j, hj, rfl⟩, e⟩
      refine ⟨j, hj, ?_⟩
      rw [← e, Fin.val_add, bp_pow hk j.2 (le_of_lt s.2)]

def ren (ρ : ℕ → ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ C.output⟩

lemma key (ρ : ℕ → ℕ) (x y : List Bool) (hlen : x.length = y.length)
    (h1 : ∀ i, i < y.length → ρ i < x.length ∧ x.getD (ρ i) false = y.getD i false)
    (h2 : ∀ i, y.length ≤ i → ρ i = i) (G : List Bool) (i : ℕ) :
    (x ++ G).getD (ρ i) false = (y ++ G).getD i false := by
  by_cases hi : i < y.length
  · obtain ⟨a, b⟩ := h1 i hi
    rw [List.getD_append _ _ _ _ a, List.getD_append _ _ _ _ hi, b]
  · rw [h2 i (le_of_not_gt hi), List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]

lemma wires_ren (ρ : ℕ → ℕ) (x y : List Bool) (hlen : x.length = y.length)
    (h1 : ∀ i, i < y.length → ρ i < x.length ∧ x.getD (ρ i) false = y.getD i false)
    (h2 : ∀ i, y.length ≤ i → ρ i = i) (gs : List Gate) :
    ∀ G : List Bool, ∃ G' : List Bool,
      List.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (x ++ G)
        (gs.map (fun g : Gate => (⟨g.op, g.inputs.map ρ⟩ : Gate))) = x ++ G' ∧
      List.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (y ++ G)
        gs = y ++ G' := by
  induction gs with
  | nil => intro G; exact ⟨G, rfl, rfl⟩
  | cons g gs ih =>
    intro G
    simp only [List.map_cons, List.foldl_cons, List.map_map]
    have hk : ((fun i => (x ++ G).getD i false) ∘ ρ) = fun i => (y ++ G).getD i false :=
      funext (key ρ x y hlen h1 h2 G)
    rw [hk, List.append_assoc, List.append_assoc]
    exact ih _

lemma eval_ren (ρ : ℕ → ℕ) (x y : List Bool) (hlen : x.length = y.length)
    (h1 : ∀ i, i < y.length → ρ i < x.length ∧ x.getD (ρ i) false = y.getD i false)
    (h2 : ∀ i, y.length ≤ i → ρ i = i) (C : Circuit) :
    (ren ρ C).eval x = C.eval y := by
  obtain ⟨G', e1, e2⟩ := wires_ren ρ x y hlen h1 h2 C.gates []
  rw [List.append_nil] at e1 e2
  unfold Circuit.eval Circuit.wires
  simp only [ren]
  rw [e1, e2]
  exact key ρ x y hlen h1 h2 G' _

lemma oneEach_len {N : ℕ} (u v : Fin N) : (oneEach u v).length = N + N := by
  simp [oneEach]

lemma oneEach_getD {N : ℕ} (u v : Fin N) (i : ℕ) :
    (oneEach u v).getD i false = (decide (i = u.val) || decide (i = N + v.val)) := by
  unfold oneEach
  by_cases hi : i < N
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    have : ¬ i = N + v.val := by omega
    simp [List.getD_eq_getElem?_getD, hi, this, Fin.ext_iff]
  · rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
    have h3 : ¬ i = u.val := by omega
    by_cases h4 : i - N < N
    · have h5 : (i - N = v.val) ↔ (i = N + v.val) := by omega
      simp [List.getD_eq_getElem?_getD, h3, h4, Fin.ext_iff, h5]
    · have h5 : ¬ (i = N + v.val) := by omega
      simp [List.getD_eq_getElem?_getD, h3, h4, h5]

def rho (N : ℕ) (f : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < N then f i else if i < N + N then N + f (i - N) else i

lemma eval_rho {N : ℕ} (f g : ℕ → ℕ) (hf : ∀ i, i < N → f i < N) (hg : ∀ i, i < N → g i < N)
    (hfg : ∀ i, i < N → f (g i) = i) (hgf : ∀ i, i < N → g (f i) = i) (C : Circuit)
    (u v : Fin N) :
    (ren (rho N f) C).eval (oneEach u v) =
      C.eval (oneEach (⟨g u.val, hg _ u.2⟩ : Fin N) (⟨g v.val, hg _ v.2⟩ : Fin N)) := by
  apply eval_ren
  · rw [oneEach_len, oneEach_len]
  · intro i hi
    rw [oneEach_len] at hi
    rw [oneEach_len, oneEach_getD, oneEach_getD]
    unfold rho
    by_cases h : i < N
    · have := hf i h
      rw [if_pos h]
      refine ⟨by omega, ?_⟩
      have e1 : (f i = u.val) ↔ (i = g u.val) := by
        constructor
        · intro e; rw [← e, hgf i h]
        · intro e; rw [e, hfg _ u.2]
      have e2 : ¬ (f i = N + v.val) := by omega
      have e3 : ¬ (i = N + g v.val) := by omega
      simp [e1, e2, e3]
    · have h' : i - N < N := by omega
      have := hf _ h'
      rw [if_neg h, if_pos hi]
      refine ⟨by omega, ?_⟩
      have e1 : (f (i - N) = v.val) ↔ (i = N + g v.val) := by
        constructor
        · intro e'
          have := hgf _ h'
          rw [e'] at this
          omega
        · intro e
          have e' : i - N = g v.val := by omega
          rw [e', hfg _ v.2]
      have e2 : ¬ (N + f (i - N) = u.val) := by omega
      have e3 : ¬ (i = g u.val) := by have := hg _ u.2; omega
      simp [e1, e2, e3]
  · intro i hi
    rw [oneEach_len] at hi
    unfold rho
    rw [if_neg (by omega), if_neg (by omega)]

def loss (a k : ℕ) (C : Circuit) (D : Finset (Fin (2 ^ a))) : ℕ :=
  ((Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))).filter (fun z =>
    C.eval (oneEach z.1 z.2) ≠ tgt a D z.1.val z.2.val)).card

def rot (a k : ℕ) (C : Circuit) (s : Fin (2 ^ a)) : Circuit :=
  ren (rho (2 ^ k) (bp k (2 ^ a) s.val)) C

lemma loss_rot {a k : ℕ} (hk : 2 * 2 ^ a ≤ k) (C : Circuit) (s : Fin (2 ^ a))
    (D : Finset (Fin (2 ^ a))) :
    loss a k (rot a k C s) D = loss a k C (D.image (fun j => j + s)) := by
  have h1 : s.val + (2 ^ a - s.val) = 2 ^ a := by omega
  have h2 : (2 ^ a - s.val) + s.val = 2 ^ a := by omega
  let E : Fin (2 ^ k) ≃ Fin (2 ^ k) :=
    { toFun := fun x => ⟨bp k (2 ^ a) (2 ^ a - s.val) x.val, bp_lt _ _ _ _⟩
      invFun := fun x => ⟨bp k (2 ^ a) s.val x.val, bp_lt _ _ _ _⟩
      left_inv := fun x => Fin.ext (bp_bp hk h2 x.2)
      right_inv := fun x => Fin.ext (bp_bp hk h1 x.2) }
  unfold loss
  apply Finset.card_equiv (E.prodCongr E)
  intro z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodCongr_apply, Prod.map_fst,
    Prod.map_snd]
  have e1 := eval_rho (N := 2 ^ k) (bp k (2 ^ a) s.val) (bp k (2 ^ a) (2 ^ a - s.val))
    (fun i _ => bp_lt _ _ _ _) (fun i _ => bp_lt _ _ _ _)
    (fun i hi => bp_bp hk h2 hi) (fun i hi => bp_bp hk h1 hi) C z.1 z.2
  have e2 := tgt_bp hk s D (bp_lt k (2 ^ a) (2 ^ a - s.val) z.1.val)
    (bp_lt k (2 ^ a) (2 ^ a - s.val) z.2.val)
  rw [bp_bp hk h2 z.1.2, bp_bp hk h2 z.2.2] at e2
  unfold rot
  rw [e1, e2]
  rfl

lemma rot_len (a k : ℕ) (C : Circuit) (s : Fin (2 ^ a)) :
    (rot a k C s).gates.length = C.gates.length := by
  simp [rot, ren]

lemma rot_fan (a k : ℕ) (C : Circuit) (s : Fin (2 ^ a))
    (h : ∀ g ∈ C.gates, g.inputs.length ≤ 2) : ∀ g ∈ (rot a k C s).gates, g.inputs.length ≤ 2 := by
  intro g hg
  simp only [rot, ren, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  simpa using h g' hg'

lemma rot_cost (a k : ℕ) (C : Circuit) (s : Fin (2 ^ a)) :
    (rot a k C s).gates.countP (fun g => g.inputs.length == 2) =
      C.gates.countP (fun g => g.inputs.length == 2) := by
  simp only [rot, ren, List.countP_map]
  congr 1
  funext g
  simp

lemma flip_step {α ι : Type} [DecidableEq ι] (S : Finset α) (f g : α → Bool) (m : α → ℕ)
    (lab : ι → ℕ) (hlab : Function.Injective lab) (D : Finset ι) (j : ι) (hj : j ∉ D) :
    (S.filter (fun z => f z ≠ xor (g z) (decide (m z ∈ (insert j D).image lab)))).card +
        (S.filter (fun z => m z = lab j ∧ f z ≠ g z)).card =
      (S.filter (fun z => f z ≠ xor (g z) (decide (m z ∈ D.image lab)))).card +
        (S.filter (fun z => m z = lab j ∧ f z = g z)).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hA : m z = lab j
  · have h1 : m z ∈ (insert j D).image lab := by
      rw [hA]; exact Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)
    have h2 : ¬ m z ∈ D.image lab := by
      rw [hA, Finset.mem_image]
      rintro ⟨j', hj', e⟩
      exact hj (hlab e ▸ hj')
    simp only [h1, h2]
    simp only [hA, true_and]
    cases f z <;> cases g z <;> simp
  · have h1 : (m z ∈ (insert j D).image lab) ↔ (m z ∈ D.image lab) := by
      simp only [Finset.mem_image, Finset.mem_insert]
      constructor
      · rintro ⟨j', hj' | hj', e⟩
        · exact absurd (hj' ▸ e.symm) hA
        · exact ⟨j', hj', e⟩
      · rintro ⟨j', hj', e⟩
        exact ⟨j', Or.inr hj', e⟩
    simp only [h1, hA, false_and, if_false, add_zero]

lemma loss_add {a k : ℕ} (C : Circuit) (D : Finset (Fin (2 ^ a))) :
    loss a k C D + ∑ j ∈ D, ((Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))).filter (fun z =>
        z.1.val ^^^ z.2.val = 2 ^ (2 ^ a + j.val) ∧
          C.eval (oneEach z.1 z.2) ≠ z.1.val.testBit (z.2.val % 2 ^ a))).card =
      loss a k C ∅ + ∑ j ∈ D, ((Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))).filter (fun z =>
        z.1.val ^^^ z.2.val = 2 ^ (2 ^ a + j.val) ∧
          C.eval (oneEach z.1 z.2) = z.1.val.testBit (z.2.val % 2 ^ a))).card := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert j D hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hinj : Function.Injective (fun j : Fin (2 ^ a) => 2 ^ (2 ^ a + j.val)) := by
      intro x y h
      have := Nat.pow_right_injective (le_refl 2) h
      exact Fin.ext (by omega)
    have st := flip_step (Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k)))
      (fun z => C.eval (oneEach z.1 z.2)) (fun z => z.1.val.testBit (z.2.val % 2 ^ a))
      (fun z => z.1.val ^^^ z.2.val) (fun j : Fin (2 ^ a) => 2 ^ (2 ^ a + j.val)) hinj D j hj
    have st' : loss a k C (insert j D) + _ = loss a k C D + _ := st
    omega

lemma avg {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι] (L : Finset ι → ℕ)
    (e n : ι → ℕ) (hL : ∀ D, L D + ∑ j ∈ D, e j = L ∅ + ∑ j ∈ D, n j) (D : Finset ι)
    (ht : D.card ≤ Fintype.card ι) :
    ∑ s : ι, L (D.image (fun j => j + s)) =
      (Fintype.card ι - D.card) * L ∅ + D.card * L Finset.univ := by
  have h1 : ∑ s : ι, L (D.image (fun j => j + s)) + ∑ s : ι, ∑ j ∈ D.image (fun j => j + s), e j =
      ∑ s : ι, (L ∅ + ∑ j ∈ D.image (fun j => j + s), n j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => hL _)
  have h2 : ∀ w : ι → ℕ, ∑ s : ι, ∑ j ∈ D.image (fun j => j + s), w j = D.card * ∑ j, w j := by
    intro w
    have : ∀ s : ι, ∑ j ∈ D.image (fun j => j + s), w j = ∑ j ∈ D, w (j + s) := fun s =>
      Finset.sum_image (fun x _ y _ h => add_right_cancel h)
    simp_rw [this]
    rw [Finset.sum_comm]
    have : ∀ j : ι, ∑ s : ι, w (j + s) = ∑ s, w s := fun j =>
      Equiv.sum_comp (Equiv.addLeft j) w
    simp_rw [this]
    rw [Finset.sum_const, smul_eq_mul]
  have h3 := hL Finset.univ
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, h2, h2] at h1
  have h4 : D.card * L Finset.univ + D.card * ∑ j, e j = D.card * L ∅ + D.card * ∑ j, n j := by
    rw [← mul_add, h3, mul_add]
  have h5 : (Fintype.card ι - D.card) * L ∅ + D.card * L ∅ = Fintype.card ι * L ∅ := by
    rw [← add_mul, Nat.sub_add_cancel ht]
  linarith

lemma score_id {a k t : ℕ} (C : Circuit) (D : Finset (Fin (2 ^ a))) (hD : D.card = t)
    (ht : t ≤ 2 ^ a) :
    ∑ s : Fin (2 ^ a), loss a k C (D.image (fun j => j + s)) =
      (2 ^ a - t) * loss a k C ∅ + t * loss a k C Finset.univ := by
  have := avg (loss a k C) _ _ (loss_add C) D (by simpa [hD] using ht)
  rw [hD, Fintype.card_fin] at this
  exact this

end PEqualNP.Outside.L_meta_26025
theorem PEqualNP.Outside.L_meta_26025 : (∀ (a k B t : ℕ), 2*2^a ≤ k → t ≤ 2^a →
  let r := 2^a
  let N := 2^k
  let I := Fin r
  let X := Fin N
  let label := fun j : I => 2^(r+j.val)
  let loss := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (D : Finset I) =>
    ((Finset.univ : Finset (X × X)).filter (fun z =>
      C.eval (PEqualNP.Represents.oneEach z.1 z.2) ≠
        xor (z.1.val.testBit (z.2.val % r)) (decide (Nat.xor z.1.val z.2.val ∈ D.image label)))).card
  let cost := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
    C.gates.countP (fun g => g.inputs.length == 2)
  let fits := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ cost C ≤ B
  let score := fun C => (r-t)*loss C ∅ + t*loss C Finset.univ
  ∃ (base : PEqualNP.CircuitLowerBounds.Circuit) (rot : I → PEqualNP.CircuitLowerBounds.Circuit),
    fits base ∧ (∀ C, fits C → score base ≤ score C) ∧
    (∀ s, fits (rot s) ∧ cost (rot s) = cost base ∧ (rot s).gates.length = base.gates.length ∧
      ∀ D : Finset I, loss (rot s) D = loss base (D.image (fun j => j+s))) ∧
    (∀ D : Finset I, D.card = t → (∑ s : I, loss (rot s) D) = score base) ∧
    ∀ (n : ℕ) (p : Fin n → ℝ) (circs : Fin n → PEqualNP.CircuitLowerBounds.Circuit),
      (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 → (∀ i, fits (circs i)) →
      ∃ D : Finset I, D.card = t ∧ (score base : ℝ) ≤
        (r : ℝ) * ∑ i : Fin n, p i * (loss (circs i) D : ℝ)) := by
  intro a k B t hk ht r N I X label loss cost fits score
  have hfit0 : fits ⟨[], 0⟩ := ⟨by simp, by simp [cost]⟩
  have hex : ∃ n, ∃ C, fits C ∧ score C = n := ⟨_, _, hfit0, rfl⟩
  classical
  obtain ⟨base, hbase, hsc⟩ := Nat.find_spec hex
  have hmin : ∀ C, fits C → score base ≤ score C := by
    intro C hC
    rw [hsc]
    exact Nat.find_min' hex ⟨C, hC, rfl⟩
  have hid : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (D : Finset I), D.card = t →
      ∑ s : I, loss C (D.image (fun j => j + s)) = score C := fun C D hD =>
    PEqualNP.Outside.L_meta_26025.score_id C D hD ht
  have hrot : ∀ (s : I) (D : Finset I),
      loss (PEqualNP.Outside.L_meta_26025.rot a k base s) D =
        loss base (D.image (fun j => j + s)) := fun s D =>
    PEqualNP.Outside.L_meta_26025.loss_rot hk base s D
  refine ⟨base, PEqualNP.Outside.L_meta_26025.rot a k base, hbase, hmin, ?_, ?_, ?_⟩
  · intro s
    have hc := PEqualNP.Outside.L_meta_26025.rot_cost a k base s
    refine ⟨⟨PEqualNP.Outside.L_meta_26025.rot_fan a k base s hbase.1, ?_⟩, hc,
      PEqualNP.Outside.L_meta_26025.rot_len a k base s, hrot s⟩
    exact le_of_eq_of_le hc hbase.2
  · intro D hD
    rw [← hid base D hD]
    exact Finset.sum_congr rfl (fun s _ => hrot s D)
  · intro n p circs hp hsum hfitc
    obtain ⟨D0, -, hD0⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset I)) (n := t) (by simpa [I, r] using ht)
    have hcard : ∀ s : I, (D0.image (fun j => j + s)).card = t := fun s => by
      rw [Finset.card_image_of_injective _ (add_left_injective s), hD0]
    have hkey : ∑ _s : I, (score base : ℝ) ≤
        ∑ s : I, (r : ℝ) * ∑ i : Fin n, p i * (loss (circs i) (D0.image (fun j => j + s)) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
        Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have h1 : (score base : ℝ) = ∑ i : Fin n, p i * (score base : ℝ) := by
        rw [← Finset.sum_mul, hsum, one_mul]
      rw [h1]
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hp i)
      have h2 := hid (circs i) D0 hD0
      have h3 : ((score (circs i) : ℕ) : ℝ) =
          ∑ s : I, (loss (circs i) (D0.image (fun j => j + s)) : ℝ) := by
        rw [← h2]; push_cast; rfl
      rw [← h3]
      exact_mod_cast hmin _ (hfitc i)
    obtain ⟨s, -, hs⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hkey
    exact ⟨D0.image (fun j => j + s), hcard s, hs⟩

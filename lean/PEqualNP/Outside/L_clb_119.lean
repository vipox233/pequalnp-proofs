import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_743
import PEqualNP.Outside.L_lib_575
import PEqualNP.Outside.L_lib_845

namespace PEqualNP.Outside.L_clb_119_aux

def seqF {X Y : Type} {S p : Nat} (hp : 0 < p) (α : Fin p → X → Fin S → Fin S)
    (β : Fin p → Y → Fin S → Fin S) (x : X) (y : Y) (s0 : Fin S) : Nat → Fin S
  | 0 => s0
  | k+1 => β ⟨k % p, Nat.mod_lt _ hp⟩ y (α ⟨k % p, Nat.mod_lt _ hp⟩ x (seqF hp α β x y s0 k))

theorem fold_take {σ : Type} {p : Nat} (G : σ → Fin p → σ) (s0 : σ) (sq : Nat → σ)
    (h0 : sq 0 = s0) (hs : ∀ k (hk : k < p), sq (k+1) = G (sq k) ⟨k, hk⟩) :
    ∀ k, k ≤ p → ((List.finRange p).take k).foldl G s0 = sq k := by
  intro k
  induction k with
  | zero => intro _; simp [h0]
  | succ k ih =>
    intro hk
    rw [List.take_add_one, List.foldl_append, ih (by omega), hs k (by omega)]
    have : (List.finRange p)[k]? = some ⟨k, by omega⟩ := by
      rw [List.getElem?_eq_getElem (by simp; omega)]
      simp
    rw [this]
    rfl

theorem fold_full {σ : Type} {p : Nat} (G : σ → Fin p → σ) (s0 : σ) (sq : Nat → σ)
    (h0 : sq 0 = s0) (hs : ∀ k (hk : k < p), sq (k+1) = G (sq k) ⟨k, hk⟩) :
    (List.finRange p).foldl G s0 = sq p := by
  have := fold_take G s0 sq h0 hs p le_rfl
  rwa [List.take_of_length_le (by simp)] at this

theorem rect_gen {X Y : Type} {S p : Nat} (hp : 0 < p) (α : Fin p → X → Fin S → Fin S)
    (β : Fin p → Y → Fin S → Fin S) (s0 : Fin S) (o : Fin S → Bool) :
    ∃ (lab : X → Y → Fin (2*S^(2*p-1))) (o' : Fin (2*S^(2*p-1)) → Bool),
      (∀ x y, o' (lab x y) = o ((List.finRange p).foldl (fun s j => β j y (α j x s)) s0)) ∧
      (∀ x y x' y', lab x y = lab x' y' → lab x y' = lab x y) := by
  have hcard : Fintype.card (((Fin p → Fin S) × (Fin (p-1) → Fin S)) × Bool) = 2*S^(2*p-1) := by
    simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Finset.prod_const,
      Finset.card_univ, Fintype.card_bool]
    rw [← pow_add, show p + (p-1) = 2*p-1 by omega, mul_comm]
  let e := Fintype.equivFinOfCardEq hcard
  let sq := fun x y => seqF hp α β x y s0
  let D := fun (x : X) (y : Y) =>
    (((fun i : Fin p => α ⟨i.val % p, Nat.mod_lt _ hp⟩ x (sq x y i.val)),
      (fun i : Fin (p-1) => sq x y (i.val+1))), o (sq x y p))
  refine ⟨fun x y => e (D x y), fun t => (e.symm t).2, ?_, ?_⟩
  · intro x y
    simp only [Equiv.symm_apply_apply]
    show o (sq x y p) = _
    congr 1
    symm
    apply fold_full _ s0 (sq x y) rfl
    intro k hk
    show β _ y (α _ x _) = _
    have : (⟨k % p, Nat.mod_lt _ hp⟩ : Fin p) = ⟨k, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)
    rw [this]
  · intro x y x' y' hl
    have hD : D x y = D x' y' := e.injective hl
    have hc := congrArg (fun d => d.1.1) hD
    have hd := congrArg (fun d => d.1.2) hD
    have hb := congrArg (fun d => d.2) hD
    simp only [D] at hc hd hb
    have claim : ∀ k, k ≤ p - 1 → sq x y' k = sq x y k := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have h1 := congrFun hc ⟨k, by omega⟩
        have h2 := congrFun hd ⟨k, by omega⟩
        simp only at h1 h2
        show β _ y' (α _ x (sq x y' k)) = sq x y (k+1)
        rw [ih (by omega), h1, h2]
        rfl
    suffices key : D x y' = D x y by
      show e (D x y') = e (D x y)
      rw [key]
    simp only [D]
    refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_
      · funext i
        show α _ x (sq x y' i.val) = α _ x (sq x y i.val)
        rw [claim i.val (by omega)]
      · funext i
        show sq x y' (i.val+1) = sq x y (i.val+1)
        rw [claim (i.val+1) (by omega)]
    · show o (sq x y' p) = o (sq x y p)
      rw [hb]
      congr 1
      obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p-1, by omega⟩
      have h1 := congrFun hc ⟨q, by omega⟩
      simp only at h1
      have e1 : sq x y' p = β ⟨q % p, Nat.mod_lt _ hp⟩ y' (α ⟨q % p, Nat.mod_lt _ hp⟩ x (sq x y' q)) := by
        subst hq; rfl
      have e2 : sq x' y' p = β ⟨q % p, Nat.mod_lt _ hp⟩ y' (α ⟨q % p, Nat.mod_lt _ hp⟩ x' (sq x' y' q)) := by
        subst hq; rfl
      rw [e1, e2, claim q (by omega), h1]


def sols (n L : Nat) (hn : 0 < n) (tab : Fin n × (Fin L → Bool) → Bool) : Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
    ∀ i : Fin n, tab (i, fun j => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true)

def Emb (n L : Nat) (hn : 0 < n) (a M : Nat) : Prop :=
  ∃ (code : Fin M → (Fin n → Bool)) (base : Fin n × (Fin L → Bool) → Bool)
    (left right : Fin M → Fin n × (Fin L → Bool)),
    Function.Injective code ∧ (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val) ∧
    ∀ A B : Finset (Fin M), sols n L hn (fun slot => base slot || decide (slot ∈ A.image left) ||
      decide (slot ∈ B.image right)) = (A ∩ B).image code

theorem Emb_cast {n n' L a M : Nat} (e : n' = n) (hn : 0 < n) (hn' : 0 < n') :
    Emb n' L hn' a M → Emb n L hn a M := by
  subst e; exact id

def tot (n L : Nat) (hn : 0 < n) (table : Fin n → (Fin L → Bool) → Bool) : Nat :=
  ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
    ∀ i : Fin n, table i (fun j => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true)).card

theorem drop_ge {n a : Nat} : ∀ (l : List (Fin n)), l.Pairwise (· < ·) →
    ∀ x ∈ l.dropWhile (fun i => decide (i.val < a)), a ≤ x.val := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons y l ih =>
    intro hl x hx
    rw [List.pairwise_cons] at hl
    by_cases hy : y.val < a
    · rw [List.dropWhile_cons_of_pos (by simpa using hy)] at hx
      exact ih hl.2 x hx
    · rw [List.dropWhile_cons_of_neg (by simpa using hy)] at hx
      rcases List.mem_cons.mp hx with h | h
      · subst h; omega
      · have := hl.1 x h
        have : y.val < x.val := this
        omega

theorem split_fold {σ : Type} {n a : Nat} (g h1 h2 : σ → Fin n → σ) (s : σ)
    (e1 : ∀ st pos, pos.val < a → g st pos = h1 st pos)
    (e2 : ∀ st pos, a ≤ pos.val → g st pos = h2 st pos) :
    (List.finRange n).foldl g s = ((List.finRange n).dropWhile (fun i => decide (i.val < a))).foldl h2
      (((List.finRange n).takeWhile (fun i => decide (i.val < a))).foldl h1 s) := by
  conv_lhs => rw [← List.takeWhile_append_dropWhile (p := fun i : Fin n => decide (i.val < a))
    (l := List.finRange n)]
  rw [List.foldl_append]
  rw [List.foldl_ext g h1 s (fun st pos hm => e1 st pos (by simpa using List.mem_takeWhile_imp hm))]
  exact List.foldl_ext g h2 _ (fun st pos hm => e2 st pos (drop_ge _ (List.pairwise_lt_finRange n) pos hm))

theorem arith1 (v u R ones W : Nat) (huv : u ≤ v) (hs : ones + W = R) (h : (v+u)*R ≤ 2*v*W) :
    2*v*ones ≤ (v-u)*R := by
  have e : (v - u) + (v+u) = 2*v := by omega
  have : 2*v*ones + (v+u)*R ≤ (v-u)*R + (v+u)*R := by
    calc 2*v*ones + (v+u)*R ≤ 2*v*ones + 2*v*W := by omega
      _ = 2*v*R := by rw [← hs]; ring
      _ = (v-u)*R + (v+u)*R := by rw [← add_mul, e]
  omega

theorem from_emb (n w p : Nat) (hn : 0 < n) (hp : 0 < p) (a M : Nat) (hE : Emb n (w+1) hn a M)
    (S R u v : Nat) (hR : 0 < R) (hv : 0 < v) (huv : u ≤ v)
    (init : Fin R → Fin S)
    (update : Fin R → Fin p → Fin n → Fin S → ((Fin (w+1) → Bool) → Bool) → Fin S)
    (out : Fin R → Fin S → Bool)
    (herr : ∀ table : Fin n → (Fin (w+1) → Bool) → Bool, tot n (w+1) hn table ≤ 1 →
      (v+u)*R ≤ 2*v*((List.finRange R).filter (fun r => out r ((List.finRange p).foldl
        (fun prev scan => (List.finRange n).foldl (fun st pos => update r scan pos st (table pos)) prev)
        (init r)) == decide (tot n (w+1) hn table = 1))).length) :
    2^(M*u^2) ≤ (2*S^(2*p-1))^(16*v^2) := by
  obtain ⟨code, base, left, right, hinj, hpos, hsol⟩ := hE
  let tabOf : Finset (Fin M) → Finset (Fin M) → Fin n → (Fin (w+1) → Bool) → Bool :=
    fun A B i pat => base (i,pat) || decide ((i,pat) ∈ A.image left) ||
      decide ((i,pat) ∈ B.image right)
  have htot : ∀ A B, tot n (w+1) hn (tabOf A B) = (A ∩ B).card := by
    intro A B
    change (sols n (w+1) hn (fun slot => base slot || decide (slot ∈ A.image left) ||
      decide (slot ∈ B.image right))).card = _
    rw [hsol, Finset.card_image_of_injective _ hinj]
  have hA : ∀ A B B' (i : Fin n), i.val < a → tabOf A B i = tabOf A B' i := by
    intro A B B' i hi
    funext pat
    have : ∀ B'' : Finset (Fin M), decide ((i,pat) ∈ B''.image right) = false := by
      intro B''
      simp only [decide_eq_false_iff_not, Finset.mem_image, not_exists, not_and]
      intro k _ hk
      have := (hpos k).2
      rw [hk] at this
      exact absurd hi (by simpa using this)
    simp only [tabOf, this]
  have hB : ∀ A A' B (i : Fin n), a ≤ i.val → tabOf A B i = tabOf A' B i := by
    intro A A' B i hi
    funext pat
    have : ∀ A'' : Finset (Fin M), decide ((i,pat) ∈ A''.image left) = false := by
      intro A''
      simp only [decide_eq_false_iff_not, Finset.mem_image, not_exists, not_and]
      intro k _ hk
      have := (hpos k).1
      rw [hk] at this
      exact absurd hi (by simpa using this)
    simp only [tabOf, this]
  let α := fun (r : Fin R) (j : Fin p) (A : Finset (Fin M)) (s : Fin S) =>
    ((List.finRange n).takeWhile (fun i => decide (i.val < a))).foldl
      (fun st pos => update r j pos st (tabOf A ∅ pos)) s
  let β := fun (r : Fin R) (j : Fin p) (B : Finset (Fin M)) (s : Fin S) =>
    ((List.finRange n).dropWhile (fun i => decide (i.val < a))).foldl
      (fun st pos => update r j pos st (tabOf ∅ B pos)) s
  have hpass : ∀ r j A B s, (List.finRange n).foldl (fun st pos => update r j pos st (tabOf A B pos)) s
      = β r j B (α r j A s) := by
    intro r j A B s
    apply split_fold
    · intro st pos hpos'
      rw [hA A B ∅ pos hpos']
    · intro st pos hpos'
      rw [hB A ∅ B pos hpos']
  have hr := fun r : Fin R => rect_gen hp (α r) (β r) (init r) (out r)
  choose lab o' hlab hrect using hr
  have hacc : ∀ r A B, o' r (lab r A B) = out r ((List.finRange p).foldl
        (fun prev scan => (List.finRange n).foldl (fun st pos => update r scan pos st (tabOf A B pos)) prev)
        (init r)) := by
    intro r A B
    rw [hlab]
    congr 2
    funext s j
    exact (hpass r j A B s).symm
  have hS : 0 < S := by
    have := (init ⟨0, hR⟩).isLt
    omega
  have hT : 0 < 2*S^(2*p-1) := by positivity
  have key := PEqualNP.Outside.L_lib_575 M (2*S^(2*p-1)) R (2*v) (v-u) hT hR (by omega) (by omega)
    (fun _ => v+u) (fun _ => by omega) lab o' hrect ?_ ?_
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      show v+u-(v-u) = 2*u by omega] at key
    have e1 : M*(2*u)^2 = (M*u^2)*4 := by ring
    have e2 : 16*(2*v)^2 = (16*v^2)*4 := by ring
    rw [e1, e2, pow_mul (2:ℕ) (M*u^2) 4, pow_mul (2*S^(2*p-1)) (16*v^2) 4] at key
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp key
  · intro x y hxy
    have h0 : tot n (w+1) hn (tabOf x y) = 0 := by
      rw [htot, Finset.disjoint_iff_inter_eq_empty.mp hxy]
      rfl
    have e := herr (tabOf x y) (by omega)
    rw [h0] at e
    have hf : (List.finRange R).filter (fun r => out r ((List.finRange p).foldl
        (fun prev scan => (List.finRange n).foldl (fun st pos => update r scan pos st (tabOf x y pos)) prev)
        (init r)) == decide (0 = 1)) = (List.finRange R).filter (fun r => !(o' r (lab r x y))) := by
      apply List.filter_congr
      intro r _
      rw [hacc]
      simp
    rw [hf] at e
    have hs := (List.length_eq_length_filter_add (l := List.finRange R) (fun r => o' r (lab r x y))).symm
    rw [List.length_finRange] at hs
    exact arith1 v u R _ _ huv hs e
  · intro i x y hxy
    have h1 : tot n (w+1) hn (tabOf x y) = 1 := by
      rw [htot, hxy]
      rfl
    have e := herr (tabOf x y) (by omega)
    rw [h1] at e
    have hf : (List.finRange R).filter (fun r => out r ((List.finRange p).foldl
        (fun prev scan => (List.finRange n).foldl (fun st pos => update r scan pos st (tabOf x y pos)) prev)
        (init r)) == decide (1 = 1)) = (List.finRange R).filter (fun r => o' r (lab r x y)) := by
      apply List.filter_congr
      intro r _
      rw [hacc]
      simp
    rw [hf] at e
    exact e


theorem direct_gen (n L : Nat) (hn : 0 < n) (h2 : 2 ≤ n) (off m : Nat) (hom : off + m ≤ n)
    (c01 : ∀ i k, i < 2 → off ≤ k → k < off + m → ∃ j, j < L ∧ (i + j) % n = k)
    (cZ : ∀ k, k < n → ¬(off ≤ k ∧ k < off + m) →
      ∃ i j, 2 ≤ i ∧ i < n ∧ j < L ∧ (i + j) % n = k) :
    Emb n L hn 1 (2^m) := by
  let code : Fin (2^m) → Fin n → Bool := fun i k =>
    decide (off ≤ k.val ∧ k.val < off + m) && Nat.testBit i.val (k.val - off)
  let win : Nat → (Fin n → Bool) → Fin L → Bool := fun i x j => x ⟨(i + j.val) % n, Nat.mod_lt _ hn⟩
  let base : Fin n × (Fin L → Bool) → Bool := fun slot => decide (2 ≤ slot.1.val ∧
    ∀ j : Fin L, ¬(off ≤ (slot.1.val + j.val) % n ∧ (slot.1.val + j.val) % n < off + m) →
      slot.2 j = false)
  let left : Fin (2^m) → Fin n × (Fin L → Bool) := fun k => (⟨0, hn⟩, win 0 (code k))
  let right : Fin (2^m) → Fin n × (Fin L → Bool) := fun k => (⟨1, by omega⟩, win 1 (code k))
  have hcv : ∀ i (k : Fin n), ¬(off ≤ k.val ∧ k.val < off + m) → code i k = false := by
    intro i k hk
    simp [code, hk]
  have det : ∀ i, i < 2 → ∀ x y : Fin n → Bool,
      (∀ k : Fin n, ¬(off ≤ k.val ∧ k.val < off + m) → x k = false) →
      (∀ k : Fin n, ¬(off ≤ k.val ∧ k.val < off + m) → y k = false) →
      win i x = win i y → x = y := by
    intro i hi x y hx hy hw
    funext k
    by_cases hk : off ≤ k.val ∧ k.val < off + m
    · obtain ⟨j, hj, hjk⟩ := c01 i k.val hi hk.1 hk.2
      have := congrFun hw ⟨j, hj⟩
      simp only [win] at this
      have e : (⟨(i + j) % n, Nat.mod_lt _ hn⟩ : Fin n) = k := Fin.ext hjk
      rw [e] at this
      exact this
    · rw [hx k hk, hy k hk]
  have hinj : Function.Injective code := by
    intro i i' h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro b
    by_cases hb : b < m
    · have := congrFun h ⟨off + b, by omega⟩
      simpa [code, hb] using this
    · have hm : 2^m ≤ 2^b := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt hm),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le i'.isLt hm)]
  refine ⟨code, base, left, right, hinj, fun i => ⟨Nat.zero_lt_one, le_refl 1⟩, ?_⟩
  intro A B
  have hnl : ∀ (i : Fin n) (pat : Fin L → Bool) (A' : Finset (Fin (2^m))), i.val ≠ 0 →
      decide ((i,pat) ∈ A'.image left) = false := by
    intro i pat A' hi
    simp only [decide_eq_false_iff_not, Finset.mem_image, not_exists, not_and]
    intro k _ hk
    have := congrArg (fun s => s.1.val) hk
    simp [left] at this
    omega
  have hnr : ∀ (i : Fin n) (pat : Fin L → Bool) (B' : Finset (Fin (2^m))), i.val ≠ 1 →
      decide ((i,pat) ∈ B'.image right) = false := by
    intro i pat B' hi
    simp only [decide_eq_false_iff_not, Finset.mem_image, not_exists, not_and]
    intro k _ hk
    have := congrArg (fun s => s.1.val) hk
    simp [right] at this
    omega
  have hnb : ∀ (i : Fin n) (pat : Fin L → Bool), i.val < 2 → base (i,pat) = false := by
    intro i pat hi
    simp only [base, decide_eq_false_iff_not, not_and]
    intro h
    omega
  ext x
  simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.mem_image]
  simp only [Finset.mem_inter]
  constructor
  · intro hx
    have hvan : ∀ k : Fin n, ¬(off ≤ k.val ∧ k.val < off + m) → x k = false := by
      intro k hk
      obtain ⟨i, j, hi2, hin, hj, hijk⟩ := cZ k.val k.isLt hk
      have hxi := hx ⟨i, hin⟩
      rw [hnl _ _ _ (by simp; omega), hnr _ _ _ (by simp; omega)] at hxi
      simp only [Bool.or_false, base, decide_eq_true_eq] at hxi
      have := hxi.2 ⟨j, hj⟩ (by simp only; rw [hijk]; exact hk)
      have e : (⟨(i + j) % n, Nat.mod_lt _ hn⟩ : Fin n) = k := Fin.ext hijk
      simp only at this
      rw [e] at this
      exact this
    have h0 := hx ⟨0, hn⟩
    rw [hnb _ _ (by simp), hnr _ _ _ (by simp)] at h0
    simp only [Bool.false_or, Bool.or_false, decide_eq_true_eq, Finset.mem_image] at h0
    obtain ⟨k, hkA, hk⟩ := h0
    have h1 := hx ⟨1, by omega⟩
    rw [hnb _ _ (by simp), hnl _ _ _ (by simp)] at h1
    simp only [Bool.false_or, Bool.or_false, decide_eq_true_eq, Finset.mem_image] at h1
    obtain ⟨k', hkB, hk'⟩ := h1
    have ek : code k = x := det 0 (by norm_num) _ _ (hcv k) hvan (congrArg Prod.snd hk)
    have ek' : code k' = x := det 1 (by norm_num) _ _ (hcv k') hvan (congrArg Prod.snd hk')
    have : k = k' := hinj (ek.trans ek'.symm)
    subst this
    exact ⟨k, ⟨hkA, hkB⟩, ek⟩
  · rintro ⟨k, ⟨hkA, hkB⟩, rfl⟩ i
    by_cases i0 : i.val = 0
    · have : (i, fun j : Fin L => code k ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = left k := by
        have ei : i = ⟨0, hn⟩ := Fin.ext i0
        subst ei
        rfl
      rw [this]
      simp [Finset.mem_image_of_mem left hkA]
    by_cases i1 : i.val = 1
    · have : (i, fun j : Fin L => code k ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = right k := by
        obtain ⟨iv, hiv⟩ := i
        simp only at i1
        subst i1
        rfl
      rw [this]
      simp [Finset.mem_image_of_mem right hkB]
    · have hb : base (i, fun j : Fin L => code k ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true := by
        simp only [base, decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        intro j hj
        exact hcv k _ hj
      rw [hb]
      rfl


theorem pw : ∀ k, 3 ≤ k → k + 4 ≤ 2^k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

theorem case845 (n w : Nat) (hn : 0 < n) (h32 : 32 ≤ n)
    (hh : n - (w+1) ≤ Nat.clog 2 (2*(n-n/2))) :
    ∃ M, 2^(n-13) ≤ M ∧ Emb n (w+1) hn (n/2) M := by
  obtain ⟨t, ht⟩ : ∃ t, t = Nat.clog 2 (2*(n-n/2)) := ⟨_, rfl⟩
  rw [← ht] at hh
  have hab : n/2 + (n - n/2) = n := by omega
  have hn' : 0 < n/2 + (n-n/2) := by omega
  have ht1 : 2*(n-n/2) ≤ 2^t := by rw [ht]; exact Nat.le_pow_clog (by norm_num) _
  have ht2 : 2^(t.pred) < 2*(n-n/2) := by rw [ht]; exact Nat.pow_pred_clog_lt_self 2 (by omega)
  have ht5 : 5 ≤ t := by
    by_contra hlt
    have : 2^t ≤ 2^4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨P, hP⟩ : ∃ P, P = 2^(t-3) := ⟨_, rfl⟩
  have e4 : 2^(t.pred) = 4*P := by
    rw [hP, show t.pred = (t-3) + 2 by rw [Nat.pred_eq_sub_one]; omega, pow_add]; ring
  have h2P : 2*P ≤ n/2 := by omega
  have hX : P ≤ n/2 - t - 1 := by
    rcases Nat.eq_or_lt_of_le ht5 with h5 | h6
    · subst h5
      norm_num at hP
      omega
    · have := pw (t-3) (by omega)
      rw [← hP] at this
      omega
  have ha : t + 3 ≤ n/2 := by
    rcases Nat.eq_or_lt_of_le ht5 with h5 | h6
    · omega
    · have := pw (t-3) (by omega)
      rw [← hP] at this
      omega
  have hmin : t + 3 ≤ min (n/2) (n-n/2) := le_min ha (by omega)
  have hmax : 2 * max (n/2) (n - n/2) ≤ 2^t := by
    rw [max_eq_right (by omega)]; exact ht1
  obtain ⟨M, code, base, left, right, hM, hc, _, _, hpos, hsol⟩ :=
    PEqualNP.Outside.L_lib_845 (n/2) (n-n/2) w t hn' (by omega) hmin hmax
  refine ⟨M, le_trans ?_ hM,
    Emb_cast hab hn hn' ⟨code, base, left, right, hc, fun i => ⟨(hpos i).1, (hpos i).2.1⟩, hsol⟩⟩
  have e1 : 2^(n-12) = 2^(n/2-t-3) * 2^((n-n/2)-t-3) * (P * P) := by
    rw [hP, ← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  have e2 : 2^(n-13) ≤ 2^(n-12) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e3 : 2^(n/2-t-3) * 2^((n-n/2)-t-3) * (P * P) ≤
      2^(n/2-t-3) * 2^((n-n/2)-t-3) * ((n/2-t-1) * ((n-n/2)-t-1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hX (by omega))
  refine le_trans e2 (le_trans (e1 ▸ e3) ?_)
  calc 2^(n/2-t-3) * 2^((n-n/2)-t-3) * ((n/2-t-1) * ((n-n/2)-t-1))
      = (n/2-t-1) * 2^(n/2-t-3) * (((n-n/2)-t-1) * 2^((n-n/2)-t-3)) := by ring
    _ ≤ _ := by
      apply Nat.mul_le_mul
      · apply Nat.mul_le_mul_right; omega
      · apply Nat.mul_le_mul_right; omega

end PEqualNP.Outside.L_clb_119_aux

theorem PEqualNP.Outside.L_clb_119 : (∀ (n w p : Nat) (hn : 0 < n), 2 ≤ n → 0 < w → 0 < p →
  let h := n-(w+1)
  let direct := if n ≤ w+1 then 2^n else 2^w
  let near := 32 ≤ n ∧ h ≤ Nat.clog 2 (2*(n-n/2))
  ∀ H : Nat, (H ≤ direct ∨ (near ∧ H ≤ 2^(n-13)) ∨
      ∃ a b q s : Nat, n = a+b ∧ 0 < q ∧ 0 < s ∧ s ≤ h ∧
        q*h < a ∧ (q+1)*h ≤ b ∧
        H ≤ q^2*(2^s-1)^(2*(q-1))*2^(n-(2*q*s+(h-s)))) →
  let Pat := Fin (w+1) → Bool
  let Row := Pat → Bool
  let Tab := Fin n → Row
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let total := fun (table : Tab) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      ∀ i : Fin n, table i (fun j => x (loc (i.val+j.val))) = true)).card
  ∀ (S R u v : Nat), 0 < R → 0 < v → u ≤ v →
    ∀ (init : Fin R → Fin S) (update : Fin R → Fin p → Fin n → Fin S → Row → Fin S)
      (out : Fin R → Fin S → Bool),
      let accepted := fun (coin : Fin R) (raw : Tab) => out coin
        ((List.finRange p).foldl (fun prev scan => (List.finRange n).foldl
          (fun st pos => update coin scan pos st (raw pos)) prev) (init coin))
      (∀ table : Tab, total table ≤ 1 → (v+u)*R ≤ 2*v*
        ((List.finRange R).filter (fun r => accepted r table == decide (total table = 1))).length) →
      2^(H*u^2) ≤ (2*S^(2*p-1))^(16*v^2)) := by
  intro n w p hn h2 hw hp h direct near H hH Pat Row Tab loc total S R u v hR hv huv init update out
    accepted herr
  have hhd : h = n - (w+1) := rfl
  have hE : ∃ a M, H ≤ M ∧ PEqualNP.Outside.L_clb_119_aux.Emb n (w+1) hn a M := by
    rcases hH with hd | ⟨⟨h32, hnear⟩, hb⟩ | ⟨a, b, q, s, hab, hq, hs, hsh, h1, h2', hM⟩
    · have hd' : H ≤ if n ≤ w+1 then 2^n else 2^w := hd
      by_cases hc : n ≤ w+1
      · rw [if_pos hc] at hd'
        refine ⟨1, 2^n, hd', PEqualNP.Outside.L_clb_119_aux.direct_gen n (w+1) hn h2 0 n
          (by omega) ?_ ?_⟩
        · intro i k hi _ hk
          interval_cases i
          · exact ⟨k, by omega, by rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]⟩
          · rcases Nat.eq_zero_or_pos k with hk0 | hk0
            · subst hk0
              exact ⟨n-1, by omega, by rw [show 1 + (n-1) = n by omega, Nat.mod_self]⟩
            · exact ⟨k-1, by omega, by rw [show 1 + (k-1) = k by omega, Nat.mod_eq_of_lt (by omega)]⟩
        · intro k hk hnot
          exact absurd ⟨Nat.zero_le _, by omega⟩ hnot
      · rw [if_neg hc] at hd'
        refine ⟨1, 2^w, hd', PEqualNP.Outside.L_clb_119_aux.direct_gen n (w+1) hn h2 1 w
          (by omega) ?_ ?_⟩
        · intro i k hi hk1 hk
          interval_cases i
          · exact ⟨k, by omega, by rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]⟩
          · exact ⟨k-1, by omega, by rw [show 1 + (k-1) = k by omega, Nat.mod_eq_of_lt (by omega)]⟩
        · intro k hk hnot
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0
            exact ⟨n-1, 1, by omega, by omega, by omega, by
              rw [show n - 1 + 1 = n by omega, Nat.mod_self]⟩
          · exact ⟨k, 0, by omega, hk, by omega, by rw [Nat.add_zero, Nat.mod_eq_of_lt hk]⟩
    · obtain ⟨M, hM, hE⟩ := PEqualNP.Outside.L_clb_119_aux.case845 n w hn h32 hnear
      exact ⟨n/2, M, le_trans hb hM, hE⟩
    · have hn' : 0 < a + b := by omega
      obtain ⟨code, base, left, right, hc, _, _, hpos, hsol⟩ :=
        PEqualNP.Outside.L_lib_743 a b h s q hn' hq hs hsh h1 h2'
      have hE : PEqualNP.Outside.L_clb_119_aux.Emb (a+b) (a+b-h) hn' a
          (q^2*(2^s-1)^(2*(q-1))*2^(a+b-(2*q*s+(h-s)))) :=
        ⟨code, base, left, right, hc, fun i => ⟨(hpos i).1, (hpos i).2.1⟩, hsol⟩
      have hL : a + b - h = w + 1 := by omega
      rw [hL] at hE
      rw [hab] at hM
      exact ⟨a, _, hM, PEqualNP.Outside.L_clb_119_aux.Emb_cast hab.symm hn hn' hE⟩
  obtain ⟨a, M, hHM, hE⟩ := hE
  have key := PEqualNP.Outside.L_clb_119_aux.from_emb n w p hn hp a M hE S R u v hR hv huv
    init update out herr
  exact le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hHM)) key

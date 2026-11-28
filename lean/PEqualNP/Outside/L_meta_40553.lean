import PEqualNP.Defs
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic

namespace PEqualNP.Outside.L_meta_40553

namespace Decode

universe u v w

structure Kit (S : Type u) (R : Type v) (A : Type w) [Monoid A] where
  Ext : S → S → Prop
  refl : ∀ s, Ext s s
  trans : ∀ {s s' s''}, Ext s s' → Ext s' s'' → Ext s s''
  cost : S → Nat
  peak : S → Nat
  weight : Nat
  Read : S → R → A → Nat → Prop
  persist : ∀ {s s' r a l}, Ext s s' → Read s r a l → Read s' r a l
  weaken : ∀ {s r a l l'}, Read s r a l → l ≤ l' → Read s r a l'
  emit : ∀ {s r r' a a' l}, Read s r a l → Read s r' a' l →
    ∃ s' t, Ext s s' ∧ cost s' ≤ cost s + weight ∧ peak s' ≤ max (peak s) (l+1) ∧
      Read s' t (a * a') (l+1)

variable {S : Type u} {R : Type v} {A : Type w} [Monoid A] [Inhabited R]

theorem Kit.batch {T : Type*} [Inhabited T] (K : Kit S R A) (s : S) (n c D : Nat) (P : S → Nat → T → Prop)
    (pm : ∀ {s₁ s₂ i r}, K.Ext s₁ s₂ → P s₁ i r → P s₂ i r)
    (step : ∀ s₁ i, K.Ext s s₁ → i < n →
      ∃ s₂ r, K.Ext s₁ s₂ ∧ K.cost s₂ ≤ K.cost s₁+c ∧
        K.peak s₂ ≤ max (K.peak s₁) D ∧ P s₂ i r) :
    ∃ (s' : S) (r : Nat → T), K.Ext s s' ∧ K.cost s' ≤ K.cost s+n*c ∧
      K.peak s' ≤ max (K.peak s) D ∧ ∀ i < n, P s' i (r i) := by
  induction n with
  | zero => exact ⟨s, fun _ => default, K.refl s, by simp, le_max_left .., by simp⟩
  | succ n ih =>
    obtain ⟨s₁, r₁, e₁, c₁, d₁, h₁⟩ := ih (fun s₁ i e hi => step s₁ i e (by omega))
    obtain ⟨s₂, r₂, e₂, c₂, d₂, h₂⟩ := step s₁ n e₁ (by omega)
    refine ⟨s₂, fun i => if i = n then r₂ else r₁ i, K.trans e₁ e₂, ?_, ?_, ?_⟩
    · rw [Nat.succ_mul]; omega
    · exact d₂.trans (max_le d₁ (le_max_right ..))
    · intro i hi
      by_cases e : i = n
      · subst i; simpa using h₂
      · simpa [e] using pm e₂ (h₁ i (by omega))

def prod (f : Nat → A) (start : Nat) : Nat → A
  | 0 => 1
  | n+1 => prod f start n * f (start+n)

@[simp] theorem prod_zero (f : Nat → A) (i : Nat) : prod f i 0 = 1 := rfl
@[simp] theorem prod_succ (f : Nat → A) (i n : Nat) :
    prod f i (n+1) = prod f i n * f (i+n) := rfl
@[simp] theorem prod_one (f : Nat → A) (i : Nat) : prod f i 1 = f i := by simp

theorem prod_split (f : Nat → A) (i a b : Nat) :
    prod f i (a+b) = prod f i a * prod f (i+a) b := by
  induction b with
  | zero => simp
  | succ b ih => rw [show a+(b+1)=a+b+1 by omega, prod_succ, ih, prod_succ, mul_assoc, Nat.add_assoc]

theorem prod_head (f : Nat → A) (i n : Nat) :
    prod f i (n+1) = f i * prod f (i+1) n := by
  rw [show n+1=1+n by omega, prod_split, prod_one]

theorem prod_congr (f g : Nat → A) (i n : Nat)
    (h : ∀ j, i ≤ j → j < i+n → f j = g j) : prod f i n = prod g i n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [prod_succ]
    rw [ih (fun j lo hi => h j lo (by omega)), h (i+n) (by omega) (by omega)]

variable (K : Kit S R A)

theorem Kit.balanced (s : S) (f : Nat → A) (r : Nat → R) (o e l : Nat)
    (hf : ∀ i < 2^e, K.Read s (r (o+i)) (f (o+i)) l) :
    ∃ s' t, K.Ext s s' ∧ K.cost s' ≤ K.cost s + (2^e-1)*K.weight ∧
      K.peak s' ≤ max (K.peak s) (l+e) ∧ K.Read s' t (prod f o (2^e)) (l+e) := by
  induction e generalizing s o with
  | zero => exact ⟨s, r o, K.refl s, by simp, le_max_left .., by simpa using hf 0 (by simp)⟩
  | succ e ih =>
    have hp : 2^e = 2^e-1+1 := by have := Nat.two_pow_pos e; omega
    have hpow : (2:Nat)^(e+1) = 2^e+2^e := by rw [Nat.pow_succ, Nat.mul_two]
    obtain ⟨s₁,t₁,E₁,C₁,D₁,V₁⟩ := ih s o (fun i hi => hf i (by omega))
    obtain ⟨s₂,t₂,E₂,C₂,D₂,V₂⟩ := ih s₁ (o+2^e) (fun i hi => by
      rw [Nat.add_assoc]; exact K.persist E₁ (hf (2^e+i) (by omega)))
    obtain ⟨s₃,t₃,E₃,C₃,D₃,V₃⟩ := K.emit (K.persist E₂ V₁) V₂
    rw [hpow, prod_split]
    refine ⟨s₃,t₃,K.trans E₁ (K.trans E₂ E₃),?_,?_,V₃⟩
    · have h : 2^e+2^e-1 = (2^e-1)+(2^e-1)+1 := by omega
      rw [h, Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
    · have hd : l+e ≤ l+(e+1) := by omega
      exact D₃.trans (max_le ((D₂.trans (max_le D₁ (le_max_right ..))).trans
        ((max_le (le_max_left ..) (hd.trans (le_max_right ..))))) (le_max_right ..))

theorem Kit.sweep (s : S) (f : Nat → A) (r : Nat → R) (o m l : Nat)
    (hf : ∀ i < m+1, K.Read s (r (o+i)) (f (o+i)) l) :
    ∃ (s' : S) (t : Nat → R), K.Ext s s' ∧ K.cost s' ≤ K.cost s + m*K.weight ∧
      K.peak s' ≤ max (K.peak s) (l+m) ∧
      ∀ i < m+1, K.Read s' (t i) (prod f o (i+1)) (l+i) := by
  induction m with
  | zero =>
    refine ⟨s, fun _ => r o, K.refl s, by simp, le_max_left .., ?_⟩
    intro i hi
    obtain rfl : i = 0 := by omega
    simpa using hf 0 (by omega)
  | succ m ih =>
    obtain ⟨s₁,t₁,E₁,C₁,D₁,V₁⟩ := ih (fun i hi => hf i (by omega))
    obtain ⟨s₂,t₂,E₂,C₂,D₂,V₂⟩ := K.emit (V₁ m (by omega))
      (K.weaken (K.persist E₁ (hf (m+1) (by omega))) (Nat.le_add_right l m))
    refine ⟨s₂,fun i => if i = m+1 then t₂ else t₁ i,K.trans E₁ E₂,?_,?_,?_⟩
    · rw [Nat.succ_mul]; omega
    · exact D₂.trans (max_le (D₁.trans (max_le (le_max_left ..) ((show _ ≤ _ by omega).trans (le_max_right ..)))) (le_max_right ..))
    · intro i hi
      by_cases he : i = m+1
      · subst i; simpa [← Nat.add_assoc] using V₂
      · simpa only [ite_eq_right he] using K.persist E₂ (V₁ i (by omega))

def window (f : Nat → A) (e i : Nat) : A :=
  prod f (i+1-2^e) (i+1-(i+1-2^e))

theorem window_next (f : Nat → A) (e i : Nat) :
    window f (e+1) i =
      if i < 2^e then window f e i else window f e (i-2^e) * window f e i := by
  have hp : (2:Nat)^(e+1) = 2^e+2^e := by rw [Nat.pow_succ, Nat.mul_two]
  split
  next h =>
    unfold window
    rw [hp, show i+1-(2^e+2^e) = 0 by omega, show i+1-2^e = 0 by omega]
  next h =>
    unfold window
    rw [hp]
    have H₀ : i-2^e+1-(2^e) = i+1-(2^e+2^e) := by omega
    have H₁ : i+1-(i+1-2^e) = 2^e := Nat.sub_sub_self ((Nat.le_of_not_gt h).trans (Nat.le_succ i))
    rw [H₀, H₁]
    have H₂ : i+1-(i+1-(2^e+2^e)) = (i-2^e+1-(i+1-(2^e+2^e))) + 2^e := by omega
    rw [H₂, prod_split]
    rw [show i+1-(2^e+2^e)+(i-2^e+1-(i+1-(2^e+2^e))) = i+1-2^e by omega]

theorem Kit.doubling (s : S) (f : Nat → A) (r : Nat → R) (n e l : Nat)
    (hf : ∀ i < n, K.Read s (r i) (f i) l) :
    ∃ (s' : S) (t : Nat → R), K.Ext s s' ∧ K.cost s' ≤ K.cost s + n*e*K.weight ∧
      K.peak s' ≤ max (K.peak s) (l+e) ∧
      ∀ i < n, K.Read s' (t i) (window f e i) (l+e) := by
  induction e with
  | zero =>
    refine ⟨s,r,K.refl s,by simp,le_max_left ..,?_⟩
    intro i hi
    simpa [window] using hf i hi
  | succ e ih =>
    obtain ⟨s₁,t₁,E₁,C₁,D₁,V₁⟩ := ih
    let P := fun s i t => K.Read s t (window f (e+1) i) (l+(e+1))
    obtain ⟨s₂,t₂,E₂,C₂,D₂,V₂⟩ := K.batch s₁ n K.weight (l+(e+1)) P
      (fun e h => K.persist e h) (by
        intro s₂ i e₁₂ hi
        have Vi := K.persist e₁₂ (V₁ i hi)
        by_cases H : i < 2^e
        · refine ⟨s₂,t₁ i,K.refl s₂,Nat.le_add_right ..,le_max_left ..,?_⟩
          simpa only [P, window_next, ite_eq_left H] using K.weaken Vi (show l+e ≤ l+(e+1) by omega)
        · have Vj := K.persist e₁₂ (V₁ (i-2^e) ((Nat.sub_le _ _).trans_lt hi))
          obtain ⟨s₃,t₃,E,C,D,V⟩ := K.emit Vj Vi
          refine ⟨s₃,t₃,E,C,D,?_⟩
          simpa only [P, window_next, ite_eq_right H, Nat.add_assoc] using V)
    refine ⟨s₂,t₂,K.trans E₁ E₂,?_,?_,V₂⟩
    · rw [Nat.mul_succ, Nat.add_mul]; omega
    · exact D₂.trans (max_le (D₁.trans (max_le (le_max_left ..) ((show _ ≤ _ by omega).trans (le_max_right ..)))) (le_max_right ..))

theorem prod_blocks (f : Nat → A) (b j : Nat) :
    prod (fun i => prod f (b*i) b) 0 j = prod f 0 (b*j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [prod_succ, ih, Nat.mul_succ, prod_split, Nat.zero_add, Nat.zero_add]

theorem Kit.scanPadded (s : S) (f : Nat → A) (r : Nat → R) (a b l : Nat)
    (ha : 2^a-1 ≤ a+b) (hb : b ≤ 2*2^a)
    (hf : ∀ i < 2^a*2^b, K.Read s (r i) (f i) l) :
    ∃ (s' : S) (t : Nat → R), K.Ext s s' ∧ K.cost s' ≤ K.cost s + 5*(2^a*2^b)*K.weight ∧
      K.peak s' ≤ max (K.peak s) (l+(a+b)+1) ∧
      ∀ i < 2^a*2^b, K.Read s' (t i) (prod f 0 (i+1)) (l+(a+b)+1) := by
  let B : Nat := 2^a
  let q : Nat := 2^b
  let fB := fun j => prod f (B*j) B
  have Bpos : 0 < B := Nat.two_pow_pos a
  have hidx : ∀ j < q, ∀ u < B, B*j+u < B*q := by
    intro j hj u hu
    calc
      B*j+u < B*(j+1) := by rw [Nat.mul_succ]; omega
      _ ≤ B*q := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨s₁,t₁,E₁,C₁,D₁,V₁⟩ := K.batch s q ((B-1)*K.weight) (l+a)
    (fun s j t => K.Read s t (fB j) (l+a))
    (fun e h => K.persist e h) (by
      intro s' j E hj
      exact K.balanced s' f r (B*j) a l (fun u hu => K.persist E (hf _ (hidx j hj u hu))))
  obtain ⟨s₂,t₂,E₂,C₂,D₂,V₂⟩ := K.doubling s₁ fB t₁ q b (l+a) V₁
  obtain ⟨s₃,t₃,E₃,C₃,D₃,V₃⟩ := K.batch (T := Nat → R) s₂ q ((B-1)*K.weight) (l+(B-1))
    (fun s j t => ∀ u < B, K.Read s (t u) (prod f (B*j) (u+1)) (l+u))
    (fun e h u hu => K.persist e (h u hu)) (by
      intro s' j E hj
      have h : B-1+1 = B := by omega
      have hs := K.sweep s' f r (B*j) (B-1) l (fun u hu =>
        K.persist (K.trans E₁ (K.trans E₂ E)) (hf _ (hidx j hj u (by omega))))
      simpa only [h] using hs)
  obtain ⟨s₄,t₄,E₄,C₄,D₄,V₄⟩ := K.batch s₃ (B*q) K.weight (l+(a+b)+1)
    (fun s i t => K.Read s t (prod f 0 (i+1)) (l+(a+b)+1))
    (fun e h => K.persist e h) (by
      intro s' i E hi
      let j := i/B
      let u := i%B
      have hj : j < 2^b := (Nat.div_lt_iff_lt_mul Bpos).2 (by simpa [Nat.mul_comm] using hi)
      have hu : u < B := Nat.mod_lt _ Bpos
      have hju : B*j+u = i := by
        simpa only [j, u, Nat.add_comm] using (Nat.mod_add_div i B)
      have U := K.weaken (K.persist E (V₃ j hj u hu)) (show l+u ≤ l+(a+b) by omega)
      by_cases J : j = 0
      · refine ⟨s',t₃ j u,K.refl s',Nat.le_add_right ..,le_max_left ..,?_⟩
        have h : B*j = 0 := by rw [J, Nat.mul_zero]
        have ui : u = i := by omega
        simpa only [h, ui] using K.weaken U (Nat.le_add_right ..)
      · have jp : 0 < j := Nat.pos_of_ne_zero J
        have W := K.persist (K.trans E₃ E) (V₂ (j-1) ((Nat.sub_le _ _).trans_lt hj))
        have hW : window fB b (j-1) = prod f 0 (B*j) := by
          unfold window
          rw [show j-1+1=j by omega, Nat.sub_eq_zero_of_le (Nat.le_of_lt hj), Nat.sub_zero, prod_blocks]
        rw [hW, Nat.add_assoc] at W
        obtain ⟨s'',t,E',C,D,V⟩ := K.emit W U
        have hP : prod f 0 (B*j) * prod f (B*j) (u+1) = prod f 0 (i+1) := by
          have hs := (prod_split f 0 (B*j) (u+1)).symm
          rw [Nat.zero_add, ← Nat.add_assoc, hju] at hs
          exact hs
        rw [hP] at V
        exact ⟨s'',t,E',C,D,V⟩)
  refine ⟨s₄,t₄,K.trans E₁ (K.trans E₂ (K.trans E₃ E₄)),?_,?_,V₄⟩
  · have hBudget : q*(B-1)+q*b+q*(B-1)+B*q ≤ 5*(B*q) := by
      have hh : (B-1)+b+(B-1)+B ≤ 5*B := by omega
      have hi := Nat.mul_le_mul_left q hh
      simp only [Nat.mul_add, ← Nat.mul_assoc] at hi
      simpa only [Nat.mul_comm q B, Nat.mul_comm q 5, Nat.mul_assoc, Nat.mul_comm q B] using hi
    have hh := Nat.mul_le_mul_right K.weight hBudget
    change _ ≤ _ + 5*(B*q)*K.weight
    simp only [Nat.add_mul, Nat.mul_assoc] at hh C₁ C₂ C₃ C₄ ⊢
    omega
  · have d₁ : l+a ≤ l+(a+b)+1 := by omega
    have d₂ : l+a+b ≤ l+(a+b)+1 := by omega
    have d₃ : l+(B-1) ≤ l+(a+b)+1 := by omega
    exact D₄.trans (max_le (D₃.trans (max_le (D₂.trans (max_le
      (D₁.trans (max_le (le_max_left ..) (d₁.trans (le_max_right ..))))
      (d₂.trans (le_max_right ..)))) (d₃.trans (le_max_right ..)))) (le_max_right ..))

theorem pad_lt_twice (m : Nat) (hm : 0 < m) : 2 ^ Nat.clog 2 m < 2*m := by
  by_cases h : m ≤ 1
  · have hm' : m = 1 := by omega
    subst m
    simp
  · let L := Nat.clog 2 m
    have hL : 0 < L := Nat.clog_pos (by decide) (by omega)
    have hm' : 2^(L-1) < m := (Nat.lt_clog_iff_pow_lt (by decide)).1 (by omega)
    calc
      2 ^ L = 2 ^ ((L-1)+1) := by rw [show L-1+1=L by omega]
      _ = 2 ^ (L-1)*2 := Nat.pow_succ 2 (L-1)
      _ < 2*m := by omega

theorem Kit.scan (s : S) (f : Nat → A) (r : Nat → R) (one : R) (m l : Nat)
    (hone : K.Read s one 1 l) (hf : ∀ i < m, K.Read s (r i) (f i) l) :
    ∃ (s' : S) (t : Nat → R), K.Ext s s' ∧ K.cost s' ≤ K.cost s + 5*2^(Nat.clog 2 m)*K.weight ∧
      K.peak s' ≤ max (K.peak s) (l+Nat.clog 2 m+1) ∧
      ∀ i < m, K.Read s' (t i) (prod f 0 (i+1)) (l+Nat.clog 2 m+1) := by
  let L := Nat.clog 2 m
  let a := Nat.log 2 L
  let b := L-a
  have e : a+b = L := Nat.add_sub_of_le (Nat.log_le_self _ _)
  have ha : 2^a-1 ≤ a+b := by rw [e]; exact Nat.sub_le_iff_le_add.2 (Nat.pow_log_le_add_one _ _)
  have hb : b ≤ 2*2^a := by
    have hb' := Nat.lt_pow_succ_log_self (show 1 < 2 by decide) L
    rw [show (Nat.log 2 L).succ = a+1 by rfl, Nat.pow_succ] at hb'
    omega
  let f' := fun i => if i<m then f i else 1
  let r' := fun i => if i<m then r i else one
  obtain ⟨s',t,E,C,D,V⟩ := K.scanPadded s f' r' a b l ha hb (by
    intro i hi
    by_cases h : i < m
    · simpa [f',r',h] using hf i h
    · simpa [f',r',h] using hone)
  have e' : 2^a*2^b = 2^L := by rw [← Nat.pow_add, e]
  rw [e'] at C
  rw [e] at D
  rw [e, e'] at V
  refine ⟨s',t,E,C,D,?_⟩
  intro i hi
  have v := V i (hi.trans_le (Nat.le_pow_clog (by decide) _))
  rw [prod_congr f' f 0 (i+1) (by intro j hj hj'; simp [f', show j < m by omega])] at v
  exact v

def Kit.op : Kit S R Aᵐᵒᵖ where
  Ext := K.Ext
  refl := K.refl
  trans := K.trans
  cost := K.cost
  peak := K.peak
  weight := K.weight
  Read := fun s r a l => K.Read s r a.unop l
  persist := K.persist
  weaken := K.weaken
  emit := fun r r' => K.emit r' r

theorem reverse_prod (f : Nat → A) (m k : Nat) (hk : k ≤ m) :
    prod (fun i => MulOpposite.op (f (m-1-i))) 0 k = MulOpposite.op (prod f (m-k) k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [prod_succ, ih (by omega), Nat.zero_add, prod_head]
    simp only [← MulOpposite.op_mul]
    rw [show m-1-k=m-(k+1) by omega, show m-(k+1)+1=m-k by omega]

theorem Kit.suffix (s : S) (f : Nat → A) (r : Nat → R) (one : R) (m l : Nat)
    (hone : K.Read s one 1 l) (hf : ∀ i < m, K.Read s (r i) (f i) l) :
    ∃ (s' : S) (t : Nat → R), K.Ext s s' ∧ K.cost s' ≤ K.cost s + 5*2^(Nat.clog 2 m)*K.weight ∧
      K.peak s' ≤ max (K.peak s) (l+Nat.clog 2 m+1) ∧
      ∀ i < m, K.Read s' (t i) (prod f i (m-i)) (l+Nat.clog 2 m+1) := by
  obtain ⟨s',t,E,C,D,V⟩ := K.op.scan s (fun i => MulOpposite.op (f (m-1-i)))
    (fun i => r (m-1-i)) one m l hone (by intro i hi; exact hf _ (by omega))
  refine ⟨s',fun i => t (m-1-i),E,C,D,?_⟩
  intro i hi
  have v := V (m-1-i) (by omega)
  rw [reverse_prod _ _ _ (by omega), show m-1-i+1=m-i by omega, show m-(m-i)=i by omega] at v
  exact v

theorem Kit.suffixBatch (s : S) (q m l : Nat) (len : Nat → Nat)
    (f : Nat → Nat → A) (r : Nat → Nat → R) (one : R)
    (hle : ∀ j < q, len j ≤ m) (hone : K.Read s one 1 l)
    (hf : ∀ j < q, ∀ i < len j, K.Read s (r j i) (f j i) l) :
    ∃ (s' : S) (t : Nat → Nat → R), K.Ext s s' ∧ K.cost s' ≤ K.cost s + q*(5*2^(Nat.clog 2 m)*K.weight) ∧
      K.peak s' ≤ max (K.peak s) (l+Nat.clog 2 m+1) ∧
      ∀ j < q, ∀ i < len j, K.Read s' (t j i) (prod (f j) i (len j-i)) (l+Nat.clog 2 m+1) := by
  apply K.batch (T := Nat → R) s q _ _ (fun s j t => ∀ i < len j,
    K.Read s (t i) (prod (f j) i (len j-i)) (l+Nat.clog 2 m+1))
  · intro s₁ s₂ j t e h i hi
    exact K.persist e (h i hi)
  · intro s₁ j e hj
    have hc := Nat.clog_mono_right 2 (hle j hj)
    obtain ⟨s₂,t,E,C,D,V⟩ := K.suffix s₁ (f j) (r j) one (len j) l
      (K.persist e hone) (fun i hi => K.persist e (hf j hj i hi))
    have hC : 2 ^ Nat.clog 2 (len j) ≤ 2 ^ Nat.clog 2 m := Nat.pow_le_pow_right (by decide) hc
    have hD : l+Nat.clog 2 (len j)+1 ≤ l+Nat.clog 2 m+1 := by omega
    exact ⟨s₂,t,E,C.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hC)) _),
      D.trans (max_le (le_max_left ..) (hD.trans (le_max_right ..))),
      fun i hi => K.weaken (V i hi) hD⟩

end Decode

namespace Decode

structure Aff where
  a : Bool
  b : Bool

def Aff.at (f : Aff) (t : Bool) : Bool := xor (f.a && t) f.b

def Aff.mul (f g : Aff) : Aff := ⟨f.a && g.a, xor (f.a && g.b) f.b⟩

instance : Monoid Aff where
  one := ⟨true, false⟩
  mul := Aff.mul
  one_mul f := by rcases f with ⟨x,y⟩; cases x <;> cases y <;> rfl
  mul_one f := by rcases f with ⟨x,y⟩; cases x <;> cases y <;> rfl
  mul_assoc f g h := by
    rcases f with ⟨a,b⟩; rcases g with ⟨c,d⟩; rcases h with ⟨e,f⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

theorem Aff.mul_at (f g : Aff) (t : Bool) : (f*g).at t = f.at (g.at t) := by
  rcases f with ⟨a,b⟩; rcases g with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases t <;> rfl

@[simp] theorem Aff.one_at (t : Bool) : (1 : Aff).at t = t := by cases t <;> rfl

structure BitKit (S : Type*) (R : Type*) (X : Type*) where
  Ext : S → S → Prop
  refl : ∀ s, Ext s s
  trans : ∀ {s s' s''}, Ext s s' → Ext s' s'' → Ext s s''
  cost : S → Nat
  peak : S → Nat
  Read : S → R → (X → Bool) → Nat → Prop
  persist : ∀ {s s' r a l}, Ext s s' → Read s r a l → Read s' r a l
  weaken : ∀ {s r a l l'}, Read s r a l → l ≤ l' → Read s r a l'
  andGate : ∀ {s r r' a a' l}, Read s r a l → Read s r' a' l →
    ∃ s' t, Ext s s' ∧ cost s' ≤ cost s + 1 ∧ peak s' ≤ max (peak s) (l+1) ∧
      Read s' t (fun x => a x && a' x) (l+1)
  xorGate : ∀ {s r r' a a' l}, Read s r a l → Read s r' a' l →
    ∃ s' t, Ext s s' ∧ cost s' ≤ cost s ∧ peak s' ≤ max (peak s) l ∧
      Read s' t (fun x => xor (a x) (a' x)) l

variable {S R X : Type*} (K : BitKit S R X)

def BitKit.aff : Kit S (R×R) (X → Aff) where
  Ext := K.Ext
  refl := K.refl
  trans := K.trans
  cost := K.cost
  peak := K.peak
  weight := 2
  Read s r f l := K.Read s r.1 (fun x => (f x).a) l ∧ K.Read s r.2 (fun x => (f x).b) l
  persist e h := ⟨K.persist e h.1, K.persist e h.2⟩
  weaken h e := ⟨K.weaken h.1 e, K.weaken h.2 e⟩
  emit := by
    rintro s r r' a a' l ⟨Va,Vb⟩ ⟨Va',Vb'⟩
    obtain ⟨s₁,t₁,E₁,C₁,D₁,V₁⟩ := K.andGate Va Va'
    obtain ⟨s₂,t₂,E₂,C₂,D₂,V₂⟩ := K.andGate (K.persist E₁ Va) (K.persist E₁ Vb')
    obtain ⟨s₃,t₃,E₃,C₃,D₃,V₃⟩ := K.xorGate V₂
      (K.weaken (K.persist (K.trans E₁ E₂) Vb) (Nat.le_succ l))
    exact ⟨s₃,(t₁,t₃),K.trans E₁ (K.trans E₂ E₃),by omega,
      D₃.trans (max_le (D₂.trans (max_le D₁ (le_max_right ..))) (le_max_right ..)),
      K.persist (K.trans E₂ E₃) V₁,V₃⟩

theorem BitKit.applyAff {s : S} {r : R×R} {u : R} {f : X → Aff} {v : X → Bool} {l : Nat}
    (hf : K.aff.Read s r f l) (hv : K.Read s u v l) :
    ∃ s' t, K.Ext s s' ∧ K.cost s' ≤ K.cost s+1 ∧ K.peak s' ≤ max (K.peak s) (l+1) ∧
      K.Read s' t (fun x => (f x).at (v x)) (l+1) := by
  obtain ⟨s₁,t₁,E₁,C₁,D₁,V₁⟩ := K.andGate hf.1 hv
  obtain ⟨s₂,t₂,E₂,C₂,D₂,V₂⟩ := K.xorGate V₁
    (K.weaken (K.persist E₁ hf.2) (Nat.le_succ l))
  exact ⟨s₂,t₂,K.trans E₁ E₂,C₂.trans C₁,D₂.trans (max_le D₁ (le_max_right ..)),V₂⟩

theorem eval_prod (f : Nat → X → Aff) (bit : Nat → X → Bool) (x : X) (i k : Nat)
    (rec : ∀ j, i ≤ j → j < i+k → (f j x).at (bit (j+1) x) = bit j x) :
    (prod f i k x).at (bit (i+k) x) = bit i x := by
  induction k with
  | zero => exact Aff.one_at _
  | succ k ih =>
    rw [prod_succ]
    change ((prod f i k x)*(f (i+k) x)).at (bit (i+(k+1)) x) = bit i x
    rw [Aff.mul_at, ← Nat.add_assoc, rec (i+k) (by omega) (by omega)]
    exact ih (fun j a b => rec j a (by omega))

variable [Inhabited R]

theorem BitKit.decodeBatch (s : S) (q m l : Nat) (len : Nat → Nat)
    (f : Nat → Nat → X → Aff) (bit : Nat → Nat → X → Bool)
    (r : Nat → Nat → R×R) (one : R×R) (seed : Nat → R)
    (hle : ∀ j < q, len j ≤ m) (hone : K.aff.Read s one 1 l)
    (hf : ∀ j < q, ∀ i < len j, K.aff.Read s (r j i) (f j i) l)
    (hs : ∀ j < q, K.Read s (seed j) (bit j (len j)) l)
    (rec : ∀ j < q, ∀ i < len j, ∀ x, (f j i x).at (bit j (i+1) x) = bit j i x) :
    ∃ (s' : S) (t : Nat → Nat → R), K.Ext s s' ∧
      K.cost s' ≤ K.cost s + q*(5*2^(Nat.clog 2 m)*2) + q*m ∧
      K.peak s' ≤ max (K.peak s) (l+Nat.clog 2 m+2) ∧
      ∀ j < q, ∀ i < len j, K.Read s' (t j i) (bit j i) (l+Nat.clog 2 m+2) := by
  obtain ⟨s₁,t₁,E₁,C₁,D₁,V₁⟩ := K.aff.suffixBatch s q m l len f r one hle hone hf
  let d := l+Nat.clog 2 m+1
  obtain ⟨s₂,t₂,E₂,C₂,D₂,V₂⟩ := K.aff.batch (T := Nat → R) s₁ q m (d+1)
    (fun s j t => ∀ i < len j, K.Read s (t i) (bit j i) (d+1))
    (fun e h i hi => K.persist e (h i hi)) (by
      intro s' j E hj
      obtain ⟨s'',t,E',C',D',V'⟩ := K.aff.batch (T := R) s' (len j) 1 (d+1)
        (fun s i t => K.Read s t (bit j i) (d+1))
        (fun e h => K.persist e h) (by
          intro s'' i E' hi
          have v₁ := K.aff.persist (K.trans E E') (V₁ j hj i hi)
          have v₂ := K.weaken (K.persist (K.trans E₁ (K.trans E E')) (hs j hj))
            (show l ≤ d by dsimp [d]; omega)
          obtain ⟨s''',t,E'',C'',D'',V''⟩ := K.applyAff v₁ v₂
          have eq : (fun x => (prod (f j) i (len j-i) x).at (bit j (len j) x)) = bit j i := by
            funext x
            have h := eval_prod (f j) (bit j) x i (len j-i)
              (fun k h₀ h₁ => rec j hj k (by omega) x)
            rwa [show i+(len j-i)=len j by omega] at h
          rw [eq] at V''
          exact ⟨s''',t,E'',C'',D'',V''⟩)
      exact ⟨s'',t,E',C'.trans (Nat.add_le_add_left (by simpa only [Nat.mul_one] using hle j hj) _),D',V'⟩)
  refine ⟨s₂,t₂,K.trans E₁ E₂,?_,?_,V₂⟩
  · change K.cost s₁ ≤ K.cost s + q*(5*2^(Nat.clog 2 m)*2) at C₁
    change K.cost s₂ ≤ K.cost s₁ + q*m at C₂
    omega
  · exact D₂.trans (max_le (D₁.trans (max_le (le_max_left ..)
      ((show d ≤ d+1 by omega).trans (le_max_right ..)))) (le_max_right ..))

def chi (x : Nat → Bool) (i : Nat) : Bool := xor (x i) (!(x (i+1)) && x (i+2))

def stripMap (h : Nat) (x : Nat → Bool) (i : Nat) : Aff :=
  ⟨!(if i+1 < h then chi x (i+1) else x h), chi x i⟩

theorem stripMap_step (h : Nat) (x : Nat → Bool) (i : Nat) (hi : i<h) :
    (stripMap h x i).at (x (i+2)) = x i := by
  by_cases H : i+1 < h
  · simp only [stripMap, Aff.at, ite_eq_left H, chi]
    cases x i <;> cases x (i+1) <;> cases x (i+2) <;> cases x (i+3) <;> rfl
  · have e : h = i+1 := by omega
    simp only [stripMap, Aff.at, ite_eq_right H, chi]
    rw [e]
    cases x i <;> cases x (i+1) <;> cases x (i+2) <;> rfl

def laneLen (h a : Nat) : Nat := (h+1-a)/2

theorem laneLen_lt (h a i : Nat) (ha : a<2) (hi : i<laneLen h a) : 2*i+a < h := by
  unfold laneLen at hi
  omega

theorem laneLen_le (h a : Nat) : laneLen h a ≤ (h+1)/2 := by
  unfold laneLen
  omega

theorem laneLen_end (h a : Nat) (ha : a<2) (hh : 2 ≤ h) :
    2*laneLen h a+a = h ∨ 2*laneLen h a+a = h+1 := by
  unfold laneLen
  omega

theorem laneLen_covers (h i : Nat) (hi : i<h) :
    i%2 < 2 ∧ i/2 < laneLen h (i%2) ∧ 2*(i/2)+i%2 = i := by
  unfold laneLen
  omega

theorem laneMap_step (h a : Nat) (x : Nat → Bool) (ha : a<2) {i : Nat} (hi : i<laneLen h a) :
    (stripMap h x (2*i+a)).at (x (2*(i+1)+a)) = x (2*i+a) := by
  rw [show 2*(i+1)+a = (2*i+a)+2 by omega]
  exact stripMap_step h x _ (laneLen_lt h a i ha hi)

end Decode

namespace Decode

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) && xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
    (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

def levelStep (ds : List Nat) (g : Gate) : List Nat :=
  ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat]

def levels (w : Nat) (C : Circuit) : List Nat := C.gates.foldl levelStep (List.replicate w 0)

def peak (w : Nat) (C : Circuit) : Nat := (levels w C).foldr max 0

structure Build (w : Nat) where
  gates : List Gate
  back : ReadsBack w ⟨gates,0⟩
  fan : ∀ g ∈ gates, g.inputs.length ≤ 2

namespace Build

variable {w : Nat} {X : Type*}

def circ (s : Build w) : Circuit := ⟨s.gates,0⟩
def empty (w : Nat) : Build w := ⟨[], by simp [ReadsBack], by simp⟩
def size (s : Build w) : Nat := w+s.gates.length
def cost (s : Build w) : Nat := s.gates.countP nonlinear
def depth (s : Build w) : Nat := peak w s.circ
def level (s : Build w) (i : Nat) : Nat := (levels w s.circ).getD i 0
def Ext (s s' : Build w) : Prop := s.gates <+: s'.gates

def Read (input : X → List Bool) (s : Build w) (r : Nat) (f : X → Bool) (l : Nat) : Prop :=
  r < s.size ∧ (∀ x, (s.circ.wires (input x)).getD r false = f x) ∧ s.level r ≤ l

theorem getD_append_left {α : Type*} {xs ys : List α} {i : Nat} (h : i < xs.length) (d : α) :
    (xs++ys).getD i d = xs.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc {α : Type*} (xs : List α) (v d : α) : (xs++[v]).getD xs.length d = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]

theorem Ext.getD {α : Type*} {xs ys : List α} (h : xs <+: ys) {i : Nat} (hi : i < xs.length) (d : α) :
    ys.getD i d = xs.getD i d := by
  obtain ⟨zs,rfl⟩ := h
  exact getD_append_left hi d

private theorem foldlen {α β : Type*} (step : List α → β → List α) (gates : List β) (x : List α)
    (hlen : ∀ l g, (step l g).length = l.length+1) :
    (gates.foldl step x).length = x.length+gates.length := by
  induction gates generalizing x with
  | nil => simp
  | cons g gs ih => simp only [List.length_cons, List.foldl_cons, ih, hlen]; omega

theorem wires_len (s : Build w) (x : List Bool) : (s.circ.wires x).length = x.length+s.gates.length :=
  foldlen _ _ _ (by simp)

theorem levels_len (s : Build w) : (levels w s.circ).length = s.size := by
  unfold levels size
  rw [foldlen (hlen := by simp [levelStep]), List.length_replicate]
  rfl

private theorem foldPrefix {α β : Type*} (step : List α → β → List α) (gates : List β) (x : List α)
    (hp : ∀ l g, l <+: step l g) : x <+: gates.foldl step x := by
  induction gates generalizing x with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih => exact (hp x g).trans (ih (step x g))

theorem wires_prefix {s s' : Build w} (h : Ext s s') (x : List Bool) :
    s.circ.wires x <+: s'.circ.wires x := by
  obtain ⟨gs,hgs⟩ := h
  unfold Circuit.wires circ
  dsimp
  rw [← hgs, List.foldl_append]
  exact foldPrefix _ _ _ (fun _ _ => List.prefix_append ..)

theorem levels_prefix {s s' : Build w} (h : Ext s s') :
    levels w s.circ <+: levels w s'.circ := by
  obtain ⟨gs,hgs⟩ := h
  unfold levels circ
  dsimp
  rw [← hgs, List.foldl_append]
  exact foldPrefix _ _ _ (fun _ _ => List.prefix_append ..)

theorem read_persist {input : X → List Bool} (hinput : ∀ x, (input x).length = w)
    {s s' : Build w} {r f l} (E : Ext s s') (V : Read input s r f l) : Read input s' r f l := by
  refine ⟨V.1.trans_le (Nat.add_le_add_left E.length_le _), ?_, ?_⟩
  · intro x
    rw [Ext.getD (wires_prefix E _) (by rw [wires_len, hinput]; exact V.1)]
    exact V.2.1 x
  · unfold level
    rw [Ext.getD (levels_prefix E) (by rw [levels_len]; exact V.1)]
    exact V.2.2

theorem read_weaken {input : X → List Bool} {s : Build w} {r f l l'}
    (V : Read input s r f l) (h : l ≤ l') : Read input s r f l' := ⟨V.1,V.2.1,V.2.2.trans h⟩

theorem read_input {input : X → List Bool} (hinput : ∀ x, (input x).length = w)
    (s : Build w) (i : Nat) (hi : i < w) :
    Read input s i (fun x => (input x).getD i false) 0 := by
  have E : Ext (empty w) s := List.nil_prefix
  apply read_persist hinput E
  refine ⟨by simpa [size,empty] using hi, fun _ => rfl, ?_⟩
  simp [level, levels, circ, empty, List.getD_eq_getElem?_getD]

@[simp] theorem empty_cost (w : Nat) : (empty w).cost = 0 := rfl
@[simp] theorem empty_depth (w : Nat) : (empty w).depth = 0 := by
  change (List.replicate w 0).foldr max 0 = 0
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, ih]

def push (s : Build w) (g : Gate) (fan : g.inputs.length ≤ 2)
    (back : ∀ i ∈ g.inputs, i < s.size) : Build w := by
  refine ⟨s.gates++[g],?_,?_⟩
  · intro j hj i hi
    change j < (s.gates++[g]).length at hj
    change i ∈ ((s.gates++[g]).getD j _).inputs at hi
    by_cases h : j < s.gates.length
    · rw [getD_append_left h] at hi
      exact s.back j h i hi
    · have h' : j = s.gates.length := by simp at hj; omega
      subst j
      rw [getD_snoc] at hi
      exact back i hi
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact s.fan _ h
    · obtain rfl : g' = g := by simpa using h
      exact fan

def localMax (s : Build w) (g : Gate) : Nat := (g.inputs.map s.level).foldr max 0

theorem localMax_le (s : Build w) (g : Gate) (l : Nat)
    (ht : ∀ i ∈ g.inputs, s.level i ≤ l) : localMax s g ≤ l := by
  unfold localMax
  generalize g.inputs = L at ht ⊢
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.foldr_cons, max_le_iff]
    constructor
    · exact ht _ List.mem_cons_self
    · exact ih (fun j hj => ht j (List.mem_cons_of_mem _ hj))

private theorem foldr_max_snoc (L : List Nat) (d : Nat) :
    (L++[d]).foldr max 0 = max (L.foldr max 0) d := by
  induction L with
  | nil => simp
  | cons n L ih => simp [ih, max_assoc]

theorem push_spec (input : X → List Bool) (hinput : ∀ x, (input x).length = w)
    (s : Build w) (g : Gate) (fan : g.inputs.length ≤ 2) (back : ∀ i ∈ g.inputs, i < s.size) :
    let s' := s.push g fan back
    let d := localMax s g + (nonlinear g).toNat
    Ext s s' ∧ s'.cost = s.cost+(nonlinear g).toNat ∧ s'.depth = max s.depth d ∧
      Read input s' s.size (fun x => g.op.eval (g.inputs.map (fun i => (s.circ.wires (input x)).getD i false))) d := by
  dsimp
  refine ⟨List.prefix_append .., ?_, ?_, ?_⟩
  · cases H : nonlinear g <;> simp [cost, push, List.countP_append, H]
  · unfold depth peak levels circ push
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact foldr_max_snoc ..
  · refine ⟨by simp [size, push],?_,?_⟩
    · intro x
      have hl : (s.circ.wires (input x)).length = s.size := by rw [wires_len, hinput]; rfl
      unfold Circuit.wires circ push
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((s.circ.wires (input x)) ++ [_]).getD s.size false = _
      rw [← hl, getD_snoc]
    · have hl := levels_len s
      unfold level levels circ push
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((levels w s.circ)++[localMax s g+(nonlinear g).toNat]).getD s.size 0 ≤ _
      rw [← hl, getD_snoc]

theorem emit (input : X → List Bool) (hinput : ∀ x, (input x).length = w)
    (s : Build w) (g : Gate) (fan : g.inputs.length ≤ 2) (back : ∀ i ∈ g.inputs, i < s.size)
    (l : Nat) (lev : ∀ i ∈ g.inputs, s.level i ≤ l) (f : X → Bool)
    (sem : ∀ x, g.op.eval (g.inputs.map (fun i => (s.circ.wires (input x)).getD i false)) = f x) :
    ∃ s' t, Ext s s' ∧ s'.cost = s.cost+(nonlinear g).toNat ∧
      s'.depth ≤ max s.depth (l+(nonlinear g).toNat) ∧ Read input s' t f (l+(nonlinear g).toNat) := by
  obtain ⟨E,C,D,V⟩ := push_spec input hinput s g fan back
  have hl := Nat.add_le_add_right (localMax_le s g l lev) (nonlinear g).toNat
  refine ⟨s.push g fan back,s.size,E,C,?_,?_⟩
  · rw [D]
    exact max_le (le_max_left ..) (hl.trans (le_max_right ..))
  · exact ⟨V.1,fun x => (V.2.1 x).trans (sem x),V.2.2.trans hl⟩

@[simp] theorem nonlinear_and (i j : Nat) : nonlinear ⟨.and,[i,j]⟩ = true := rfl
@[simp] theorem nonlinear_or (i j : Nat) : nonlinear ⟨.or,[i,j]⟩ = true := rfl
@[simp] theorem nonlinear_mod2 (i j : Nat) : nonlinear ⟨.mod 2,[i,j]⟩ = false := rfl
@[simp] theorem nonlinear_unary (op : GateOp) (i : Nat) : nonlinear ⟨op,[i]⟩ = false := rfl
@[simp] theorem nonlinear_nullary (op : GateOp) : nonlinear ⟨op,[]⟩ = false := rfl

section
variable {input : X → List Bool} (hinput : ∀ x, (input x).length = w)
include hinput

theorem emit0 (s : Build w) (op : GateOp) :
    ∃ s' t, Ext s s' ∧ s'.cost = s.cost ∧ s'.depth = s.depth ∧
      Read input s' t (fun _ => op.eval []) 0 := by
  let g : Gate := ⟨op,[]⟩
  have fan : g.inputs.length ≤ 2 := by simp [g]
  have back : ∀ i ∈ g.inputs, i < s.size := by simp [g]
  obtain ⟨E,C,D,V⟩ := push_spec input hinput s g fan back
  refine ⟨s.push g fan back,s.size,E,?_,?_,?_⟩
  · simpa [g] using C
  · simpa [g, localMax] using D
  · simpa [g, localMax] using V

theorem emitConst (s : Build w) (b : Bool) :
    ∃ s' t, Ext s s' ∧ s'.cost = s.cost ∧ s'.depth = s.depth ∧
      Read input s' t (fun _ => b) 0 := by
  cases b
  · exact emit0 hinput s .or
  · exact emit0 hinput s .and

theorem emit1 (op : GateOp) {s : Build w} {i f l} (V : Read input s i f l) :
    ∃ s' t, Ext s s' ∧ s'.cost = s.cost ∧ s'.depth ≤ max s.depth l ∧
      Read input s' t (fun x => op.eval [f x]) l := by
  have M := emit input hinput s ⟨op,[i]⟩ (by simp)
    (by intro j hj; simp at hj; subst j; exact V.1)
    l (by intro j hj; simp at hj; subst j; exact V.2.2)
    (fun x => op.eval [f x]) (by intro x; simp only [List.map_cons, List.map_nil, V.2.1 x])
  simpa using M

theorem emit2 (op : GateOp) {s : Build w} {i j f g l}
    (V : Read input s i f l) (W : Read input s j g l) :
    let a := (nonlinear ⟨op,[i,j]⟩).toNat
    ∃ s' t, Ext s s' ∧ s'.cost = s.cost+a ∧ s'.depth ≤ max s.depth (l+a) ∧
      Read input s' t (fun x => op.eval [f x,g x]) (l+a) := by
  exact emit input hinput s ⟨op,[i,j]⟩ (by simp)
    (by intro k hk; simp at hk; rcases hk with rfl | rfl; exact V.1; exact W.1)
    l (by intro k hk; simp at hk; rcases hk with rfl | rfl; exact V.2.2; exact W.2.2)
    (fun x => op.eval [f x,g x]) (by intro x; simp only [List.map_cons, List.map_nil,V.2.1 x,W.2.1 x])

theorem emitNot {s : Build w} {i f l} (V : Read input s i f l) :
    ∃ s' t, Ext s s' ∧ s'.cost = s.cost ∧ s'.depth ≤ max s.depth l ∧
      Read input s' t (fun x => !(f x)) l := emit1 hinput .not V

theorem emitAnd {s : Build w} {i j f g l} (V : Read input s i f l) (W : Read input s j g l) :
    ∃ s' t, Ext s s' ∧ s'.cost = s.cost+1 ∧ s'.depth ≤ max s.depth (l+1) ∧
      Read input s' t (fun x => f x && g x) (l+1) := by
  have eq (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
  simpa only [nonlinear_and, Bool.toNat_true, eq] using emit2 hinput .and V W

theorem emitOr {s : Build w} {i j f g l} (V : Read input s i f l) (W : Read input s j g l) :
    ∃ s' t, Ext s s' ∧ s'.cost = s.cost+1 ∧ s'.depth ≤ max s.depth (l+1) ∧
      Read input s' t (fun x => f x || g x) (l+1) := by
  have eq (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
  simpa only [nonlinear_or, Bool.toNat_true, eq] using emit2 hinput .or V W

theorem emitXor {s : Build w} {i j f g l} (V : Read input s i f l) (W : Read input s j g l) :
    ∃ s' t, Ext s s' ∧ s'.cost = s.cost ∧ s'.depth ≤ max s.depth l ∧
      Read input s' t (fun x => xor (f x) (g x)) l := by
  have eq (a b : Bool) : (!(GateOp.eval (.mod 2) [a,b])) = xor a b := by cases a <;> cases b <;> rfl
  obtain ⟨s₁,t₁,E₁,C₁,D₁,V₁⟩ := emit2 hinput (.mod 2) V W
  simp only [nonlinear_mod2, Bool.toNat_false, Nat.add_zero] at C₁ D₁ V₁
  obtain ⟨s₂,t₂,E₂,C₂,D₂,V₂⟩ := emitNot hinput V₁
  exact ⟨s₂,t₂,E₁.trans E₂,C₂.trans C₁,D₂.trans (max_le D₁ (le_max_right ..)),
    V₂.1,fun x => (V₂.2.1 x).trans (eq _ _),V₂.2.2⟩

end

def bitKit (input : X → List Bool) (hinput : ∀ x, (input x).length = w) : BitKit (Build w) Nat X where
  Ext := Ext
  refl := fun _ => ⟨[], by simp⟩
  trans := List.IsPrefix.trans
  cost := cost
  peak := depth
  Read := Read input
  persist := read_persist hinput
  weaken := read_weaken
  andGate := fun V W => by
    obtain ⟨s,t,E,C,D,H⟩ := emitAnd hinput V W
    exact ⟨s,t,E,C.le,D,H⟩
  xorGate := fun V W => by
    obtain ⟨s,t,E,C,D,H⟩ := emitXor hinput V W
    exact ⟨s,t,E,C.le,D,H⟩

end Build
end Decode

namespace Decode.Build

variable {w : Nat} {X : Type*}

def decoderBudget (q h : Nat) : Nat :=
  let m := (h+1)/2
  (2*q)*(5*2^(Nat.clog 2 m)*2) + (2*q)*m

def coef (h : Nat) (x : Nat → Bool) (i : Nat) : Bool :=
  !(if i+1 < h then Decode.chi x (i+1) else x h)

theorem finishStrips (input : X → List Bool) (hinput : ∀ x, (input x).length = w)
    (s : Build w) (q h l : Nat) (hh : 2 ≤ h)
    (word : Nat → X → Nat → Bool) (reply : Nat → Nat → Nat) (tail : Nat → Bool → Nat)
    (hy : ∀ j < q, ∀ i < h, Read input s (reply j i) (fun x => Decode.chi (word j x) i) l)
    (ht : ∀ j < q, ∀ b : Bool, Read input s (tail j b) (fun x => word j x (h+b.toNat)) l) :
    ∃ (s' : Build w) (out : Nat → Nat → Nat), Ext s s' ∧
      s'.cost ≤ s.cost + decoderBudget q h ∧ s'.depth ≤ max s.depth (l+Nat.clog 2 (h+2)+2) ∧
      ∀ j < q, ∀ i < h+2, Read input s' (out j i) (fun x => word j x i) (l+Nat.clog 2 (h+2)+2) := by
  let K := bitKit input hinput
  obtain ⟨s₁,one,E₁,C₁,D₁,V₁⟩ := emitConst hinput s true
  obtain ⟨s₂,zero,E₂,C₂,D₂,V₂⟩ := emitConst hinput s₁ false
  obtain ⟨s₃,co,E₃,C₃,D₃,V₃⟩ := K.aff.batch (T := Nat → Nat) s₂ q 0 l
    (fun s j rr => ∀ i < h, Read input s (rr i) (fun x => coef h (word j x) i) l)
    (fun e V i hi => read_persist hinput e (V i hi)) (by
      intro s' j E hj
      obtain ⟨s'',r,E',C,D,V⟩ := K.aff.batch (T := Nat) s' h 0 l
        (fun s i r => Read input s r (fun x => coef h (word j x) i) l)
        (fun e V => read_persist hinput e V) (by
          intro s'' i E' hi
          have e := E₁.trans (E₂.trans (E.trans E'))
          by_cases H : i+1<h
          · have V := read_persist hinput e (hy j hj (i+1) H)
            obtain ⟨sNew,t,E'',C,D,W⟩ := emitNot hinput V
            exact ⟨sNew,t,E'',C.le,D,by simpa only [coef, ite_eq_left H] using W⟩
          · have V := read_persist hinput e (ht j hj false)
            obtain ⟨sNew,t,EN,C,D,W⟩ := emitNot hinput V
            exact ⟨sNew,t,EN,C.le,D,by simpa only [coef, ite_eq_right H, Bool.toNat_false, Nat.add_zero] using W⟩)
      exact ⟨s'',r,E',by simpa only [Nat.mul_zero, Nat.add_zero] using C,D,V⟩)
  have E₀ := E₁.trans (E₂.trans E₃)
  let m := (h+1)/2
  let len : Nat → Nat := fun j => laneLen h (j%2)
  let f : Nat → Nat → X → Aff := fun j i x => stripMap h (word (j/2) x) (2*i+j%2)
  let bits : Nat → Nat → X → Bool := fun j i x => word (j/2) x (2*i+j%2)
  let rt : Nat → Nat → Nat×Nat := fun j i => (co (j/2) (2*i+j%2),reply (j/2) (2*i+j%2))
  let b : Nat → Bool := fun j => decide (h < 2*len j + j%2)
  let seed : Nat → Nat := fun j => tail (j/2) (b j)
  have readOne : K.aff.Read s₃ (one,zero) 1 l :=
    ⟨read_weaken (read_persist hinput (E₂.trans E₃) V₁) (Nat.zero_le _),
      read_weaken (read_persist hinput E₃ V₂) (Nat.zero_le _)⟩
  have strip_idx : ∀ j < 2*q, j/2 < q := by intro j hj; omega
  have readF : ∀ j < 2*q, ∀ i < len j, K.aff.Read s₃ (rt j i) (f j i) l := by
    intro j hj i hi
    have H := laneLen_lt h (j%2) i (Nat.mod_lt _ (by decide)) hi
    exact ⟨V₃ (j/2) (strip_idx j hj) (2*i+j%2) H,
      read_persist hinput E₀ (hy (j/2) (strip_idx j hj) (2*i+j%2) H)⟩
  have readSeeds : ∀ j < 2*q, K.Read s₃ (seed j) (bits j (len j)) l := by
    intro j hj
    have E : h+(b j).toNat = 2*len j+j%2 := by
      have Z := laneLen_end h (j%2) (Nat.mod_lt _ (by decide)) hh
      change 2*len j+j%2=h ∨ 2*len j+j%2=h+1 at Z
      rcases Z with Z | Z <;> simp [b,Z]
    have R := read_persist hinput E₀ (ht (j/2) (strip_idx j hj) (b j))
    rw [E] at R
    exact R
  obtain ⟨s₄,out,E₄,C₄,D₄,V₄⟩ := K.decodeBatch s₃ (2*q) m l len f bits rt (one,zero) seed
    (fun j _ => laneLen_le h (j%2)) readOne readF readSeeds
    (fun j _ i hi x => laneMap_step h (j%2) (word (j/2) x) (Nat.mod_lt _ (by decide)) hi)
  have lev : l+Nat.clog 2 m+2 ≤ l+Nat.clog 2 (h+2)+2 := by
    have H := Nat.clog_mono_right 2 (show m ≤ h+2 by dsimp [m]; omega)
    omega
  refine ⟨s₄,fun j i => if i < h then out (2*j+i%2) (i/2) else tail j (decide (h < i)),E₀.trans E₄,?_,?_,?_⟩
  · change s₃.cost ≤ s₂.cost+q*0 at C₃
    change s₄.cost ≤ s₃.cost+(2*q)*(5*2^(Nat.clog 2 m)*2)+(2*q)*m at C₄
    rw [Nat.add_assoc] at C₄
    change s₄.cost ≤ s₃.cost+decoderBudget q h at C₄
    omega
  · change s₃.depth ≤ max s₂.depth l at D₃
    change s₄.depth ≤ max s₃.depth (l+Nat.clog 2 m+2) at D₄
    rw [D₂,D₁] at D₃
    have base : l ≤ l+Nat.clog 2 (h+2)+2 := by omega
    have d₃ := D₃.trans (max_le (le_max_left s.depth _) (base.trans (le_max_right s.depth _)))
    exact D₄.trans (max_le d₃ (lev.trans (le_max_right ..)))
  · intro j hj i hi
    by_cases I : i<h
    · have H := laneLen_covers h i I
      have A : (2*j+i%2)/2=j := by omega
      have B : (2*j+i%2)%2=i%2 := by omega
      have L : i/2 < len (2*j+i%2) := by simpa only [len,B] using H.2.1
      have V : Read input s₄ (out (2*j+i%2) (i/2)) (bits (2*j+i%2) (i/2)) (l+Nat.clog 2 m+2) :=
        V₄ (2*j+i%2) (by omega) (i/2) L
      simpa only [ite_eq_left I,bits,A,B,H.2.2] using read_weaken V lev
    · have H : h+(decide (h < i)).toNat=i := by
        by_cases F : h < i
        · simp [F]; omega
        · simp [F]; omega
      have V := read_persist hinput (E₀.trans E₄) (ht j hj (decide (h < i)))
      rw [H] at V
      simpa only [ite_eq_right I] using read_weaken V (show l ≤ l+Nat.clog 2 (h+2)+2 by omega)

theorem decoderBudget_bound (n h : Nat) (hh : 5 ≤ h) :
    decoderBudget (2*n) h + 166*n ≤ 64*n*(h+1) := by
  let m := (h+1)/2
  have Hm : 0 < m := by dsimp [m]; omega
  have Hb := pad_lt_twice m Hm
  change (2*(2*n))*(5*2^Nat.clog 2 m*2)+(2*(2*n))*m+166*n ≤ _
  by_cases H : h < 7
  · have hm : m=3 := by dsimp [m]; omega
    have hp : 2^Nat.clog 2 3 = 4 := by decide
    rw [hm,hp]
    calc
      _ = 338*n := by ring
      _ ≤ (64*6)*n := Nat.mul_le_mul_right _ (by decide)
      _ ≤ _ := by
        calc
          _ = 64*n*6 := by rw [Nat.mul_assoc, Nat.mul_comm 6, ← Nat.mul_assoc]
          _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  · have e' : 2*m ≤ h+1 := by dsimp [m]; omega
    have e : 2^Nat.clog 2 m ≤ h+1 := Hb.le.trans e'
    have e₁ : (2*(2*n))*(5*2^Nat.clog 2 m*2) ≤ 40*n*(h+1) := by
      rw [show (2*(2*n))*(5*2^Nat.clog 2 m*2) = (40*n)*2^Nat.clog 2 m by ring]
      exact Nat.mul_le_mul_left (40*n) e
    have e₂ : (2*(2*n))*m ≤ 2*n*(h+1) := by
      have d := Nat.mul_le_mul_left (2*n) e'
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using d
    have e₃ : 166*n ≤ 22*n*(h+1) := by
      have d : 166 ≤ 22*(h+1) := by omega
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_left n d
    have E : 40*n*(h+1)+2*n*(h+1)+22*n*(h+1) = 64*n*(h+1) := by ring
    omega
theorem decoderBudget_bound167 (n h : Nat) (hh : 5 ≤ h) :
    decoderBudget (2*n) h + 167*n ≤ 64*n*(h+1) := by
  let m := (h+1)/2
  have Hm : 0 < m := by dsimp [m]; omega
  have Hb := pad_lt_twice m Hm
  change (2*(2*n))*(5*2^Nat.clog 2 m*2)+(2*(2*n))*m+167*n ≤ _
  by_cases H : h < 7
  · have hm : m=3 := by dsimp [m]; omega
    have hp : 2^Nat.clog 2 3 = 4 := by decide
    rw [hm,hp]
    calc
      _ = 339*n := by ring
      _ ≤ (64*6)*n := Nat.mul_le_mul_right _ (by decide)
      _ ≤ _ := by
        calc
          _ = 64*n*6 := by rw [Nat.mul_assoc, Nat.mul_comm 6, ← Nat.mul_assoc]
          _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  · have e' : 2*m ≤ h+1 := by dsimp [m]; omega
    have e : 2^Nat.clog 2 m ≤ h+1 := Hb.le.trans e'
    have e₁ : (2*(2*n))*(5*2^Nat.clog 2 m*2) ≤ 40*n*(h+1) := by
      rw [show (2*(2*n))*(5*2^Nat.clog 2 m*2) = (40*n)*2^Nat.clog 2 m by ring]
      exact Nat.mul_le_mul_left (40*n) e
    have e₂ : (2*(2*n))*m ≤ 2*n*(h+1) := by
      have d := Nat.mul_le_mul_left (2*n) e'
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using d
    have e₃ : 167*n ≤ 22*n*(h+1) := by
      have d : 167 ≤ 22*(h+1) := by omega
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_left n d
    have E : 40*n*(h+1)+2*n*(h+1)+22*n*(h+1) = 64*n*(h+1) := by ring
    omega

end Decode.Build

namespace Select

def chi (u : Nat → Bool) (i : Nat) : Bool := xor (u i) (!(u (i+1)) && u (i+2))
def sub (len : Nat) (f : Nat → Bool) (i : Nat) : List Bool :=
  List.ofFn (fun t : Fin len => f (i+t.val))
def extend : List Bool → Bool → Bool → List Bool
  | [], a, b => [a,b]
  | y :: ys, a,b =>
    let us := extend ys a b
    xor y (!(us.getD 0 false) && us.getD 1 false) :: us

def signature (y s : List Bool) (a b : Bool) : List Bool :=
  List.ofFn (fun t : Fin y.length => chi (fun i => xor ((extend y a b).getD i false) (s.getD i false)) t.val)

def recover (y s z : List Bool) : Bool × Bool :=
  if signature y s true true = z then (true,true)
  else if signature y s true false = z then (true,false)
  else if signature y s false true = z then (false,true)
  else (false,false)

def badR (y : List Bool) (q : Fin 3) : Bool :=
  if q = 0 then !y.getD 2 false && !y.getD 4 false
  else if q = 1 then y.getD 4 false
  else y.getD 2 false && !y.getD 4 false

def badC (y : List Bool) (q : Fin 3) : Bool :=
  if q = 0 then y.getD 2 false && !y.getD 3 false
  else if q = 1 then !y.getD 2 false && !y.getD 3 false
  else y.getD 3 false

def pick (r c : List Bool) : Fin 3 :=
  if !(badR r 0 || badC c 0) then 0 else if !(badR r 1 || badC c 1) then 1 else 2

theorem pick_good (r c : List Bool) : badR r (pick r c) = false ∧ badC c (pick r c) = false := by
  unfold pick badR badC
  cases r.getD 2 false <;> cases r.getD 4 false <;>
    cases c.getD 2 false <;> cases c.getD 3 false <;> decide

def pat (col : Bool) (q : Fin 3) : List Bool :=
  if col then
    if q = 0 then [true,false,true,true,true,true]
    else if q = 1 then [false,true,true,true,true,true]
    else [false,true,true,false,true,true]
  else
    if q = 0 then [true,true,true,true,true,true,false]
    else if q = 1 then [false,false,true,false,false,true,false]
    else [false,false,true,true,true,true,true]

private theorem recover_row_finite :
    ∀ (y0 y1 y2 y3 y4 a b : Bool) (q : Fin 3),
    let y := [y0,y1,y2,y3,y4]
    badR y q = false → recover y (pat false q) (signature y (pat false q) a b) = (a,b) := by
  decide

private theorem recover_col_finite :
    ∀ (y0 y1 y2 y3 a b : Bool) (q : Fin 3),
    let y := [y0,y1,y2,y3]
    badC y q = false → recover y (pat true q) (signature y (pat true q) a b) = (a,b) := by
  decide

@[simp] theorem sub_len (len : Nat) (f : Nat → Bool) (i : Nat) : (sub len f i).length = len := by
  simp [sub]

@[simp] theorem sub_get (len : Nat) (f : Nat → Bool) (i t : Nat) (ht : t < len) :
    (sub len f i).getD t false = f (i+t) := by
  simp [sub, List.getD_eq_getElem?_getD, ht]

theorem sub_succ (m : Nat) (u : Nat → Bool) (i : Nat) :
    sub (m+1) u i = u i :: sub m u (i+1) := by
  simp [sub, List.ofFn_succ, Nat.add_assoc, Nat.add_comm 1]

private theorem invert_chi (u : Nat → Bool) (i : Nat) : xor (chi u i) (!(u (i+1)) && u (i+2)) = u i := by
  unfold chi
  cases u i <;> cases u (i+1) <;> cases u (i+2) <;> decide

theorem extend_sub (len : Nat) (u : Nat → Bool) (i : Nat) :
    extend (sub len (chi u) i) (u (i+len)) (u (i+len+1)) = sub (len+2) u i := by
  induction len generalizing i with
  | zero => simp [extend, sub, List.ofFn_succ]
  | succ len ih =>
    rw [sub_succ len]
    change (xor (chi u i) (!((extend (sub len (chi u) (i+1)) (u (i+(len+1)))
        (u (i+(len+1)+1))).getD 0 false) &&
        (extend (sub len (chi u) (i+1)) (u (i+(len+1)))
        (u (i+(len+1)+1))).getD 1 false) :: _) = _
    rw [show i + (len+1) = (i+1)+len by omega, ih, sub_succ (len+2)]
    rw [sub_get _ _ _ _ (by omega : 0 < len+2), sub_get _ _ _ _ (by omega : 1 < len+2)]
    simp [Nat.add_assoc, invert_chi]

theorem signature_sub (len : Nat) (u s : Nat → Bool) (i : Nat) :
    signature (sub len (chi u) i) (sub (len+2) s i) (u (i+len)) (u (i+len+1)) =
      sub len (chi (fun j => xor (u j) (s j))) i := by
  unfold signature
  rw [extend_sub]
  apply List.ext_getElem
  · simp
  · intro t ht ht'
    have q : t < len := by simpa using ht'
    simp only [List.getElem_ofFn, sub] at *
    change chi (fun j => xor ((sub (len+2) u i).getD j false) ((sub (len+2) s i).getD j false)) t = _
    simp only [chi, sub_get _ _ _ _ (by omega : t < len+2),
      sub_get _ _ _ _ (by omega : t+1 < len+2), sub_get _ _ _ _ (by omega : t+2 < len+2), Nat.add_assoc]

private theorem recover_row_word (u : Nat → Bool) (i : Nat) (q : Fin 3)
    (g : badR (sub 5 (chi u) i) q = false) :
    recover (sub 5 (chi u) i) (pat false q)
      (signature (sub 5 (chi u) i) (pat false q) (u (i+5)) (u (i+5+1))) = (u (i+5),u (i+5+1)) := by
  simp only [sub, List.ofFn_succ, List.ofFn_zero] at g ⊢
  exact recover_row_finite _ _ _ _ _ _ _ q g

private theorem recover_col_word (u : Nat → Bool) (i : Nat) (q : Fin 3)
    (g : badC (sub 4 (chi u) i) q = false) :
    recover (sub 4 (chi u) i) (pat true q)
      (signature (sub 4 (chi u) i) (pat true q) (u (i+4)) (u (i+4+1))) = (u (i+4),u (i+4+1)) := by
  simp only [sub, List.ofFn_succ, List.ofFn_zero] at g ⊢
  exact recover_col_finite _ _ _ _ _ _ q g

end Select

namespace Select

open scoped BigOperators

def buildKey (k : Nat) (f : Fin k → Bool) : Nat :=
  ∑ i : Fin k, if f i then 2^i.val else 0

private theorem buildKey_succ (k : Nat) (f : Fin (k+1) → Bool) :
    buildKey (k+1) f = 2 * buildKey k (fun i => f i.succ) + (f 0).toNat := by
  unfold buildKey
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  cases f 0 <;> simp [Nat.pow_succ, Nat.mul_comm, Nat.add_comm]

theorem buildKey_bit (k : Nat) (f : Fin k → Bool) (j : Fin k) :
    (buildKey k f).testBit j.val = f j := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    rw [buildKey_succ]
    have hb : (f 0).toNat < 2^1 := by cases f 0 <;> decide
    change (2^1 * _ + _).testBit j.val = _
    rw [Nat.testBit_two_pow_mul_add _ hb]
    refine Fin.cases ?_ (fun i => ?_) j
    · change (f 0).toNat.testBit 0 = f 0
      cases f 0 <;> decide
    · simpa using ih (fun i => f i.succ) i

theorem buildKey_lt (k : Nat) (f : Fin k → Bool) : buildKey k f < 2^k := by
  induction k with
  | zero => simp [buildKey]
  | succ k ih =>
    rw [buildKey_succ, Nat.pow_succ, Nat.mul_comm (2^k)]
    have q := ih (fun i => f i.succ)
    cases f 0 <;> simp <;> omega

def pos (k h start t : Nat) : Nat := (start+h+k-9+t) % k

theorem pos_lt {k h start t : Nat} (hk : 0 < k) : pos k h start t < k := Nat.mod_lt _ hk

theorem pos_inj {k h start a b : Nat} (ha : a < k) (hb : b < k) :
    pos k h start a = pos k h start b ↔ a = b := by
  constructor
  · intro e
    exact (Nat.ModEq.add_left_cancel' (start+h+k-9) e).eq_of_lt_of_lt ha hb
  · intro e; rw [e]

def support (q : Fin 3) : List Nat :=
  if q = 0 then [4,7] else if q = 1 then [1,6,7] else [1,6,9]

def keyFlag (k h start : Nat) (q : Fin 3) (i : Fin k) : Bool :=
  decide (i.val ∈ (support q).map (pos k h start))

def key (k h start : Nat) (q : Fin 3) : Nat := buildKey k (keyFlag k h start q)

def menu (k h start : Nat) : Finset Nat := Finset.univ.image (key k h start : Fin 3 → Nat)

theorem key_mem (k h start : Nat) (q : Fin 3) : key k h start q ∈ menu k h start := by
  exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩

theorem menu_range (k h start : Nat) : menu k h start ⊆ Finset.range (2^k) := by
  intro x hx
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_range.mpr (buildKey_lt _ _)

theorem key_flag_pos {k h start t : Nat} (hk : 11 ≤ k) (ht : t < 11) (q : Fin 3) :
    keyFlag k h start q ⟨pos k h start t,pos_lt (by omega)⟩ = decide (t ∈ support q) := by
  fin_cases q <;> simp [keyFlag, support, List.mem_cons, pos_inj (by omega : t < k) (by omega : 4 < k),
    pos_inj (by omega : t < k) (by omega : 7 < k), pos_inj (by omega : t < k) (by omega : 1 < k),
    pos_inj (by omega : t < k) (by omega : 6 < k), pos_inj (by omega : t < k) (by omega : 9 < k)]

theorem key_bit_pos {k h start t : Nat} (hk : 11 ≤ k) (ht : t < 11) (q : Fin 3) :
    (key k h start q).testBit (pos k h start t) = decide (t ∈ support q) := by
  exact (buildKey_bit _ _ ⟨_,pos_lt (by omega)⟩).trans (key_flag_pos hk ht q)

theorem menu_card {k h start : Nat} (hk : 11 ≤ k) : (menu k h start).card = 3 := by
  have hinj : Function.Injective (key k h start : Fin 3 → Nat) := by
    intro p q eq
    have hp := congrArg (fun z : Nat => z.testBit (pos k h start 4)) eq
    have hq := congrArg (fun z : Nat => z.testBit (pos k h start 9)) eq
    simp only [key_bit_pos hk (by decide : 4 < 11), key_bit_pos hk (by decide : 9 < 11)] at hp hq
    fin_cases p <;> fin_cases q <;> first | rfl | (exfalso; exact Bool.noConfusion hp) | (exfalso; exact Bool.noConfusion hq)
  simp [menu, Finset.card_image_of_injective _ hinj]

def len (col : Bool) : Nat := if col then 4 else 5

def shift (k start : Nat) (col : Bool) (x j : Nat) : Bool :=
  let bit := fun back : Nat => x.testBit ((start+j+k-back) % k)
  if col then xor (bit 1) (xor (bit 3) (bit 5))
  else xor (bit 0) (xor (bit 1) (bit 2))

def observe (h k start : Nat) (col : Bool) (x u m : Nat) : List Bool :=
  sub m (chi (fun t => xor (u.testBit t) (shift k start col x t))) (h-m)

private theorem shift_pos {h k start m t b : Nat} (hh : m ≤ h) (hk : 11 ≤ k)
    (hm : m ≤ 9) (hb : b ≤ 9-m+t) :
    (start+(h-m+t)+k-b) % k = pos k h start (9-m+t-b) := by
  unfold pos
  congr 1
  omega

def stepPat (col : Bool) (q : Fin 3) (t : Nat) : Bool :=
  let bit := fun b => decide ((9-len col+t-b) ∈ support q)
  if col then xor (bit 1) (xor (bit 3) (bit 5))
  else xor (bit 0) (xor (bit 1) (bit 2))

private theorem step_pat_finite : ∀ (col : Bool) (q : Fin 3),
    sub (len col+2) (stepPat col q) 0 = pat col q := by decide

theorem strip_pattern {h k start : Nat} (hh : 5 ≤ h) (hk : h+6 ≤ k) (col : Bool) (q : Fin 3) :
    sub (len col+2) (shift k start col (key k h start q)) (h-len col) = pat col q := by
  rw [← step_pat_finite col q]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hi0 : i < len col+2 := by simpa using hi
    simp only [sub, List.getElem_ofFn, Nat.zero_add]
    have hb (b : Nat) (bb : b ≤ (if col then 5 else 2)) :
        (key k h start q).testBit ((start+(h-len col+i)+k-b)%k) =
          decide ((9-len col+i-b) ∈ support q) := by
      have h0 : len col ≤ h := by cases col <;> simp [len] <;> omega
      have h1 : len col ≤ 9 := by cases col <;> decide
      have h2 : b ≤ 9-len col+i := by cases col <;> simp [len] at * <;> omega
      rw [shift_pos h0 (by omega) h1 h2, key_bit_pos (by omega) (by omega)]
    cases col
    · simp only [shift, stepPat, Bool.false_eq_true, ↓reduceIte]
      rw [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide)]
    · simp only [shift, stepPat, ↓reduceIte]
      rw [hb 1 (by decide), hb 3 (by decide), hb 5 (by decide)]

theorem recover_selected {h k start : Nat} (hh : 5 ≤ h) (hk : h+6 ≤ k) (r c : Nat) (col : Bool) :
    let ry := sub 5 (chi r.testBit) (h-5)
    let cy := sub 4 (chi c.testBit) (h-4)
    let q := pick ry cy
    let x := key k h start q
    let u := if col then c else r
    recover (sub (len col) (chi u.testBit) (h-len col))
      (sub (len col+2) (shift k start col x) (h-len col))
      (observe h k start col x u (len col)) = (u.testBit h,u.testBit (h+1)) := by
  dsimp only
  unfold observe
  rw [← signature_sub, strip_pattern hh hk]
  have gg := pick_good (sub 5 (chi r.testBit) (h-5)) (sub 4 (chi c.testBit) (h-4))
  cases col
  · simp only [len, Bool.false_eq_true, ↓reduceIte]
    have e := recover_row_word r.testBit (h-5) _ gg.1
    simpa only [Nat.sub_add_cancel hh] using e
  · simp only [len, ↓reduceIte]
    have e := recover_col_word c.testBit (h-4) _ gg.2
    simpa only [Nat.sub_add_cancel (by omega : 4 ≤ h)] using e

end Select

namespace Select

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

def depth (w : Nat) (C : Circuit) : Nat :=
  (C.gates.foldl (fun (ds : List Nat) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).foldr max 0

def localCircuit : Circuit := ⟨[
  ⟨.or, []⟩, ⟨.or, [0,1]⟩, ⟨.not,[3]⟩, ⟨.and,[2,6]⟩, ⟨.not,[7]⟩,
  ⟨.and,[5,8]⟩, ⟨.not,[1]⟩, ⟨.or,[2,3]⟩, ⟨.and,[10,11]⟩,
  ⟨.not,[9]⟩, ⟨.not,[12]⟩, ⟨.and,[13,14]⟩, ⟨.not,[15]⟩], 9⟩

theorem localFan : ∀ g ∈ localCircuit.gates, g.inputs.length ≤ 2 := by
  intro g hg
  simp only [localCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem localBack : ReadsBack 4 localCircuit := by
  intro j hj
  let i : Fin 13 := ⟨j,hj⟩
  suffices ∀ i : Fin 13, ∀ a ∈ (gateAt localCircuit i.val).inputs, a < 4 + i.val by exact this i
  intro q
  fin_cases q <;>
    simp [gateAt, localCircuit]

theorem localCount : localCircuit.gates.countP nonlinear = 6 := by decide

theorem localDepth : depth 4 localCircuit = 3 := by decide

theorem constantsAndNOTFree : nonlinear ⟨.or, []⟩ = false ∧
    ∀ a : Nat, nonlinear ⟨.not, [a]⟩ = false := by
  constructor
  · decide
  · intro a; rfl

def localInput (r c : List Bool) : List Bool :=
  [r.getD 2 false, r.getD 4 false, c.getD 2 false, c.getD 3 false]

def flagTap (k h start : Nat) (i : Fin k) : Nat :=
  if i.val = pos k h start 4 then 9
  else if i.val = pos k h start 7 then 16
  else if i.val = pos k h start 1 ∨ i.val = pos k h start 6 then 13
  else if i.val = pos k h start 9 then 15 else 4

theorem flagTap_bound (k h start : Nat) (i : Fin k) : flagTap k h start i < 4 + localCircuit.gates.length := by
  unfold flagTap
  split <;> try decide
  split <;> try decide
  split <;> try decide
  split <;> decide

private theorem localOutputs (r c : List Bool) :
    let w := localCircuit.wires (localInput r c)
    let q := pick r c
    w.getD 4 false = false ∧
    w.getD 9 false = decide (q = 0) ∧
    w.getD 16 false = decide (q ≠ 2) ∧
    w.getD 13 false = decide (q ≠ 0) ∧
    w.getD 15 false = decide (q = 2) := by
  unfold localInput pick badR badC
  cases r.getD 2 false <;> cases r.getD 4 false <;>
    cases c.getD 2 false <;> cases c.getD 3 false <;> decide

theorem flagTap_value {k h start : Nat} (hk : 11 ≤ k) (r c : List Bool) (i : Fin k) :
    (localCircuit.wires (localInput r c)).getD (flagTap k h start i) false =
      keyFlag k h start (pick r c) i := by
  have out := localOutputs r c
  dsimp only at out
  obtain ⟨z,a,b,cc,d⟩ := out
  unfold flagTap
  split
  · next hi =>
    rw [a]
    have he : i = ⟨pos k h start 4,pos_lt (by omega)⟩ := Fin.ext hi
    rw [he]
    rw [key_flag_pos hk (by decide : 4 < 11)]
    generalize pick r c = q
    fin_cases q <;> decide
  · next hn4 =>
    split
    · next hi =>
      rw [b]
      have he : i = ⟨pos k h start 7,pos_lt (by omega)⟩ := Fin.ext hi
      rw [he]
      rw [key_flag_pos hk (by decide : 7 < 11)]
      generalize pick r c = q
      fin_cases q <;> decide
    · next hn7 =>
      split
      · next hi =>
        rw [cc]
        rcases hi with hi | hi
        · have he : i = ⟨pos k h start 1,pos_lt (by omega)⟩ := Fin.ext hi
          rw [he]
          rw [key_flag_pos hk (by decide : 1 < 11)]
          generalize pick r c = q
          fin_cases q <;> decide
        · have he : i = ⟨pos k h start 6,pos_lt (by omega)⟩ := Fin.ext hi
          rw [he]
          rw [key_flag_pos hk (by decide : 6 < 11)]
          generalize pick r c = q
          fin_cases q <;> decide
      · next hn16 =>
        split
        · next hi =>
          rw [d]
          have he : i = ⟨pos k h start 9,pos_lt (by omega)⟩ := Fin.ext hi
          rw [he]
          rw [key_flag_pos hk (by decide : 9 < 11)]
          generalize pick r c = q
          fin_cases q <;> decide
        · next hn9 =>
          rw [z]
          have hn1 : i.val ≠ pos k h start 1 := fun h => hn16 (Or.inl h)
          have hn6 : i.val ≠ pos k h start 6 := fun h => hn16 (Or.inr h)
          generalize pick r c = q
          fin_cases q <;> simp [keyFlag, support, hn1, hn4, hn6, hn7, hn9]

theorem localChosenKey {k h start : Nat} (hk : 11 ≤ k) (r c : List Bool) :
    buildKey k (fun i => (localCircuit.wires (localInput r c)).getD (flagTap k h start i) false) =
      key k h start (pick r c) := by
  unfold key
  congr 1
  funext i
  exact flagTap_value hk r c i

end Select

namespace Select

inductive TailPin where
  | reply (index : Nat)
  | shift (index : Nat)
  | observation (index : Nat)

inductive Formula where
  | input (i : TailPin)
  | lit (b : Bool)
  | neg (x : Formula)
  | add (x y : Formula)
  | mul (x y : Formula)
  | dis (x y : Formula)

def Formula.val (f : TailPin → Bool) : Formula → Bool
  | .input i => f i
  | .lit b => b
  | .neg x => !(x.val f)
  | .add x y => xor (x.val f) (y.val f)
  | .mul x y => x.val f && y.val f
  | .dis x y => x.val f || y.val f

def Formula.size : Formula → Nat
  | .input _ | .lit _ => 0
  | .neg x => x.size
  | .add x y => x.size + y.size
  | .mul x y | .dis x y => x.size + y.size + 1

def Formula.depth : Formula → Nat
  | .input _ | .lit _ => 0
  | .neg x => x.depth
  | .add x y => max x.depth y.depth
  | .mul x y | .dis x y => max x.depth y.depth + 1

def Formula.compl : Formula → Formula
  | .lit a => .lit (!a)
  | a => .neg a

def Formula.prod : Formula → Formula → Formula
  | .lit true, b => b
  | .lit false, _ => .lit false
  | a, .lit true => a
  | _, .lit false => .lit false
  | a,b => .mul a b

@[simp] theorem Formula.val_compl (f : TailPin → Bool) (a : Formula) :
    (a.compl).val f = !(a.val f) := by cases a <;> rfl

@[simp] theorem Formula.val_prod (f : TailPin → Bool) (a b : Formula) :
    (a.prod b).val f = (a.val f && b.val f) := by
  cases a <;> cases b <;> try rfl
  all_goals (cases ‹Bool› <;> try cases ‹Bool›); all_goals simp [prod, val]

def backFormula (a b : Bool) : List Formula → List Formula
  | [] => [.lit a,.lit b]
  | y :: ys =>
    let sub := backFormula a b ys
    let u := sub.getD 0 (.lit false)
    let v := sub.getD 1 (.lit false)
    .add y (u.compl.prod v) :: sub

private theorem val_get (f : TailPin → Bool) (l : List Formula) (i : Nat) :
    (l.getD i (.lit false)).val f = (l.map (Formula.val f)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

private theorem val_back (f : TailPin → Bool) (a b : Bool) (l : List Formula) :
    (backFormula a b l).map (Formula.val f) = extend (l.map (Formula.val f)) a b := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [backFormula, Formula.val, Formula.val_prod, Formula.val_compl, List.map_cons, val_get, extend, ih]

def sigFormula (m : Nat) (a b : Bool) : List Formula :=
  let u := backFormula a b (List.ofFn fun i : Fin m => .input (.reply i.val))
  let v := fun i => Formula.add (u.getD i (.lit false)) (.input (.shift i))
  List.ofFn fun i : Fin m => .add (v i.val) ((v (i.val+1)).compl.prod (v (i.val+2)))

def tailEnv (y s z : List Bool) : TailPin → Bool
  | .reply i => y.getD i false
  | .shift i => s.getD i false
  | .observation i => z.getD i false

private theorem idx_list {α : Type} (l : List α) (d : α) :
    (List.ofFn fun i : Fin l.length => l.getD i.val d) = l := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

private theorem val_sig (y s z : List Bool) (a b : Bool) :
    (sigFormula y.length a b).map (Formula.val (tailEnv y s z)) = signature y s a b := by
  unfold sigFormula signature
  rw [List.map_ofFn]
  congr 1
  funext i
  have hr : List.ofFn ((Formula.val (tailEnv y s z)) ∘
      fun i : Fin y.length => Formula.input (.reply i.val)) = y := idx_list y false
  simp only [Function.comp_apply, Formula.val, Formula.val_prod, Formula.val_compl, chi, val_get, val_back, List.map_ofFn, tailEnv, hr]

def compareFormula : List Formula → Nat → Formula
  | [],_ => .lit true
  | u :: us,j => ((Formula.add u (.input (.observation j))).compl).prod (compareFormula us (j+1))

private theorem val_compare (y s z : List Bool) (l : List Formula) (j : Nat)
    (h : z.length = j + l.length) :
    (compareFormula l j).val (tailEnv y s z) = decide (l.map (Formula.val (tailEnv y s z)) = z.drop j) := by
  induction l generalizing z j with
  | nil => simp [compareFormula, Formula.val, List.drop_eq_nil_of_le (by simpa using h.le : z.length ≤ j)]
  | cons u us ih =>
    have hj : j < z.length := by simp at h; omega
    have ht : z.length = (j+1) + us.length := by simp at h; omega
    have ze : z.drop j = z.getD j false :: z.drop (j+1) := by
      rw [List.drop_eq_getElem_cons hj]
      simp [hj]
    unfold compareFormula
    rw [Formula.val_prod, Formula.val_compl, ih _ _ ht, ze]
    have heq (p q : Bool) : (!(p ^^ q)) = decide (p = q) := by cases p <;> cases q <;> decide
    simp [Formula.val, tailEnv, heq]

def tailForm (m : Nat) : Formula × Formula :=
  let tt := compareFormula (sigFormula m true true) 0
  let tf := compareFormula (sigFormula m true false) 0
  let ft := compareFormula (sigFormula m false true) 0
  (.dis tt tf, .dis tt (.mul (.neg tf) ft))

private theorem val_hit (y s z : List Bool) (h : z.length = y.length) (a b : Bool) :
    (compareFormula (sigFormula y.length a b) 0).val (tailEnv y s z) = decide (signature y s a b = z) := by
  rw [val_compare, val_sig, List.drop_zero]
  simpa [sigFormula] using h

theorem tailForm_correct (y s z : List Bool) (h : z.length = y.length) :
    ((tailForm y.length).1.val (tailEnv y s z), (tailForm y.length).2.val (tailEnv y s z)) = recover y s z := by
  unfold tailForm recover
  simp only [Formula.val, val_hit y s z h]
  generalize signature y s true true = t₁
  generalize signature y s true false = t₂
  generalize signature y s false true = t₃
  by_cases e₁ : t₁ = z <;> by_cases e₂ : t₂ = z <;> by_cases e₃ : t₃ = z <;> simp [*]

theorem tailForm_row_cost : (tailForm 5).1.size + (tailForm 5).2.size = 103 := by decide

theorem tailForm_col_cost : (tailForm 4).1.size + (tailForm 4).2.size = 58 := by decide

theorem tailForm_bound (col : Bool) :
    (tailForm (len col)).1.size + (tailForm (len col)).2.size ≤ 103 ∧
    max (tailForm (len col)).1.depth (tailForm (len col)).2.depth ≤ 7 := by
  cases col <;> decide

end Select

namespace Select

open PEqualNP.CircuitLowerBounds

def FormPins (m : Nat) : TailPin → Bool
  | .reply i | .observation i => decide (i < m)
  | .shift i => decide (i < m+2)

def Formula.pinsOK (m : Nat) : Formula → Bool
  | .input i => FormPins m i
  | .lit _ => true
  | .neg x => x.pinsOK m
  | .add x y | .mul x y | .dis x y => x.pinsOK m && y.pinsOK m

theorem tailForm_pins (col : Bool) :
    (tailForm (len col)).1.pinsOK (len col) = true ∧
    (tailForm (len col)).2.pinsOK (len col) = true := by
  cases col <;> decide

theorem tailForm_selected {h k start : Nat} (hh : 5 ≤ h) (hk : h+6 ≤ k) (r c : Nat) (col : Bool) :
    let ry := sub 5 (chi r.testBit) (h-5)
    let cy := sub 4 (chi c.testBit) (h-4)
    let q := pick ry cy
    let x := key k h start q
    let u := if col then c else r
    let y := sub (len col) (chi u.testBit) (h-len col)
    let s := sub (len col+2) (shift k start col x) (h-len col)
    let z := observe h k start col x u (len col)
    let F := tailForm (len col)
    (F.1.val (tailEnv y s z), F.2.val (tailEnv y s z)) = (u.testBit h,u.testBit (h+1)) := by
  dsimp only
  have zlen : (observe h k start col (key k h start
      (pick (sub 5 (chi r.testBit) (h-5)) (sub 4 (chi c.testBit) (h-4))))
      (if col then c else r) (len col)).length =
      (sub (len col) (chi ((if col then c else r).testBit)) (h-len col)).length := by simp [observe]
  have cf := tailForm_correct _
    (sub (len col+2) (shift k start col (key k h start
      (pick (sub 5 (chi r.testBit) (h-5)) (sub 4 (chi c.testBit) (h-4))))) (h-len col)) _ zlen
  rw [sub_len] at cf
  rw [cf]
  exact recover_selected hh hk r c col

theorem primitive_nonlin (a b : Nat) :
    nonlinear ⟨.and,[a,b]⟩ = true ∧
    nonlinear ⟨.or,[a,b]⟩ = true ∧
    nonlinear ⟨.mod 2,[a,b]⟩ = false ∧
    nonlinear ⟨.not,[a]⟩ = false ∧
    nonlinear ⟨.and,[]⟩ = false ∧ nonlinear ⟨.or,[]⟩ = false := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem primitive_xor (a b : Bool) :
    (!((GateOp.mod 2).eval [a,b])) = xor a b := by cases a <;> cases b <;> decide

theorem shift_pin_eq {h k start : Nat} (col : Bool) (x i : Nat) (hi : i < len col+2) :
    let idx : Nat → Nat := fun back => (start+(h-len col+i)+k-back)%k
    let p := fun back => x.testBit (idx back)
    (sub (len col+2) (shift k start col x) (h-len col)).getD i false =
      (if col then xor (p 1) (xor (p 3) (p 5)) else xor (p 0) (xor (p 1) (p 2))) := by
  dsimp only
  rw [sub_get _ _ _ _ hi]
  rfl

end Select

namespace Select

structure FormulaKit (S R X : Type*) extends Decode.BitKit S R X where
  literal : ∀ (s : S) (b : Bool),
    ∃ s' t, Ext s s' ∧ cost s' ≤ cost s ∧ peak s' ≤ peak s ∧ Read s' t (fun _ => b) 0
  negGate : ∀ {s t f l}, Read s t f l →
    ∃ s' t', Ext s s' ∧ cost s' ≤ cost s ∧ peak s' ≤ max (peak s) l ∧
      Read s' t' (fun x => !(f x)) l
  orGate : ∀ {s r r' a a' l}, Read s r a l → Read s r' a' l →
    ∃ s' t, Ext s s' ∧ cost s' ≤ cost s+1 ∧ peak s' ≤ max (peak s) (l+1) ∧
      Read s' t (fun x => a x || a' x) (l+1)

namespace FormulaKit

variable {S R X : Type*} (K : FormulaKit S R X)

def Produced (s : S) (c l : Nat) (f : X → Bool) : Prop :=
  ∃ s' t, K.Ext s s' ∧ K.cost s' ≤ K.cost s+c ∧ K.peak s' ≤ max (K.peak s) l ∧ K.Read s' t f l

private theorem join {s : S} {ca cb d da db g : Nat} {f₁ f₂ : X → Bool} {op : Bool → Bool → Bool}
    (AA : K.Produced s ca (d+da) f₁)
    (BB : ∀ s', K.Ext s s' → K.Produced s' cb (d+db) f₂)
    (opGate : ∀ {s r r' a a' l}, K.Read s r a l → K.Read s r' a' l →
      K.Produced s g (l+g) (fun x => op (a x) (a' x))) :
    K.Produced s (ca+cb+g) (d+max da db+g) (fun x => op (f₁ x) (f₂ x)) := by
  obtain ⟨s₁,t₁,E₁,C₁,D₁,V₁⟩ := AA
  obtain ⟨s₂,t₂,E₂,C₂,D₂,V₂⟩ := BB s₁ E₁
  have l₁ : d+da ≤ d+max da db := Nat.add_le_add_left (le_max_left ..) _
  have l₂ : d+db ≤ d+max da db := Nat.add_le_add_left (le_max_right ..) _
  obtain ⟨s₃,t₃,E₃,C₃,D₃,V₃⟩ := opGate
    (K.weaken (K.persist E₂ V₁) l₁) (K.weaken V₂ l₂)
  refine ⟨s₃,t₃,K.trans E₁ (K.trans E₂ E₃),by omega,?_,V₃⟩
  exact D₃.trans (max_le (D₂.trans (max_le (D₁.trans (max_le (le_max_left ..)
    (l₁.trans (Nat.le_add_right ..) |>.trans (le_max_right ..))))
    (l₂.trans (Nat.le_add_right ..) |>.trans (le_max_right ..)))) (le_max_right ..))

theorem realize (s : S) (m l : Nat) (r : TailPin → R) (f : X → TailPin → Bool)
    (e : Formula) (he : e.pinsOK m = true)
    (hf : ∀ i, FormPins m i = true → K.Read s (r i) (fun x => f x i) l) :
    K.Produced s e.size (l+e.depth) (fun x => e.val (f x)) := by
  induction e generalizing s with
  | input i => exact ⟨s,r i,K.refl _,by simp [Formula.size],le_max_left ..,hf i he⟩
  | lit b =>
    obtain ⟨s₁,t,E,C,D,V⟩ := K.literal s b
    exact ⟨s₁,t,E,by simpa [Formula.size] using C,D.trans (le_max_left ..),
      K.weaken V (Nat.zero_le _)⟩
  | neg a ih =>
    obtain ⟨s₁,t₁,E₁,C₁,D₁,V₁⟩ := ih s he hf
    obtain ⟨s₂,t₂,E₂,C₂,D₂,V₂⟩ := K.negGate V₁
    exact ⟨s₂,t₂,K.trans E₁ E₂,C₂.trans C₁,D₂.trans (max_le D₁ (le_max_right ..)),V₂⟩
  | add a b ia ib =>
    simp only [Formula.pinsOK, Bool.and_eq_true] at he
    simpa only [Formula.size, Formula.depth, Formula.val, Nat.add_zero] using
      K.join (g := 0) (op := xor) (ia s he.1 hf) (fun s' E => ib s' he.2 (fun i hi => K.persist E (hf i hi)))
        (fun V V' => K.xorGate V V')
  | mul a b ia ib =>
    simp only [Formula.pinsOK, Bool.and_eq_true] at he
    simpa only [Formula.size, Formula.depth, Formula.val, Nat.add_assoc] using
      K.join (g := 1) (op := Bool.and) (ia s he.1 hf) (fun s' E => ib s' he.2 (fun i hi => K.persist E (hf i hi)))
        (fun V V' => K.andGate V V')
  | dis a b ia ib =>
    simp only [Formula.pinsOK, Bool.and_eq_true] at he
    simpa only [Formula.size, Formula.depth, Formula.val, Nat.add_assoc] using
      K.join (g := 1) (op := Bool.or) (ia s he.1 hf) (fun s' E => ib s' he.2 (fun i hi => K.persist E (hf i hi)))
        (fun V V' => K.orGate V V')

def tailBudget (col : Bool) : Nat := if col then 58 else 103

theorem realizeTail (s : S) (col : Bool) (l : Nat) (r : TailPin → R) (f : X → TailPin → Bool)
    (hf : ∀ i, FormPins (len col) i = true → K.Read s (r i) (fun x => f x i) l) :
    let F := tailForm (len col)
    ∃ s' a b, K.Ext s s' ∧ K.cost s' ≤ K.cost s + tailBudget col ∧
      K.peak s' ≤ max (K.peak s) (l+7) ∧
      K.Read s' a (fun x => F.1.val (f x)) (l+7) ∧ K.Read s' b (fun x => F.2.val (f x)) (l+7) := by
  let F := tailForm (len col)
  have P := tailForm_pins col
  have S : F.1.size + F.2.size = tailBudget col := by cases col <;> decide
  have D := (tailForm_bound col).2
  change max F.1.depth F.2.depth ≤ 7 at D
  have H₁ : l+F.1.depth ≤ l+7 := by exact Nat.add_le_add_left ((le_max_left ..).trans D) _
  have H₂ : l+F.2.depth ≤ l+7 := by exact Nat.add_le_add_left ((le_max_right ..).trans D) _
  obtain ⟨s₁,a,E₁,C₁,D₁,V₁⟩ := K.realize s (len col) l r f F.1 P.1 hf
  obtain ⟨s₂,b,E₂,C₂,D₂,V₂⟩ := K.realize s₁ (len col) l r f F.2 P.2
    (fun i hi => K.persist E₁ (hf i hi))
  refine ⟨s₂,a,b,K.trans E₁ E₂,by omega,?_,K.weaken (K.persist E₂ V₁) H₁,K.weaken V₂ H₂⟩
  exact D₂.trans (max_le (D₁.trans (max_le (le_max_left ..) (H₁.trans (le_max_right ..))))
    (H₂.trans (le_max_right ..)))

end FormulaKit
end Select

namespace Select

open Decode (Build)

variable {w : Nat} {X : Type*} {input : X → List Bool}
variable (hinput : ∀ x, (input x).length = w)

def buildKit : FormulaKit (Build w) Nat X where
  toBitKit := Build.bitKit input hinput
  literal := fun s b => by
    obtain ⟨s',t,E,C,D,V⟩ := Build.emitConst hinput s b
    exact ⟨s',t,E,C.le,D.le,V⟩
  negGate := fun V => by
    obtain ⟨s',t,E,C,D,V'⟩ := Build.emitNot hinput V
    exact ⟨s',t,E,C.le,D,V'⟩
  orGate := fun V W => by
    obtain ⟨s',t,E,C,D,V'⟩ := Build.emitOr hinput V W
    exact ⟨s',t,E,C.le,D,V'⟩

include hinput in
private theorem emitXor3 {s : Build w} {a b c l : Nat} {f g j : X → Bool}
    (A : Build.Read input s a f l) (B : Build.Read input s b g l) (C : Build.Read input s c j l) :
    ∃ s' t, Build.Ext s s' ∧ s'.cost = s.cost ∧ s'.depth ≤ max s.depth l ∧
      Build.Read input s' t (fun x => xor (f x) (xor (g x) (j x))) l := by
  obtain ⟨s₁,t₁,E₁,C₁,D₁,V₁⟩ := Build.emitXor hinput B C
  obtain ⟨s₂,t₂,E₂,C₂,D₂,V₂⟩ := Build.emitXor hinput (Build.read_persist hinput E₁ A) V₁
  exact ⟨s₂,t₂,E₁.trans E₂,C₂.trans C₁,D₂.trans (max_le D₁ (le_max_right ..)),V₂⟩

def shiftWord (h k start : Nat) (col : Bool) (x : Nat) : List Bool :=
  sub (len col+2) (shift k start col x) (h-len col)

include hinput in
theorem emitShiftPin (s : Build w) (h k start l i : Nat) (hk : 0 < k) (col : Bool) (value : X → Nat)
    (keyTap : Fin k → Nat) (hkRead : ∀ j, Build.Read input s (keyTap j) (fun x => (value x).testBit j.val) l)
    (hi : i < len col+2) :
    ∃ s' t, Build.Ext s s' ∧ s'.cost = s.cost ∧ s'.depth ≤ max s.depth l ∧
      Build.Read input s' t (fun x => (shiftWord h k start col (value x)).getD i false) l := by
  let index := fun b : Nat => ((start+(h-len col+i)+k-b)%k : Nat)
  let readBit := fun b => hkRead ⟨index b, Nat.mod_lt _ hk⟩
  have ee : (fun x => (shiftWord h k start col (value x)).getD i false) =
      (fun x => if col then xor ((value x).testBit (index 1))
        (xor ((value x).testBit (index 3)) ((value x).testBit (index 5)))
      else xor ((value x).testBit (index 0)) (xor ((value x).testBit (index 1)) ((value x).testBit (index 2)))) := by
    funext x
    exact shift_pin_eq col (value x) i hi
  rw [ee]
  cases col
  · exact emitXor3 hinput (readBit 0) (readBit 1) (readBit 2)
  · exact emitXor3 hinput (readBit 1) (readBit 3) (readBit 5)

include hinput in

theorem realizeStripTail (s : Build w) (h k start l : Nat) (hk : 0 < k) (col : Bool)
    (re ob : X → List Bool) (value : X → Nat) (rt ot : Nat → Nat) (kt : Fin k → Nat)
    (hre : ∀ i < len col, Build.Read input s (rt i) (fun x => (re x).getD i false) l)
    (hob : ∀ i < len col, Build.Read input s (ot i) (fun x => (ob x).getD i false) l)
    (hkey : ∀ i, Build.Read input s (kt i) (fun x => (value x).testBit i.val) l)
    (hrlen : ∀ x, (re x).length = len col) (holen : ∀ x, (ob x).length = len col) :
    let f := fun x => recover (re x) (shiftWord h k start col (value x)) (ob x)
    ∃ s' a b, Build.Ext s s' ∧ s'.cost ≤ s.cost + FormulaKit.tailBudget col ∧ s'.depth ≤ max s.depth (l+7) ∧
      Build.Read input s' a (fun x => (f x).1) (l+7) ∧ Build.Read input s' b (fun x => (f x).2) (l+7) := by
  let K := Build.bitKit input hinput
  have hb := K.aff.batch (T := Nat) s (len col+2) 0 l
    (fun s j t => Build.Read input s t (fun x => (shiftWord h k start col (value x)).getD j false) l)
    (fun e v => Build.read_persist hinput e v) (by
      intro s₁ j E hj
      obtain ⟨s₂,t,E₂,C,D,V⟩ := emitShiftPin hinput s₁ h k start l j hk col value kt
        (fun i => Build.read_persist hinput E (hkey i)) hj
      exact ⟨s₂,t,E₂,by change s₂.cost ≤ s₁.cost+0; omega,D,V⟩)
  obtain ⟨s₁,st,E₁,C₁,D₁,V₁⟩ := hb
  change Build.Ext s s₁ at E₁
  change s₁.cost ≤ s.cost+(len col+2)*0 at C₁
  change s₁.depth ≤ max s.depth l at D₁
  let r : TailPin → Nat := fun i => match i with
    | .reply j => rt j
    | .shift j => st j
    | .observation j => ot j
  let f : X → TailPin → Bool := fun x => tailEnv (re x) (shiftWord h k start col (value x)) (ob x)
  obtain ⟨s₂,a,b,E₂,C₂,D₂,A,B⟩ := (buildKit hinput).realizeTail s₁ col l r f (by
    intro i hi
    cases i with
    | reply j => exact Build.read_persist hinput E₁ (hre j (of_decide_eq_true hi))
    | shift j => exact V₁ j (of_decide_eq_true hi)
    | observation j => exact Build.read_persist hinput E₁ (hob j (of_decide_eq_true hi)))
  change Build.Ext s₁ s₂ at E₂
  change s₂.cost ≤ s₁.cost + FormulaKit.tailBudget col at C₂
  change s₂.depth ≤ max s₁.depth (l+7) at D₂
  have sem (x : X) : ((tailForm (len col)).1.val (f x), (tailForm (len col)).2.val (f x)) =
      recover (re x) (shiftWord h k start col (value x)) (ob x) := by
    have H := tailForm_correct (re x) (shiftWord h k start col (value x)) (ob x) ((holen x).trans (hrlen x).symm)
    rwa [hrlen x] at H
  refine ⟨s₂,a,b,E₁.trans E₂,by omega,D₂.trans (max_le (D₁.trans
    (max_le (le_max_left ..) ((Nat.le_add_right ..).trans (le_max_right ..)))) (le_max_right ..)),?_,?_⟩
  · exact ⟨A.1,fun x => (A.2.1 x).trans (congrArg Prod.fst (sem x)),A.2.2⟩
  · exact ⟨B.1,fun x => (B.2.1 x).trans (congrArg Prod.snd (sem x)),B.2.2⟩

end Select

namespace Layout40553

private theorem flat_getD {α : Type*} {n m : Nat} (f : Fin n → List α)
    (hlen : ∀ j, (f j).length = m) (j i : Nat) (hj : j < n) (hi : i < m)
    (d : α) : (List.ofFn f).flatten.getD (m*j+i) d = (f ⟨j,hj⟩).getD i d := by
  have hl : ∀ row ∈ List.ofFn f, row.length = m :=
    List.forall_mem_ofFn_iff.mpr hlen
  have hu : ∀ (rows : List (List α)) (hrows : ∀ row ∈ rows, row.length = m)
      (j i : Nat), i < m → rows.flatten.getD (m*j+i) d = (rows.getD j []).getD i d := by
    intro rows hrows j i hi
    induction rows generalizing j with
    | nil => simp
    | cons row rows ih =>
      obtain ⟨hr, hrs⟩ := List.forall_mem_cons.mp hrows
      cases j with
      | zero =>
        simpa only [List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] using
          Decode.Build.getD_append_left (by omega : i < row.length) d
      | succ j =>
        simp only [List.flatten_cons, Nat.mul_succ]
        rw [show m*j+m+i = row.length+(m*j+i) by omega,
          List.getD_append_right _ _ _ _ (by omega : row.length ≤ row.length+(m*j+i))]
        simpa only [Nat.add_sub_cancel_left, List.getD_cons_succ] using ih hrs j
  rw [hu _ hl _ _ hi]
  simp [List.getD_eq_getElem?_getD, hj]

end Layout40553

namespace Layout40553

open Decode.Build

private theorem flat_length {α : Type*} {n m : Nat} (f : Fin n → List α)
    (hlen : ∀ j, (f j).length = m) : (List.ofFn f).flatten.length = n*m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hlen 0,
      ih (fun i => f i.succ) (fun i => hlen i.succ)]
    simp [Nat.succ_mul, Nat.add_comm]

variable {X : Type*}

def yBlock (h : Nat) (r c : X → Fin n → Nat) (x : X) (j : Fin n) : List Bool :=
  List.ofFn (fun i : Fin h => Select.chi (r x j).testBit i.val) ++
  List.ofFn (fun i : Fin h => Select.chi (c x j).testBit i.val)

def dataBlock (h k start : Nat) (r c : X → Fin n → Nat) (key : X → Fin n → Nat)
    (x : X) (j : Fin n) : List Bool :=
  List.ofFn (fun i : Fin k => (key x j).testBit i.val) ++
  Select.observe h k start false (key x j) (r x j) 5 ++
  Select.observe h k start true (key x j) (c x j) 4

def input (h k start n : Nat) (r c : X → Fin n → Nat) (key : X → Fin n → Nat) (x : X) : List Bool :=
  (List.ofFn (yBlock h r c x)).flatten ++
  (List.ofFn (dataBlock h k start r c key x)).flatten

private theorem yBlock_length (h : Nat) (r c : X → Fin n → Nat) (x : X) (j : Fin n) :
    (yBlock h r c x j).length = 2*h := by simp [yBlock]; omega

private theorem dataBlock_length (h k start : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (x : X) (j : Fin n) :
    (dataBlock h k start r c key x j).length = k+9 := by
  simp [dataBlock, Select.observe, Select.sub]

private theorem y_length (h : Nat) (r c : X → Fin n → Nat) (x : X) :
    (List.ofFn (yBlock h r c x)).flatten.length = 2*n*h := by
  rw [flat_length (m := 2*h) _ (yBlock_length h r c x)]
  ring

private theorem data_length (h k start : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (x : X) :
    (List.ofFn (dataBlock h k start r c key x)).flatten.length = n*(k+9) :=
  flat_length _ (dataBlock_length h k start r c key x)

theorem input_length (h k start n : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (x : X) :
    (input h k start n r c key x).length = 2*n*h+n*(k+9) := by
  simp only [input, List.length_append, y_length, data_length]

end Layout40553

namespace Layout40553

open Decode.Build

variable {X : Type*}

theorem input_y_at (h k start n : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (x : X) (j : Fin n) (i : Nat) (hi : i < 2*h) :
    (input h k start n r c key x).getD (2*h*j.val+i) false =
      (yBlock h r c x j).getD i false := by
  have hiw : 2*h*j.val+i < 2*n*h := by
    calc
      _ < 2*h*(j.val+1) := by rw [Nat.mul_succ]; omega
      _ ≤ 2*h*n := Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr j.isLt)
      _ = 2*n*h := by ring
  rw [input, Decode.Build.getD_append_left (by rw [y_length]; exact hiw)]
  exact flat_getD (yBlock h r c x) (yBlock_length h r c x) j.val i j.isLt hi false

theorem input_data_at (h k start n : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (x : X) (j : Fin n) (i : Nat) (hi : i < k+9) :
    (input h k start n r c key x).getD (2*n*h+(k+9)*j.val+i) false =
      (dataBlock h k start r c key x j).getD i false := by
  rw [input, List.getD_append_right _ _ _ _ (by rw [y_length]; omega :
    (List.ofFn (yBlock h r c x)).flatten.length ≤ 2*n*h+(k+9)*j.val+i)]
  rw [y_length, show 2*n*h+(k+9)*j.val+i-2*n*h = (k+9)*j.val+i by omega]
  exact flat_getD (dataBlock h k start r c key x)
    (dataBlock_length h k start r c key x) j.val i j.isLt hi false

end Layout40553

namespace Layout40553

open Decode (Build)
open Decode.Build

variable {X : Type*} {w : Nat}

def word (r c : X → Fin n → Nat) (x : X) (j : Fin n) (col : Bool) : Nat :=
  if col then c x j else r x j

def replySuffix (h : Nat) (r c : X → Fin n → Nat) (j : Fin n) (col : Bool) (x : X) : List Bool :=
  Select.sub (Select.len col) (Select.chi (word r c x j col).testBit) (h-Select.len col)

def obsSuffix (h k start : Nat) (r c : X → Fin n → Nat) (key : X → Fin n → Nat)
    (j : Fin n) (col : Bool) (x : X) : List Bool :=
  Select.observe h k start col (key x j) (word r c x j col) (Select.len col)

def tailValue (h k start : Nat) (r c : X → Fin n → Nat) (key : X → Fin n → Nat)
    (j : Fin n) (col : Bool) (x : X) : Bool × Bool :=
  Select.recover (replySuffix h r c j col x)
    (Select.shiftWord h k start col (key x j)) (obsSuffix h k start r c key j col x)

theorem batch_tails (input : X → List Bool) (hinput : ∀ x, (input x).length = w)
    (s : Build w) (h k start n l : Nat) (hk : 0 < k)
    (r c : X → Fin n → Nat) (key : X → Fin n → Nat)
    (rt ot : Fin n → Bool → Nat → Nat) (kt : Fin n → Fin k → Nat)
    (hre : ∀ j col i, i < Select.len col →
      Read input s (rt j col i) (fun x => (replySuffix h r c j col x).getD i false) l)
    (hob : ∀ j col i, i < Select.len col →
      Read input s (ot j col i) (fun x => (obsSuffix h k start r c key j col x).getD i false) l)
    (hkey : ∀ j i, Read input s (kt j i) (fun x => (key x j).testBit i.val) l) :
    ∃ (s' : Build w) (tail : Fin n → Bool → Bool → Nat), Ext s s' ∧
      s'.cost ≤ s.cost+161*n ∧ s'.depth ≤ max s.depth (l+7) ∧
      ∀ j col, Read input s' (tail j col false) (fun x => (tailValue h k start r c key j col x).1) (l+7) ∧
        Read input s' (tail j col true) (fun x => (tailValue h k start r c key j col x).2) (l+7) := by
  let K := bitKit input hinput
  let P := fun (ss : Build w) (j : Nat) (t : Bool → Nat × Nat) =>
    ∀ (hj : j < n) (col : Bool),
      Read input ss (t col).1 (fun x => (tailValue h k start r c key ⟨j,hj⟩ col x).1) (l+7) ∧
      Read input ss (t col).2 (fun x => (tailValue h k start r c key ⟨j,hj⟩ col x).2) (l+7)
  obtain ⟨s',tt,E,C,D,V⟩ := K.aff.batch (T := Bool → Nat × Nat) s n 161 (l+7) P
    (fun e v hj col => ⟨read_persist hinput e (v hj col).1,
      read_persist hinput e (v hj col).2⟩) (by
      intro s₁ j E hj
      let J : Fin n := ⟨j,hj⟩
      obtain ⟨sr,ar,br,Er,Cr,Dr,Ar,Br⟩ :=
        Select.realizeStripTail hinput s₁ h k start l hk false
          (replySuffix h r c J false) (obsSuffix h k start r c key J false)
          (fun x => key x J) (rt J false) (ot J false) (kt J)
          (fun i hi => read_persist hinput E (hre J false i hi))
          (fun i hi => read_persist hinput E (hob J false i hi))
          (fun i => read_persist hinput E (hkey J i))
          (fun x => Select.sub_len ..) (fun x => Select.sub_len ..)
      obtain ⟨sc,ac,bc,Ec,Cc,Dc,Ac,Bc⟩ :=
        Select.realizeStripTail hinput sr h k start l hk true
          (replySuffix h r c J true) (obsSuffix h k start r c key J true)
          (fun x => key x J) (rt J true) (ot J true) (kt J)
          (fun i hi => read_persist hinput (E.trans Er) (hre J true i hi))
          (fun i hi => read_persist hinput (E.trans Er) (hob J true i hi))
          (fun i => read_persist hinput (E.trans Er) (hkey J i))
          (fun x => Select.sub_len ..) (fun x => Select.sub_len ..)
      refine ⟨sc, (fun col => if col then (ac,bc) else (ar,br)), Er.trans Ec, ?_, ?_, ?_⟩
      · change sc.cost ≤ sr.cost + 58 at Cc
        change sr.cost ≤ s₁.cost + 103 at Cr
        change sc.cost ≤ s₁.cost + 161
        omega
      · exact Dc.trans (max_le (Dr.trans (max_le (le_max_left ..) (le_max_right ..)))
          (le_max_right ..))
      · intro hJ col
        cases col with
        | false => exact ⟨read_persist hinput Ec Ar,read_persist hinput Ec Br⟩
        | true => exact ⟨Ac,Bc⟩)
  change s'.cost ≤ s.cost+n*161 at C
  refine ⟨s', (fun j col b => if b then (tt j.val col).2 else (tt j.val col).1), E,?_,D,?_⟩
  · simpa only [Nat.mul_comm] using C
  intro j col
  have Q := V j.val j.isLt j.isLt col
  exact ⟨Q.1,Q.2⟩

end Layout40553

namespace Layout40553

variable {X : Type*}

theorem input_reply_at (h k start n : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (x : X) (j : Fin n) (col : Bool) (i : Nat) (hi : i < h) :
    (input h k start n r c key x).getD (2*h*j.val+(if col then h+i else i)) false =
      Select.chi (word r c x j col).testBit i := by
  have hi' : (if col then h+i else i) < 2*h := by cases col <;> simp_all <;> omega
  rw [input_y_at h k start n r c key x j _ hi']
  cases col with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, word, yBlock]
    rw [Decode.Build.getD_append_left (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  | true =>
    simp only [↓reduceIte, word, yBlock]
    rw [List.getD_append_right _ _ _ _ (by simp :
      (List.ofFn (fun i : Fin h => Select.chi (r x j).testBit i.val)).length ≤ h+i)]
    simp [List.getD_eq_getElem?_getD, hi]

theorem input_key_at (h k start n : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (x : X) (j : Fin n) (i : Fin k) :
    (input h k start n r c key x).getD (2*n*h+(k+9)*j.val+i.val) false =
      (key x j).testBit i.val := by
  rw [input_data_at h k start n r c key x j i.val (by omega : i.val < k+9)]
  rw [dataBlock, Decode.Build.getD_append_left (by simp [Select.observe]; omega),
    Decode.Build.getD_append_left (by simp)]
  simp [List.getD_eq_getElem?_getD]

end Layout40553

namespace Layout40553

variable {X : Type*}

theorem input_obs_at (h k start n : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (x : X) (j : Fin n) (col : Bool)
    (i : Nat) (hi : i < Select.len col) :
    (input h k start n r c key x).getD
      (2*n*h+(k+9)*j.val+k+(if col then 5+i else i)) false =
      (obsSuffix h k start r c key j col x).getD i false := by
  have hblock : k+(if col then 5+i else i) < k+9 := by
    cases col <;> simp_all [Select.len] <;> omega
  rw [show 2*n*h+(k+9)*j.val+k+(if col then 5+i else i) =
    2*n*h+(k+9)*j.val+(k+(if col then 5+i else i)) by omega]
  rw [input_data_at h k start n r c key x j _ hblock]
  cases col with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at *
    have hi5 : i < 5 := by simpa [Select.len] using hi
    rw [dataBlock, Decode.Build.getD_append_left (by simp [Select.observe]; omega)]
    rw [List.getD_append_right _ _ _ _ (by simp :
      (List.ofFn (fun a : Fin k => (key x j).testBit a.val)).length ≤ k+i)]
    simp [obsSuffix, word, Select.len]
  | true =>
    simp only [↓reduceIte] at *
    rw [dataBlock, List.getD_append_right _ _ _ _ (by simp [Select.observe])]
    simp only [List.length_append, List.length_ofFn, Select.observe, Select.sub_len]
    rw [show k+(5+i)-(k+5)=i by omega]
    simp only [obsSuffix,word,Select.len,Select.observe]
    rfl

end Layout40553

namespace Layout40553

open Decode (Build)
open Decode.Build

variable {X : Type*}

private theorem y_index_lt {h n j i : Nat} (hj : j < n) (hi : i < 2*h) :
    2*h*j+i < 2*n*h := by
  calc
    _ < 2*h*(j+1) := by rw [Nat.mul_succ]; omega
    _ ≤ 2*h*n := Nat.mul_le_mul_left _ (by omega)
    _ = 2*n*h := by ring

private theorem data_index_lt {h k n j i : Nat} (hj : j < n) (hi : i < k+9) :
    2*n*h+(k+9)*j+i < 2*n*h+n*(k+9) := by
  calc
    _ < 2*n*h+(k+9)*(j+1) := by rw [Nat.mul_succ]; omega
    _ ≤ 2*n*h+(k+9)*n := Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    _ = 2*n*h+n*(k+9) := by ring

theorem input_read_y (h k start n : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (j : Fin n) (i : Nat) (hi : i < 2*h) :
    Read (input h k start n r c key) (empty (2*n*h+n*(k+9))) (2*h*j.val+i)
      (fun x => (yBlock h r c x j).getD i false) 0 := by
  have V := read_input (fun x => input_length h k start n r c key x)
    (empty (2*n*h+n*(k+9))) (2*h*j.val+i) (by
      have q := y_index_lt j.isLt hi
      omega)
  exact ⟨V.1, (fun x => (V.2.1 x).trans (input_y_at h k start n r c key x j i hi)), V.2.2⟩

theorem input_read_data (h k start n : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (j : Fin n) (i : Nat) (hi : i < k+9) :
    Read (input h k start n r c key) (empty (2*n*h+n*(k+9))) (2*n*h+(k+9)*j.val+i)
      (fun x => (dataBlock h k start r c key x j).getD i false) 0 := by
  have V := read_input (fun x => input_length h k start n r c key x)
    (empty (2*n*h+n*(k+9))) (2*n*h+(k+9)*j.val+i)
    (data_index_lt j.isLt hi)
  exact ⟨V.1, (fun x => (V.2.1 x).trans (input_data_at h k start n r c key x j i hi)), V.2.2⟩

end Layout40553

namespace Layout40553

open Decode (Build)
open Decode.Build
variable {X : Type*}

private theorem read_congr {w : Nat} {input : X → List Bool} {s : Build w} {t l : Nat}
    {f g : X → Bool} (V : Read input s t f l) (eq : ∀ x, f x = g x) :
    Read input s t g l := ⟨V.1,fun x => (V.2.1 x).trans (eq x),V.2.2⟩

theorem input_read_key (h k start n : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (j : Fin n) (i : Fin k) :
    Read (input h k start n r c key) (empty (2*n*h+n*(k+9)))
      (2*n*h+(k+9)*j.val+i.val) (fun x => (key x j).testBit i.val) 0 := by
  apply read_congr (input_read_data h k start n r c key j i.val (by omega : i.val < k+9))
  intro x
  exact (input_data_at h k start n r c key x j i.val (by omega)).symm.trans
    (input_key_at h k start n r c key x j i)

theorem input_read_obs (h k start n : Nat) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (j : Fin n) (col : Bool) (i : Nat)
    (hi : i < Select.len col) :
    Read (input h k start n r c key) (empty (2*n*h+n*(k+9)))
      (2*n*h+(k+9)*j.val+k+(if col then 5+i else i))
      (fun x => (obsSuffix h k start r c key j col x).getD i false) 0 := by
  have hb : k+(if col then 5+i else i) < k+9 := by
    cases col <;> simp_all [Select.len] <;> omega
  have V := input_read_data h k start n r c key j _ hb
  have he : 2*n*h+(k+9)*j.val+(k+(if col then 5+i else i)) =
      2*n*h+(k+9)*j.val+k+(if col then 5+i else i) := by omega
  rw [he] at V
  apply read_congr V
  intro x
  have H := input_obs_at h k start n r c key x j col i hi
  have he' : 2*n*h+(k+9)*j.val+k+(if col then 5+i else i) =
      2*n*h+(k+9)*j.val+(k+(if col then 5+i else i)) := by omega
  rw [he'] at H
  exact (input_data_at h k start n r c key x j _ hb).symm.trans H

theorem input_read_suffix (h k start n : Nat) (hh : 5 ≤ h) (r c : X → Fin n → Nat)
    (key : X → Fin n → Nat) (j : Fin n) (col : Bool) (i : Nat)
    (hi : i < Select.len col) :
    Read (input h k start n r c key) (empty (2*n*h+n*(k+9)))
      (2*h*j.val+(if col then h+(h-Select.len col+i) else h-Select.len col+i))
      (fun x => (replySuffix h r c j col x).getD i false) 0 := by
  have hi' : h-Select.len col+i<h := by
    cases col <;> simp_all [Select.len] <;> omega
  have hb : (if col then h+(h-Select.len col+i) else h-Select.len col+i) < 2*h := by
    cases col <;> simp_all [Select.len] <;> omega
  apply read_congr (input_read_y h k start n r c key j _ hb)
  intro x
  calc
    _ = (input h k start n r c key x).getD
        (2*h*j.val+(if col then h+(h-Select.len col+i) else h-Select.len col+i)) false :=
      (input_y_at h k start n r c key x j _ hb).symm
    _ = Select.chi (word r c x j col).testBit (h-Select.len col+i) :=
      input_reply_at h k start n r c key x j col _ hi'
    _ = (replySuffix h r c j col x).getD i false := by
      change _ = (Select.sub (Select.len col) (Select.chi (word r c x j col).testBit)
        (h-Select.len col)).getD i false
      rw [Select.sub_get _ _ _ _ hi]

end Layout40553

namespace Layout40553

open Decode (Build)
open Decode.Build
variable {X : Type*}

theorem literal_tails (h k start n : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k)
    (r c : X → Fin n → Nat) (key : X → Fin n → Nat)
    (hselected : ∀ x j, key x j = Select.key k h start
      (Select.pick (Select.sub 5 (Select.chi (r x j).testBit) (h-5))
        (Select.sub 4 (Select.chi (c x j).testBit) (h-4)))) :
    ∃ (s : Build (2*n*h+n*(k+9))) (tail : Fin n → Bool → Bool → Nat),
      s.cost ≤ 161*n ∧ s.depth ≤ 7 ∧
      ∀ j col b, Read (input h k start n r c key) s (tail j col b)
        (fun x => (word r c x j col).testBit (h+b.toNat)) 7 := by
  let s₀ := empty (2*n*h+n*(k+9))
  let rt := fun (j : Fin n) (col : Bool) (i : Nat) =>
    2*h*j.val + if col then h+(h-Select.len col+i) else h-Select.len col+i
  let ot := fun (j : Fin n) (col : Bool) (i : Nat) =>
    2*n*h+(k+9)*j.val+k+(if col then 5+i else i)
  let kt := fun (j : Fin n) (i : Fin k) => 2*n*h+(k+9)*j.val+i.val
  obtain ⟨s,tail,E,C,D,V⟩ := batch_tails (input h k start n r c key)
    (fun x => input_length h k start n r c key x) s₀ h k start n 0 (by omega)
    r c key rt ot kt
    (fun j col i hi => input_read_suffix h k start n hh r c key j col i hi)
    (fun j col i hi => input_read_obs h k start n r c key j col i hi)
    (fun j i => input_read_key h k start n r c key j i)
  have sem (x : X) (j : Fin n) (col : Bool) :
      tailValue h k start r c key j col x =
        ((word r c x j col).testBit h, (word r c x j col).testBit (h+1)) := by
    unfold tailValue replySuffix obsSuffix Select.shiftWord
    rw [hselected x j]
    exact Select.recover_selected hh hk (r x j) (c x j) col
  refine ⟨s,tail,?_,?_,?_⟩
  · simpa [s₀] using C
  · simpa [s₀] using D
  · intro j col b
    cases b with
    | false =>
      apply read_congr (V j col).1
      intro x
      simpa [sem x j col]
    | true =>
      apply read_congr (V j col).2
      intro x
      simpa [sem x j col]

end Layout40553

namespace Layout40553

open Decode (Build)
open Decode.Build
variable {X : Type*}

def stripWord (n : Nat) (r c : X → Fin n → Nat) (t : Nat) (x : X) (i : Nat) : Bool :=
  if H : t/2 < n then (word r c x ⟨t/2,H⟩ (decide (t%2=1))).testBit i else false

private theorem stripWord_pair (r c : X → Fin n → Nat) (j : Fin n) (col : Bool) (x : X) (i : Nat) :
    stripWord n r c (2*j.val+col.toNat) x i = (word r c x j col).testBit i := by
  have e : (2*j.val+col.toNat)/2 = j.val := by cases col <;> simp <;> omega
  have f : decide ((2*j.val+col.toNat)%2=1) = col := by cases col <;> simp
  simp only [stripWord,e,f,dite_eq_left j.isLt]

theorem literal_decoder (h k start n : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k)
    (r c : X → Fin n → Nat) (key : X → Fin n → Nat)
    (hselected : ∀ x j, key x j = Select.key k h start
      (Select.pick (Select.sub 5 (Select.chi (r x j).testBit) (h-5))
        (Select.sub 4 (Select.chi (c x j).testBit) (h-4)))) :
    ∃ (s : Build (2*n*h+n*(k+9))) (out : Fin n → Bool → Fin (h+2) → Nat),
      s.cost ≤ 161*n+decoderBudget (2*n) h ∧ s.depth ≤ Nat.clog 2 (h+2)+9 ∧
      ∀ j col i, Read (input h k start n r c key) s (out j col i)
        (fun x => (word r c x j col).testBit i.val) (Nat.clog 2 (h+2)+9) := by
  let inp := input h k start n r c key
  have hinp : ∀ x, (inp x).length = 2*n*h+n*(k+9) :=
    fun x => input_length h k start n r c key x
  obtain ⟨s,tail,C,D,V⟩ := literal_tails h k start n hh hk r c key hselected
  have E₀ : Ext (empty (2*n*h+n*(k+9))) s := List.nil_prefix
  let rt : Nat → Nat → Nat := fun t i =>
    2*h*(t/2)+(if decide (t%2=1) then h+i else i)
  let st : Nat → Bool → Nat := fun t b =>
    if H : t/2<n then tail ⟨t/2,H⟩ (decide (t%2=1)) b else 0
  have hj (t : Nat) (ht : t < 2*n) : t/2 < n := by omega
  have hy : ∀ t < 2*n, ∀ i < h, Read inp s (rt t i)
      (fun x => Decode.chi (stripWord n r c t x) i) 7 := by
    intro t ht i hi
    let J : Fin n := ⟨t/2,hj t ht⟩
    let col : Bool := decide (t%2=1)
    have hib : (if col then h+i else i) < 2*h := by
      cases col <;> simp_all <;> omega
    have A := input_read_y h k start n r c key J _ hib
    have B : Read inp (empty (2*n*h+n*(k+9))) (rt t i)
        (fun x => Select.chi (word r c x J col).testBit i) 0 := by
      apply read_congr A
      intro x
      exact (input_y_at h k start n r c key x J _ hib).symm.trans
        (input_reply_at h k start n r c key x J col i hi)
    have B' := read_weaken (read_persist hinp E₀ B) (by omega : 0 ≤ 7)
    apply read_congr B'
    intro x
    have eq : stripWord n r c t x = (word r c x J col).testBit := by
      funext z
      simp [stripWord,J,col,hj t ht]
    rw [eq]
    rfl
  have ht : ∀ t < 2*n, ∀ b : Bool, Read inp s (st t b)
      (fun x => stripWord n r c t x (h+b.toNat)) 7 := by
    intro t hti b
    let J : Fin n := ⟨t/2,hj t hti⟩
    let col : Bool := decide (t%2=1)
    have A := V J col b
    have B : Read inp s (tail J col b)
        (fun x => stripWord n r c t x (h+b.toNat)) 7 := by
      apply read_congr A
      intro x
      simp only [stripWord, dif_pos (hj t hti)]
      rfl
    simpa only [st, dif_pos (hj t hti)] using B
  obtain ⟨ss,outs,E,C',D',V'⟩ := finishStrips inp hinp s (2*n) h 7 (by omega)
    (stripWord n r c) rt st hy ht
  refine ⟨ss,fun j col i => outs (2*j.val+col.toNat) i.val,?_,?_,?_⟩
  · omega
  · omega
  · intro j col i
    have hpair : 2*j.val+col.toNat < 2*n := by
      have e := j.isLt
      cases col <;> simp_all <;> omega
    have A := V' (2*j.val+col.toNat) hpair i.val i.isLt
    apply read_congr (read_weaken A (by omega))
    intro x
    exact stripWord_pair r c j col x i.val

end Layout40553

namespace Replicate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def inputWire (h n : Nat) (j : Fin n) (a : Fin 4) : Nat :=
  if a.val = 0 then 2*j.val*h + h-3
  else if a.val = 1 then 2*j.val*h + h-1
  else if a.val = 2 then 2*j.val*h + h+h-2
  else 2*j.val*h + h+h-1

def remap (w : Nat) (h n : Nat) (j : Fin n) (a : Nat) : Nat :=
  if ha : a < 4 then inputWire h n j ⟨a,ha⟩ else w+13*j.val+(a-4)

def block (w h n : Nat) (j : Fin n) : List Gate :=
  Select.localCircuit.gates.map (fun g => ⟨g.op, g.inputs.map (remap w h n j)⟩)

def circuit (h n : Nat) : Circuit :=
  ⟨(List.ofFn (fun j : Fin n => block (2*n*h) h n j)).flatten, 0⟩

def keyTap (h k start n : Nat) (j : Fin n) (i : Fin k) : Nat :=
  remap (2*n*h) h n j (Select.flagTap k h start i)

@[simp] theorem block_length (w h n : Nat) (j : Fin n) : (block w h n j).length = 13 := by
  simp [block, Select.localCircuit]

@[simp] theorem circuit_length (h n : Nat) : (circuit h n).gates.length = 13*n := by
  simp only [circuit, List.length_flatten, List.map_ofFn, Function.comp_def]
  simp [block_length, Nat.mul_comm]

theorem block_fan (w h n : Nat) (j : Fin n) :
    ∀ g ∈ block w h n j, g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  simpa [block] using Select.localFan g' hg'

theorem circuit_fan (h n : Nat) : ∀ g ∈ (circuit h n).gates, g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨l,hl,hg'⟩ := List.mem_flatten.mp hg
  obtain ⟨j,_,rfl⟩ := List.mem_ofFn.mp hl
  exact block_fan _ _ _ j g hg'

theorem block_count (w h n : Nat) (j : Fin n) :
    (block w h n j).countP Select.nonlinear = 6 := by
  rfl

theorem circuit_count (h n : Nat) : (circuit h n).gates.countP Select.nonlinear = 6*n := by
  simp only [circuit, List.countP_flatten, List.map_ofFn, Function.comp_def]
  simp [block_count, Nat.mul_comm]

theorem inputWire_lt (h n : Nat) (hh : 5 ≤ h) (j : Fin n) (a : Fin 4) :
    inputWire h n j a < 2*n*h := by
  have hj0 : (j.val+1)*(2*h) ≤ n*(2*h) :=
    Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr j.isLt)
  have hj : 2*j.val*h + 2*h ≤ 2*n*h := by nlinarith only [hj0]
  fin_cases a <;> simp [inputWire] <;> omega

theorem keyTap_bound (h k start n : Nat) (hh : 5 ≤ h) (j : Fin n) (i : Fin k) :
    keyTap h k start n j i < 2*n*h+(circuit h n).gates.length := by
  have ht := Select.flagTap_bound k h start i
  norm_num [Select.localCircuit] at ht
  have hj : j.val+1 ≤ n := Nat.succ_le_iff.mpr j.isLt
  simp only [keyTap, remap, circuit_length]
  split
  · next ha =>
    have hb := inputWire_lt h n hh j ⟨_, ha⟩
    omega
  · omega

theorem gateAt_block (w h n : Nat) (j : Fin n) (t : Nat) :
    gateAt ⟨block w h n j, 0⟩ t =
      ⟨(gateAt Select.localCircuit t).op,
        (gateAt Select.localCircuit t).inputs.map (remap w h n j)⟩ := by
  simp only [gateAt, block, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hx : Select.localCircuit.gates[t]? <;> simp [hx]

theorem block_back (h n : Nat) (hh : 5 ≤ h) (j : Fin n) :
    ∀ t < (block (2*n*h) h n j).length,
    ∀ a ∈ (gateAt ⟨block (2*n*h) h n j, 0⟩ t).inputs,
      a < 2*n*h+13*j.val+t := by
  intro t ht a ha
  rw [gateAt_block] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  have ht' : t < Select.localCircuit.gates.length := by simpa [block_length, Select.localCircuit] using ht
  have hlocal := Select.localBack t ht' b hb
  by_cases hraw : b < 4
  · simp only [remap, dif_pos hraw]
    have hi := inputWire_lt h n hh j ⟨b,hraw⟩
    omega
  · simp only [remap, dif_neg hraw]
    omega

def raw (h n : Nat) (j : Fin n) (s : List Bool) : List Bool :=
  List.ofFn (fun a : Fin 4 => s.getD (inputWire h n j a) false)

@[simp] theorem raw_length (h n : Nat) (j : Fin n) (s : List Bool) : (raw h n j s).length = 4 := by
  simp [raw]

theorem remap_getD (h n m : Nat) (j : Fin n) (s z : List Bool)
    (hs : s.length = 2*n*h+13*j.val) (hz : z.length = m) (a : Nat)
    (ha : a < 4+m) (hinput : ∀ i : Fin 4, inputWire h n j i < s.length) :
    (s++z).getD (remap (2*n*h) h n j a) false =
    (raw h n j s++z).getD a false := by
  by_cases hraw : a < 4
  · simp only [remap, dif_pos hraw]
    rw [List.getD_append s z false _ (hinput ⟨a,hraw⟩)]
    rw [List.getD_append (raw h n j s) z false _ (by simpa using hraw)]
    simp only [raw, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hraw]
  · simp only [remap, dif_neg hraw]
    rw [List.getD_append_right s z false _ (by omega : s.length ≤ 2*n*h+13*j.val+(a-4))]
    rw [List.getD_append_right (raw h n j s) z false _ (by simp only [raw_length]; omega)]
    have ix : 2*n*h+13*j.val+(a-4)-s.length = a-(raw h n j s).length := by
      simp only [hs, raw_length]
      omega
    rw [ix]

def step (s : List Bool) (g : Gate) : List Bool :=
  s ++ [g.op.eval (g.inputs.map (fun a => s.getD a false))]

def mappedGate (h n : Nat) (j : Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap (2*n*h) h n j)⟩

theorem fold_remap_aux (h n m : Nat) (j : Fin n) (gs : List Gate) (s z : List Bool)
    (hs : s.length = 2*n*h+13*j.val) (hz : z.length = m)
    (hback : ∀ t < gs.length, ∀ a ∈ (gateAt ⟨gs,0⟩ t).inputs, a < 4+m+t)
    (hinput : ∀ i : Fin 4, inputWire h n j i < s.length) :
    (gs.map (mappedGate h n j)).foldl step (s++z) =
      s ++ (gs.foldl step (raw h n j s++z)).drop 4 := by
  induction gs generalizing m z with
  | nil => simp [raw_length]
  | cons g gs ih =>
    have hg : ∀ a ∈ g.inputs, a < 4+m := by
      intro a ha
      have q := hback 0 (by simp) a (by simpa [gateAt] using ha)
      simpa using q
    have he : ((g.inputs.map (remap (2*n*h) h n j)).map
          (fun a => (s++z).getD a false)) =
        g.inputs.map (fun a => (raw h n j s++z).getD a false) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact remap_getD h n m j s z hs hz a (hg a ha) hinput
    let v := g.op.eval (g.inputs.map (fun a => (raw h n j s++z).getD a false))
    have hback' : ∀ t < gs.length, ∀ a ∈ (gateAt ⟨gs,0⟩ t).inputs,
        a < 4+(m+1)+t := by
      intro t ht a ha
      have old := hback (t+1) (by simp; omega) a (by simpa [gateAt] using ha)
      omega
    have hrec := ih (m+1) (z++[v]) (by simp [hz]) hback'
    simpa only [List.map_cons, List.foldl_cons, mappedGate, step,
      he, List.append_assoc] using hrec

theorem block_wires (h n : Nat) (j : Fin n) (s : List Bool)
    (hs : s.length = 2*n*h+13*j.val)
    (hinput : ∀ i : Fin 4, inputWire h n j i < s.length) :
    (⟨block (2*n*h) h n j,0⟩ : Circuit).wires s =
      s ++ (Select.localCircuit.wires (raw h n j s)).drop 4 := by
  have hback : ∀ t < Select.localCircuit.gates.length,
      ∀ a ∈ (gateAt Select.localCircuit t).inputs, a < 4+0+t := by
    intro t ht a ha
    simpa using Select.localBack t ht a ha
  have aux := fold_remap_aux h n 0 j Select.localCircuit.gates s [] hs rfl hback hinput
  change (Select.localCircuit.gates.map (mappedGate h n j)).foldl step s =
    s ++ (Select.localCircuit.gates.foldl step (raw h n j s)).drop 4
  simpa using aux

def indexedGate (h n : Nat) (a : Fin (n*13)) : Gate :=
  let j : Fin n := ⟨a.val / 13, by have ha := a.isLt; omega⟩
  gateAt ⟨block (2*n*h) h n j,0⟩ (a.val % 13)

def indexed (h n : Nat) : Circuit := ⟨List.ofFn (indexedGate h n),0⟩

@[simp] theorem indexed_length (h n : Nat) : (indexed h n).gates.length = n*13 := by
  simp [indexed]

theorem indexed_back (h n : Nat) (hh : 5 ≤ h) : ReadsBack (2*n*h) (indexed h n) := by
  intro t ht a ha
  have ht' : t < n*13 := by simpa [indexed] using ht
  let x : Fin (n*13) := ⟨t,ht'⟩
  let j : Fin n := ⟨t/13, by omega⟩
  have ht0 : t%13 < (block (2*n*h) h n j).length := by simp [block_length, Nat.mod_lt]
  have hb := block_back h n hh j (t%13) ht0 a
  have hg : (gateAt (indexed h n) t).inputs =
      (gateAt ⟨block (2*n*h) h n j,0⟩ (t%13)).inputs := by
    simp [gateAt, indexed, indexedGate, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      ht', x, j]
  have ha' : a ∈ (gateAt ⟨block (2*n*h) h n j,0⟩ (t%13)).inputs := by
    rwa [hg] at ha
  have htdiv : 13*(t/13)+t%13=t := by omega
  specialize hb ha'
  dsimp [j] at hb
  omega

theorem indexed_eq_circuit (h n : Nat) : (indexed h n).gates = (circuit h n).gates := by
  change List.ofFn (indexedGate h n) =
    (List.ofFn (fun j : Fin n => block (2*n*h) h n j)).flatten
  rw [List.ofFn_mul]
  congr 1
  apply List.ofFn_inj.mpr
  funext j
  apply List.ext_getElem
  · simp [block_length]
  · intro t ht ht'
    have ht0 : t < 13 := by simpa using ht
    simp only [List.getElem_ofFn]
    have hd : (j.val*13+t)/13 = j.val := by omega
    have hm : (j.val*13+t)%13 = t := by omega
    simp [indexedGate, gateAt, hd, hm, List.getD_eq_getElem?_getD, ht0]

theorem circuit_back (h n : Nat) (hh : 5 ≤ h) : ReadsBack (2*n*h) (circuit h n) := by
  simpa [ReadsBack, gateAt, indexed_eq_circuit] using indexed_back h n hh

theorem circuit_valid (h n : Nat) (hh : 5 ≤ h) :
    ReadsBack (2*n*h) (circuit h n) ∧
      ∀ g ∈ (circuit h n).gates, g.inputs.length ≤ 2 :=
  ⟨circuit_back h n hh, circuit_fan h n⟩

theorem circuit_zero (h : Nat) : (circuit h 0).gates = [] := by
  rfl

theorem keyTap_zero (h k start : Nat) : ∀ j : Fin 0, ∀ i : Fin k,
    keyTap h k start 0 j i < 2*0*h+(circuit h 0).gates.length := by
  intro j
  exact j.elim0

def blocks (h n m : Nat) (hm : m ≤ n) : List Gate :=
  (List.ofFn (fun i : Fin m => block (2*n*h) h n ⟨i.val, lt_of_lt_of_le i.isLt hm⟩)).flatten

theorem blocks_succ (h n m : Nat) (hm : m+1 ≤ n) :
    blocks h n (m+1) hm =
      blocks h n m (by omega) ++ block (2*n*h) h n ⟨m,by omega⟩ := by
  simp only [blocks, List.ofFn_succ', List.concat_eq_append, List.flatten_concat]
  rfl

theorem blocks_full (h n : Nat) : blocks h n n (le_refl n) = (circuit h n).gates := by
  rfl

def run (h n m : Nat) (hm : m ≤ n) (y : List Bool) : List Bool :=
  (blocks h n m hm).foldl step y

theorem run_succ (h n m : Nat) (hm : m+1 ≤ n) (y : List Bool) :
    run h n (m+1) hm y =
      (block (2*n*h) h n ⟨m,by omega⟩).foldl step (run h n m (by omega) y) := by
  simp [run, blocks_succ, List.foldl_append]

theorem fold_step_length (gs : List Gate) (s : List Bool) :
    (gs.foldl step s).length = s.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [step]
    omega

theorem fold_step_prefix (gs : List Gate) (s : List Bool) :
    ∃ z : List Bool, gs.foldl step s = s ++ z := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨z,hz⟩ := ih (step s g)
    refine ⟨[g.op.eval (g.inputs.map (fun a => s.getD a false))] ++ z, ?_⟩
    change gs.foldl step (step s g) = _
    rw [hz]
    simp [step, List.append_assoc]

@[simp] theorem blocks_length (h n m : Nat) (hm : m ≤ n) :
    (blocks h n m hm).length = 13*m := by
  simp only [blocks, List.length_flatten, List.map_ofFn, Function.comp_def]
  simp [block_length, Nat.mul_comm]

theorem run_length (h n m : Nat) (hm : m ≤ n) (y : List Bool) :
    (run h n m hm y).length = y.length+13*m := by
  simp [run, fold_step_length, blocks_length]

theorem run_prefix (h n m : Nat) (hm : m ≤ n) (y : List Bool) :
    ∃ z : List Bool, run h n m hm y = y ++ z :=
  fold_step_prefix _ _

theorem raw_append (h n : Nat) (hh : 5 ≤ h) (j : Fin n) (y z : List Bool)
    (hy : y.length = 2*n*h) : raw h n j (y++z) = raw h n j y := by
  unfold raw
  congr 1
  funext i
  rw [List.getD_append y z false _ (by rw [hy]; exact inputWire_lt h n hh j i)]

theorem run_next (h n m : Nat) (hh : 5 ≤ h) (hm : m+1 ≤ n)
    (y : List Bool) (hy : y.length = 2*n*h) :
    run h n (m+1) hm y =
      run h n m (by omega) y ++
        (Select.localCircuit.wires (raw h n ⟨m,by omega⟩ y)).drop 4 := by
  let j : Fin n := ⟨m,by omega⟩
  let s := run h n m (by omega) y
  have hs : s.length = 2*n*h+13*j.val := by
    simp only [s, run_length, hy, j]
  have hi : ∀ i : Fin 4, inputWire h n j i < s.length := by
    intro i
    have := inputWire_lt h n hh j i
    omega
  obtain ⟨z,hz⟩ := run_prefix h n m (by omega) y
  have hr : raw h n j s = raw h n j y := by
    rw [show s = y++z from hz]
    exact raw_append h n hh j y z hy
  rw [run_succ]
  change (⟨block (2*n*h) h n j,0⟩ : Circuit).wires s = _
  rw [block_wires h n j s hs hi, hr]

theorem run_full (h n : Nat) (y : List Bool) :
    run h n n (le_refl n) y = (circuit h n).wires y := by
  change (blocks h n n (le_refl n)).foldl step y = (circuit h n).gates.foldl step y
  rw [blocks_full]

theorem run_monotone (h n m q : Nat) (hm : m ≤ q) (hq : q ≤ n) (y : List Bool) :
    ∃ z : List Bool, run h n q hq y = run h n m (by omega) y ++ z := by
  induction q, hm using Nat.le_induction with
  | base =>
    exact ⟨[], by simp⟩
  | succ q hmq ih =>
    obtain ⟨z,hz⟩ := ih (by omega)
    obtain ⟨z',hz'⟩ := fold_step_prefix
      (block (2*n*h) h n ⟨q,by omega⟩) (run h n q (by omega) y)
    refine ⟨z++z', ?_⟩
    rw [run_succ, hz', hz]
    simp [List.append_assoc]

theorem flagTap_ge_four (k h start : Nat) (i : Fin k) :
    4 ≤ Select.flagTap k h start i := by
  unfold Select.flagTap
  repeat' first | omega | split

theorem tap_stage (h k start n : Nat) (hh : 5 ≤ h) (j : Fin n)
    (y : List Bool) (hy : y.length = 2*n*h) (i : Fin k) :
    (run h n (j.val+1) (Nat.succ_le_iff.mpr j.isLt) y).getD
        (keyTap h k start n j i) false =
      (Select.localCircuit.wires (raw h n j y)).getD (Select.flagTap k h start i) false := by
  let a := Select.flagTap k h start i
  have h4 : 4 ≤ a := flagTap_ge_four k h start i
  have h17 : a < 17 := by
    have hb := Select.flagTap_bound k h start i
    norm_num [Select.localCircuit] at hb
    exact hb
  have hk : keyTap h k start n j i = 2*n*h+13*j.val+(a-4) := by
    dsimp only [a] at h4 ⊢
    simp [keyTap, remap, show ¬ Select.flagTap k h start i < 4 by omega]
  let s := run h n j.val (by omega) y
  have hs : s.length = 2*n*h+13*j.val := by simp [s, run_length, hy]
  rw [run_next h n j.val hh (Nat.succ_le_iff.mpr j.isLt) y hy]
  change (s ++ (Select.localCircuit.wires (raw h n j y)).drop 4).getD _ false = _
  rw [hk, List.getD_append_right s _ false _ (by omega)]
  have ix : 2*n*h+13*j.val+(a-4)-s.length = a-4 := by omega
  rw [ix]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have he : 4+(a-4)=a := by omega
  rw [he]

theorem tap_stage_bound (h k start n : Nat) (hh : 5 ≤ h) (j : Fin n)
    (y : List Bool) (hy : y.length = 2*n*h) (i : Fin k) :
    keyTap h k start n j i <
      (run h n (j.val+1) (Nat.succ_le_iff.mpr j.isLt) y).length := by
  have ht := Select.flagTap_bound k h start i
  norm_num [Select.localCircuit] at ht
  have h4 := flagTap_ge_four k h start i
  rw [run_length, hy]
  simp only [keyTap, remap]
  split
  · next ha =>
    have hb := inputWire_lt h n hh j ⟨_,ha⟩
    omega
  · omega

theorem tap_value (h k start n : Nat) (hh : 5 ≤ h) (j : Fin n)
    (y : List Bool) (hy : y.length = 2*n*h) (i : Fin k) :
    ((circuit h n).wires y).getD (keyTap h k start n j i) false =
      (Select.localCircuit.wires (raw h n j y)).getD (Select.flagTap k h start i) false := by
  obtain ⟨z,hz⟩ := run_monotone h n (j.val+1) n
    (Nat.succ_le_iff.mpr j.isLt) (le_refl n) y
  rw [← run_full h n y, hz]
  rw [List.getD_append (run h n (j.val+1) (by omega) y) z false _
    (tap_stage_bound h k start n hh j y hy i)]
  exact tap_stage h k start n hh j y hy i

theorem chosen_key (h k start n : Nat) (hh : 5 ≤ h) (hk : 11 ≤ k)
    (y : List Bool) (hy : y.length = 2*n*h) (r c : Fin n → List Bool)
    (hraw : ∀ j : Fin n, raw h n j y = Select.localInput (r j) (c j))
    (j : Fin n) :
    (∑ i : Fin k, if ((circuit h n).wires y).getD (keyTap h k start n j i) false
      then 2^i.val else 0) = Select.key k h start (Select.pick (r j) (c j)) := by
  change Select.buildKey k (fun i => ((circuit h n).wires y).getD
    (keyTap h k start n j i) false) = _
  have hf : (fun i : Fin k => ((circuit h n).wires y).getD
      (keyTap h k start n j i) false) =
    (fun i : Fin k => (Select.localCircuit.wires (Select.localInput (r j) (c j))).getD
      (Select.flagTap k h start i) false) := by
    funext i
    rw [tap_value h k start n hh j y hy i, hraw j]
  rw [hf]
  exact Select.localChosenKey hk (r j) (c j)

theorem chosen_mem (h k start n : Nat) (hh : 5 ≤ h) (hk : 11 ≤ k)
    (y : List Bool) (hy : y.length = 2*n*h) (r c : Fin n → List Bool)
    (hraw : ∀ j : Fin n, raw h n j y = Select.localInput (r j) (c j)) :
    ∀ j : Fin n,
    (∑ i : Fin k, if ((circuit h n).wires y).getD (keyTap h k start n j i) false
      then 2^i.val else 0) ∈ Select.menu k h start := by
  intro j
  rw [chosen_key h k start n hh hk y hy r c hraw j]
  exact Select.key_mem k h start (Select.pick (r j) (c j))

theorem flatten_getD (n m : Nat) (f : Fin n → List Bool)
    (hlen : ∀ j : Fin n, (f j).length = m) (j : Fin n) (t : Nat) (ht : t < m) :
    (List.ofFn f).flatten.getD (m*j.val+t) false = (f j).getD t false := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add, List.ofFn_succ,
        List.flatten_cons]
      rw [List.getD_append (f 0) _ false _ (by simpa [hlen 0] using ht)]
    · have htail : ∀ a : Fin n, (f a.succ).length = m := fun a => hlen a.succ
      have ih' := ih (fun a : Fin n => f a.succ) htail j
      simp only [Fin.val_succ, List.ofFn_succ, List.flatten_cons]
      rw [List.getD_append_right (f 0) _ false _ (by rw [hlen 0]; simp only [Nat.mul_add, Nat.mul_one]; omega)]
      have he : m*(j.val+1)+t-(f 0).length = m*j.val+t := by rw [hlen 0]; simp only [Nat.mul_add, Nat.mul_one]; omega
      rw [he]
      exact ih'

def reply (h u : Nat) : List Bool :=
  List.ofFn (fun i : Fin h => Select.chi u.testBit i.val)

def replyPairs (h n : Nat) (r c : Fin n → Nat) : List Bool :=
  (List.ofFn (fun j : Fin n => reply h (r j) ++ reply h (c j))).flatten

@[simp] theorem reply_length (h u : Nat) : (reply h u).length = h := by
  simp [reply]

theorem replyPairs_length (h n : Nat) (r c : Fin n → Nat) :
    (replyPairs h n r c).length = 2*n*h := by
  simp only [replyPairs, List.length_flatten, List.map_ofFn, Function.comp_def]
  simp [reply_length, two_mul, Nat.mul_add, Nat.add_mul, Nat.mul_comm]

theorem reply_get (h u t : Nat) (ht : t < h) :
    (reply h u).getD t false = Select.chi u.testBit t := by
  simp only [reply, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [ht]

theorem pair_get (h n : Nat) (r c : Fin n → Nat) (j : Fin n)
    (t : Nat) (ht : t < 2*h) :
    (replyPairs h n r c).getD ((2*h)*j.val+t) false =
      (reply h (r j) ++ reply h (c j)).getD t false := by
  exact flatten_getD n (2*h) (fun a => reply h (r a) ++ reply h (c a))
    (by intro a; simp [reply_length, two_mul]) j t ht

theorem pair_row (h n : Nat) (r c : Fin n → Nat) (j : Fin n)
    (t : Nat) (ht : t < h) :
    (replyPairs h n r c).getD (2*j.val*h+t) false = Select.chi (r j).testBit t := by
  have he : 2*j.val*h+t = (2*h)*j.val+t := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [he, pair_get h n r c j t (by omega)]
  rw [List.getD_append (reply h (r j)) _ false _ (by simpa [reply_length] using ht)]
  exact reply_get h (r j) t ht

theorem pair_col (h n : Nat) (r c : Fin n → Nat) (j : Fin n)
    (t : Nat) (ht : t < h) :
    (replyPairs h n r c).getD (2*j.val*h+h+t) false = Select.chi (c j).testBit t := by
  have he : 2*j.val*h+h+t = (2*h)*j.val+(h+t) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
  rw [he, pair_get h n r c j (h+t) (by omega)]
  rw [List.getD_append_right (reply h (r j)) _ false _ (by simp [reply_length])]
  have hx : h+t-(reply h (r j)).length = t := by simp [reply_length]
  rw [hx]
  exact reply_get h (c j) t ht

theorem raw_pairs (h n : Nat) (hh : 5 ≤ h) (r c : Fin n → Nat) (j : Fin n) :
    raw h n j (replyPairs h n r c) =
      Select.localInput
        (Select.sub 5 (Select.chi (r j).testBit) (h-5))
        (Select.sub 4 (Select.chi (c j).testBit) (h-4)) := by
  let y := replyPairs h n r c
  let ry := Select.sub 5 (Select.chi (r j).testBit) (h-5)
  let cy := Select.sub 4 (Select.chi (c j).testBit) (h-4)
  have h0 : y.getD (inputWire h n j 0) false = ry.getD 2 false := by
    change y.getD (2*j.val*h+h-3) false = _
    have he : 2*j.val*h+h-3 = 2*j.val*h+(h-3) := by omega
    rw [he, pair_row h n r c j (h-3) (by omega), Select.sub_get 5 _ (h-5) 2 (by decide)]
    congr 1; omega
  have h1 : y.getD (inputWire h n j 1) false = ry.getD 4 false := by
    change y.getD (2*j.val*h+h-1) false = _
    have he : 2*j.val*h+h-1 = 2*j.val*h+(h-1) := by omega
    rw [he, pair_row h n r c j (h-1) (by omega), Select.sub_get 5 _ (h-5) 4 (by decide)]
    congr 1; omega
  have h2 : y.getD (inputWire h n j 2) false = cy.getD 2 false := by
    change y.getD (2*j.val*h+h+h-2) false = _
    have he : 2*j.val*h+h+h-2 = 2*j.val*h+h+(h-2) := by omega
    rw [he, pair_col h n r c j (h-2) (by omega), Select.sub_get 4 _ (h-4) 2 (by decide)]
    congr 1; omega
  have h3 : y.getD (inputWire h n j 3) false = cy.getD 3 false := by
    change y.getD (2*j.val*h+h+h-1) false = _
    have he : 2*j.val*h+h+h-1 = 2*j.val*h+h+(h-1) := by omega
    rw [he, pair_col h n r c j (h-1) (by omega), Select.sub_get 4 _ (h-4) 3 (by decide)]
    congr 1; omega
  change [y.getD (inputWire h n j 0) false, y.getD (inputWire h n j 1) false,
      y.getD (inputWire h n j 2) false, y.getD (inputWire h n j 3) false] =
    [ry.getD 2 false, ry.getD 4 false, cy.getD 2 false, cy.getD 3 false]
  simp only [List.cons.injEq, and_true]
  exact ⟨h0,h1,h2,h3⟩

theorem pairs_chosen_key (h k start n : Nat) (hh : 5 ≤ h) (hk : 11 ≤ k)
    (r c : Fin n → Nat) (j : Fin n) :
    (∑ i : Fin k, if ((circuit h n).wires (replyPairs h n r c)).getD
      (keyTap h k start n j i) false then 2^i.val else 0) =
      Select.key k h start
        (Select.pick
          (Select.sub 5 (Select.chi (r j).testBit) (h-5))
          (Select.sub 4 (Select.chi (c j).testBit) (h-4))) := by
  exact chosen_key h k start n hh hk (replyPairs h n r c) (replyPairs_length h n r c)
    (fun j => Select.sub 5 (Select.chi (r j).testBit) (h-5))
    (fun j => Select.sub 4 (Select.chi (c j).testBit) (h-4))
    (raw_pairs h n hh r c) j

theorem pairs_chosen_mem (h k start n : Nat) (hh : 5 ≤ h) (hk : 11 ≤ k)
    (r c : Fin n → Nat) :
    ∀ j : Fin n,
    (∑ i : Fin k, if ((circuit h n).wires (replyPairs h n r c)).getD
      (keyTap h k start n j i) false then 2^i.val else 0) ∈ Select.menu k h start := by
  intro j
  rw [pairs_chosen_key h k start n hh hk r c j]
  exact Select.key_mem k h start _

def rawNat (h n : Nat) (j : Fin n) (s : List Nat) : List Nat :=
  List.ofFn (fun a : Fin 4 => s.getD (inputWire h n j a) 0)

@[simp] theorem rawNat_length (h n : Nat) (j : Fin n) (s : List Nat) :
    (rawNat h n j s).length = 4 := by simp [rawNat]

theorem remap_getD_nat (h n m : Nat) (j : Fin n) (s z : List Nat)
    (hs : s.length = 2*n*h+13*j.val) (hz : z.length = m) (a : Nat)
    (ha : a < 4+m) (hinput : ∀ i : Fin 4, inputWire h n j i < s.length) :
    (s++z).getD (remap (2*n*h) h n j a) 0 =
    (rawNat h n j s++z).getD a 0 := by
  by_cases hraw : a < 4
  · simp only [remap, dif_pos hraw]
    rw [List.getD_append s z 0 _ (hinput ⟨a,hraw⟩)]
    rw [List.getD_append (rawNat h n j s) z 0 _ (by simpa using hraw)]
    simp only [rawNat, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hraw]
  · simp only [remap, dif_neg hraw]
    rw [List.getD_append_right s z 0 _ (by omega : s.length ≤ 2*n*h+13*j.val+(a-4))]
    rw [List.getD_append_right (rawNat h n j s) z 0 _ (by simp only [rawNat_length]; omega)]
    have ix : 2*n*h+13*j.val+(a-4)-s.length = a-(rawNat h n j s).length := by
      simp only [hs, rawNat_length]
      omega
    rw [ix]

def depthStep (ds : List Nat) (g : Gate) : List Nat :=
  ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (Select.nonlinear g).toNat]

theorem nonlinear_map (h n : Nat) (j : Fin n) (g : Gate) :
    Select.nonlinear (mappedGate h n j g) = Select.nonlinear g := by
  simp [Select.nonlinear, mappedGate]

theorem fold_remap_depth_aux (h n m : Nat) (j : Fin n) (gs : List Gate)
    (s z : List Nat) (hs : s.length = 2*n*h+13*j.val) (hz : z.length = m)
    (hback : ∀ t < gs.length, ∀ a ∈ (gateAt ⟨gs,0⟩ t).inputs, a < 4+m+t)
    (hinput : ∀ i : Fin 4, inputWire h n j i < s.length) :
    (gs.map (mappedGate h n j)).foldl depthStep (s++z) =
      s ++ (gs.foldl depthStep (rawNat h n j s++z)).drop 4 := by
  induction gs generalizing m z with
  | nil => simp [rawNat_length]
  | cons g gs ih =>
    have hg : ∀ a ∈ g.inputs, a < 4+m := by
      intro a ha
      have q := hback 0 (by simp) a (by simpa [gateAt] using ha)
      simpa using q
    have he : ((g.inputs.map (remap (2*n*h) h n j)).map
          (fun a => (s++z).getD a 0)) =
        g.inputs.map (fun a => (rawNat h n j s++z).getD a 0) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact remap_getD_nat h n m j s z hs hz a (hg a ha) hinput
    let v := (g.inputs.map (fun a => (rawNat h n j s++z).getD a 0)).foldr max 0 +
      (Select.nonlinear g).toNat
    have hv : depthStep (s++z) (mappedGate h n j g) = s ++ (z++[v]) := by
      simp only [depthStep, mappedGate, Gate.inputs, Gate.op]
      rw [he]
      simp only [List.append_assoc]
      congr 1
      simp [v, Select.nonlinear]
    have hback' : ∀ t < gs.length, ∀ a ∈ (gateAt ⟨gs,0⟩ t).inputs,
        a < 4+(m+1)+t := by
      intro t ht a ha
      have old := hback (t+1) (by simp; omega) a (by simpa [gateAt] using ha)
      omega
    have hrec := ih (m+1) (z++[v]) (by simp [hz]) hback'
    have hvlocal : depthStep (rawNat h n j s++z) g = rawNat h n j s ++ (z++[v]) := by
      simp [depthStep, v, List.append_assoc]
    simpa only [List.map_cons, List.foldl_cons, hv, hvlocal, List.append_assoc] using hrec

theorem block_depths (h n : Nat) (j : Fin n) (s : List Nat)
    (hs : s.length = 2*n*h+13*j.val)
    (hi : ∀ i : Fin 4, inputWire h n j i < s.length) :
    (block (2*n*h) h n j).foldl depthStep s =
      s ++ (Select.localCircuit.gates.foldl depthStep (rawNat h n j s)).drop 4 := by
  have hback : ∀ t < Select.localCircuit.gates.length,
      ∀ a ∈ (gateAt Select.localCircuit t).inputs, a < 4+0+t := by
    intro t ht a ha
    simpa using Select.localBack t ht a ha
  have aux := fold_remap_depth_aux h n 0 j Select.localCircuit.gates s [] hs rfl hback hi
  change (Select.localCircuit.gates.map (mappedGate h n j)).foldl depthStep s =
    s ++ (Select.localCircuit.gates.foldl depthStep (rawNat h n j s)).drop 4
  simpa using aux

def levels : List Nat := [0,1,0,1,1,2,0,1,2,2,2,3,3]

theorem local_levels :
    (Select.localCircuit.gates.foldl depthStep (List.replicate 4 0)).drop 4 = levels := by
  decide

def depthTail : Nat → List Nat
  | 0 => []
  | m+1 => depthTail m ++ levels

@[simp] theorem depthTail_length (m : Nat) : (depthTail m).length = 13*m := by
  induction m with
  | zero => simp [depthTail]
  | succ m ih => simp [depthTail, levels, ih, Nat.mul_add]

def depthRun (h n m : Nat) (hm : m ≤ n) : List Nat :=
  (blocks h n m hm).foldl depthStep (List.replicate (2*n*h) 0)

theorem depthRun_succ (h n m : Nat) (hm : m+1 ≤ n) :
    depthRun h n (m+1) hm =
      (block (2*n*h) h n ⟨m,by omega⟩).foldl depthStep (depthRun h n m (by omega)) := by
  simp [depthRun, blocks_succ, List.foldl_append]

theorem rawNat_base (h n : Nat) (hh : 5 ≤ h) (j : Fin n) (z : List Nat) :
    rawNat h n j (List.replicate (2*n*h) 0 ++ z) = List.replicate 4 0 := by
  have hz (a : Fin 4) :
      (List.replicate (2*n*h) 0 ++ z).getD (inputWire h n j a) 0 = 0 := by
    rw [List.getD_append _ z 0 _ (by simpa using inputWire_lt h n hh j a)]
    exact List.getD_replicate 0 (inputWire_lt h n hh j a)
  change (List.ofFn (fun a : Fin 4 =>
    (List.replicate (2*n*h) 0 ++ z).getD (inputWire h n j a) 0)) = List.replicate 4 0
  simp_rw [hz]
  rfl

theorem depthRun_exact (h n m : Nat) (hh : 5 ≤ h) (hm : m ≤ n) :
    depthRun h n m hm = List.replicate (2*n*h) 0 ++ depthTail m := by
  induction m with
  | zero => simp [depthRun, blocks, depthTail]
  | succ m ih =>
    let j : Fin n := ⟨m,by omega⟩
    let s := depthRun h n m (by omega)
    have hz : s = List.replicate (2*n*h) 0 ++ depthTail m := ih (by omega)
    have hs : s.length = 2*n*h+13*j.val := by simp [hz, j]
    have hi : ∀ i : Fin 4, inputWire h n j i < s.length := by
      intro i
      have hx := inputWire_lt h n hh j i
      omega
    rw [depthRun_succ]
    change (block (2*n*h) h n j).foldl depthStep s = _
    rw [block_depths h n j s hs hi, hz,
      rawNat_base h n hh j (depthTail m), local_levels]
    simp [depthTail, List.append_assoc]

theorem levels_le : ∀ a ∈ levels, a ≤ 3 := by decide

theorem depthTail_le (m : Nat) : ∀ a ∈ depthTail m, a ≤ 3 := by
  induction m with
  | zero => simp [depthTail]
  | succ m ih =>
    intro a ha
    obtain hm | hl := List.mem_append.mp (by simpa only [depthTail] using ha)
    · exact ih a hm
    · exact levels_le a hl

theorem foldr_max_le (l : List Nat) (hl : ∀ a ∈ l, a ≤ 3) :
    l.foldr max 0 ≤ 3 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    apply max_le (hl a (by simp))
    exact ih (by intro b hb; exact hl b (by simp [hb]))

theorem circuit_depth_le (h n : Nat) (hh : 5 ≤ h) :
    Select.depth (2*n*h) (circuit h n) ≤ 3 := by
  change ((circuit h n).gates.foldl depthStep (List.replicate (2*n*h) 0)).foldr max 0 ≤ 3
  have he : (circuit h n).gates.foldl depthStep (List.replicate (2*n*h) 0) =
      List.replicate (2*n*h) 0 ++ depthTail n := by
    simpa [depthRun, blocks_full] using depthRun_exact h n n hh (le_refl n)
  rw [he]
  apply foldr_max_le
  intro a ha
  obtain hr | ht := List.mem_append.mp ha
  · simp at hr
    omega
  · exact depthTail_le n a ht

end Replicate

namespace LowerInv

def chi (u : Nat → Bool) (i : Nat) : Bool :=
  xor (u i) (!(u (i + 1)) && u (i + 2))

private def push (b : Bool) (r : Nat) : Nat :=
  (r <<< 1) ||| b.toNat

private theorem push_zero (b : Bool) (r : Nat) : (push b r).testBit 0 = b := by
  cases b <;> simp [push]

private theorem push_succ (b : Bool) (r i : Nat) :
    (push b r).testBit (i + 1) = r.testBit i := by
  have hb : b.toNat.testBit (i + 1) = false := by
    rw [Nat.testBit_add_one]
    cases b <;> exact Nat.zero_testBit _
  simp [push, hb]

private def oddBit (z : Bool) (r : Nat) : Bool :=
  xor (!z) (!(r.testBit 0) && r.testBit 1)

private def pair (z : Bool) (r : Nat) : Nat :=
  push (!(oddBit z r) && r.testBit 0) (push (oddBit z r) r)

private theorem pair_shift (z : Bool) (r i : Nat) :
    (pair z r).testBit (i + 2) = r.testBit i := by
  change (pair z r).testBit ((i + 1) + 1) = _
  simp only [pair, push_succ]

private theorem pair_chi_zero (z : Bool) (r : Nat) :
    chi (pair z r).testBit 0 = false := by
  simp only [chi, pair, push_zero, push_succ]
  exact Bool.xor_self _

private theorem pair_chi_one (z : Bool) (r : Nat) :
    chi (pair z r).testBit 1 = !z := by
  simp only [chi, pair, push_zero, push_succ, oddBit]
  have cancel : ∀ a b : Bool, xor (xor a b) b = a := by decide
  exact cancel _ _

private theorem pair_chi_shift (z : Bool) (r i : Nat) :
    chi (pair z r).testBit (i + 2) = chi r.testBit i := by
  simp only [chi, show i + 2 + 1 = (i + 1) + 2 by omega, pair_shift]

private theorem pair_zero (z : Bool) (r : Nat) :
    (pair z r).testBit 0 = (z && r.testBit 0) := by
  simp only [pair, push_zero, oddBit]
  have step : ∀ a b c : Bool, (!(xor (!a) (!b && c)) && b) = (a && b) := by decide
  exact step _ _ _

def raw (x : Nat → Bool) : Nat → Nat
  | 0 => 1
  | m + 1 => pair (x 0) (raw (fun j => x (j + 1)) m)

theorem raw_tail (x : Nat → Bool) (m i : Nat) (hi : 2 * m < i) :
    (raw x m).testBit i = false := by
  induction m generalizing x i with
  | zero =>
    change (1 : Nat).testBit i = false
    cases i with
    | zero => omega
    | succ i => rw [Nat.testBit_succ]; exact Nat.zero_testBit _
  | succ m ih =>
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    rw [raw, pair_shift]
    exact ih _ _ (by omega)

theorem chi_tip (x : Nat → Bool) (m : Nat) :
    chi (raw x m).testBit (2 * m) = true := by
  induction m generalizing x with
  | zero =>
    simp only [raw, Nat.mul_zero]
    decide
  | succ m ih =>
    rw [raw, show 2 * (m + 1) = 2 * m + 2 by omega, pair_chi_shift]
    exact ih _

theorem chi_even (x : Nat → Bool) (m j : Nat) (hj : j < m) :
    chi (raw x m).testBit (2 * j) = false := by
  induction m generalizing x j with
  | zero => omega
  | succ m ih =>
    cases j with
    | zero => exact pair_chi_zero _ _
    | succ j =>
      rw [raw, show 2 * (j + 1) = (2 * j) + 2 by omega, pair_chi_shift]
      exact ih _ _ (by omega)

theorem chi_odd (x : Nat → Bool) (m j : Nat) (hj : j < m) :
    chi (raw x m).testBit (2 * j + 1) = !(x j) := by
  induction m generalizing x j with
  | zero => omega
  | succ m ih =>
    cases j with
    | zero => exact pair_chi_one _ _
    | succ j =>
      rw [raw, show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, pair_chi_shift]
      exact ih _ _ (by omega)

theorem chi_tail (x : Nat → Bool) (m i : Nat) (hi : 2 * m < i) :
    chi (raw x m).testBit i = false := by
  rw [chi, raw_tail x m i hi, raw_tail x m (i + 1) (by omega),
    raw_tail x m (i + 2) (by omega)]
  rfl

private theorem decide_all_succ (x : Nat → Bool) (m : Nat) :
    decide (∀ j < m + 1, x j = true) =
      (x 0 && decide (∀ j < m, x (j + 1) = true)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨h 0 (by omega), fun j hj => h (j + 1) (by omega)⟩
  · rintro ⟨h0, hs⟩ j hj
    cases j with
    | zero => exact h0
    | succ j => exact hs j (by omega)

theorem raw_lsb (x : Nat → Bool) (m : Nat) :
    (raw x m).testBit 0 = decide (∀ j < m, x j = true) := by
  induction m generalizing x with
  | zero => simp [raw]
  | succ m ih => rw [raw, pair_zero, ih, decide_all_succ]

theorem raw_lt (x : Nat → Bool) (m : Nat) : raw x m < 2 ^ (2 * m + 1) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  exact raw_tail x m i (by omega)

def strip (x : Nat → Bool) (m : Nat) : Fin (2 ^ ((2 * m + 6) + 2)) :=
  ⟨raw x m, Nat.lt_of_lt_of_le (raw_lt x m)
    (Nat.pow_le_pow_of_le (by decide) (by omega))⟩

theorem restrictedInverse (x : Nat → Bool) (m : Nat) :
    let h := 2 * m + 6
    ∃ R : Fin (2 ^ (h + 2)),
      (∀ i, 2 * m < i → R.val.testBit i = false) ∧
      chi R.val.testBit (2 * m) = true ∧
      (∀ j < m, chi R.val.testBit (2 * j) = false) ∧
      (∀ j < m, chi R.val.testBit (2 * j + 1) = !(x j)) ∧
      (∀ i, 2 * m < i → chi R.val.testBit i = false) ∧
      R.val.testBit 0 = decide (∀ j < m, x j = true) :=
  ⟨strip x m, raw_tail x m, chi_tip x m, chi_even x m, chi_odd x m,
    chi_tail x m, raw_lsb x m⟩

abbrev inv (m : Nat) (x : Nat → Bool) : Fin (2 ^ (2 * m + 6 + 2)) := strip x m

theorem inv_tail (m : Nat) (x : Nat → Bool) (i : Nat) (hi : 2 * m < i) :
    (inv m x).val.testBit i = false :=
  raw_tail x m i hi

theorem inv_bit_zero (m : Nat) (x : Nat → Bool) :
    (inv m x).val.testBit 0 = decide (∀ j : Fin m, x j = true) := by
  change (raw x m).testBit 0 = _
  rw [raw_lsb]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨fun h j => h j.val j.isLt, fun h j hj => h ⟨j, hj⟩⟩

theorem inv_reply (m : Nat) (x : Nat → Bool) (i : Nat) :
    chi (inv m x).val.testBit i =
      if i = 2 * m then true else if i < 2 * m ∧ i % 2 = 1 then !(x (i / 2)) else false := by
  change chi (raw x m).testBit i = _
  by_cases he : i = 2 * m
  · rw [ite_eq_left he, he]
    exact chi_tip x m
  rw [ite_eq_right he]
  by_cases hi : i < 2 * m
  · by_cases ho : i % 2 = 1
    · rw [ite_eq_left ⟨hi, ho⟩]
      calc
        chi (raw x m).testBit i = chi (raw x m).testBit (2 * (i / 2) + 1) :=
          congrArg (chi (raw x m).testBit) (by omega)
        _ = !(x (i / 2)) := chi_odd x m (i / 2) (by omega)
    · rw [ite_eq_right (fun h => ho h.2)]
      calc
        chi (raw x m).testBit i = chi (raw x m).testBit (2 * (i / 2)) :=
          congrArg (chi (raw x m).testBit) (by omega)
        _ = false := chi_even x m (i / 2) (by omega)
  · rw [ite_eq_right (fun h => hi h.1)]
    exact chi_tail x m i (by omega)

end LowerInv

namespace L40553Lower

open scoped BigOperators

private def bit (b : Bool) : ZMod 2 := if b then 1 else 0

private def mon (x : Nat → Bool) (s : Finset Nat) : ZMod 2 :=
  if ∀ i ∈ s, x i = true then 1 else 0

private def value (x : Nat → Bool) : List (Finset Nat) → ZMod 2
  | [] => 0
  | s :: p => mon x s + value x p

def Deg (d : Nat) (f : (Nat → Bool) → Bool) : Prop :=
  ∃ p : List (Finset Nat), (∀ s ∈ p, s.card ≤ d) ∧ ∀ x, value x p = bit (f x)

private theorem mon_empty (x : Nat → Bool) : mon x ∅ = 1 := by
  simp [mon]

private theorem mon_singleton (x : Nat → Bool) (i : Nat) : mon x {i} = bit (x i) := by
  simp [mon, bit]

private theorem bit_xor (a b : Bool) : bit (xor a b) = bit a + bit b := by
  cases a <;> cases b <;> decide

private theorem bit_and (a b : Bool) : bit (a && b) = bit a * bit b := by
  cases a <;> cases b <;> decide

private theorem mon_union (x : Nat → Bool) (s t : Finset Nat) :
    mon x (s ∪ t) = mon x s * mon x t := by
  have h : (∀ i ∈ s ∪ t, x i = true) ↔ (∀ i ∈ s, x i = true) ∧ (∀ i ∈ t, x i = true) := by
    simp only [Finset.mem_union]
    exact ⟨fun h => ⟨fun i hi => h i (.inl hi), fun i hi => h i (.inr hi)⟩,
      fun h i hi => hi.elim (h.1 i) (h.2 i)⟩
  simp only [mon, h]
  by_cases hs : ∀ i ∈ s, x i = true
  · by_cases ht : ∀ i ∈ t, x i = true
    · rw [ite_eq_left hs, ite_eq_left ht, ite_eq_left ⟨hs, ht⟩, mul_one]
    · rw [ite_eq_left hs, ite_eq_right ht, ite_eq_right (fun hst => ht hst.2), mul_zero]
  · rw [ite_eq_right hs, ite_eq_right (fun hst => hs hst.1), zero_mul]

private theorem value_append (x : Nat → Bool) (p q : List (Finset Nat)) :
    value x (p ++ q) = value x p + value x q := by
  induction p with
  | nil => simp [value]
  | cons s p ih => simp [value, ih, add_assoc]

private theorem value_map_union (x : Nat → Bool) (s : Finset Nat) (q : List (Finset Nat)) :
    value x (q.map (fun t => s ∪ t)) = mon x s * value x q := by
  induction q with
  | nil => simp [value]
  | cons t q ih => simp [value, mon_union, ih, mul_add]

private theorem value_flatMap_union (x : Nat → Bool) (p q : List (Finset Nat)) :
    value x (p.flatMap (fun s => q.map (fun t => s ∪ t))) = value x p * value x q := by
  induction p with
  | nil => simp [value]
  | cons s p ih => simp [value, value_append, value_map_union, ih, add_mul]

theorem deg_const (d : Nat) (b : Bool) : Deg d (fun _ => b) := by
  cases b with
  | false => exact ⟨[], by simp, fun _ => rfl⟩
  | true => exact ⟨[∅], by simp, fun x => by simp [value, mon_empty, bit]⟩

theorem deg_coord (i : Nat) : Deg 1 (fun x => x i) := by
  exact ⟨[{i}], by simp, fun x => by simp [value, mon_singleton]⟩

variable {d e m : Nat} {f g : (Nat → Bool) → Bool}

theorem deg_mono (h : d ≤ e) : Deg d f → Deg e f := by
  rintro ⟨p, hp, heval⟩
  exact ⟨p, fun s hs => (hp s hs).trans h, heval⟩

theorem deg_xor : Deg d f → Deg d g → Deg d (fun x => xor (f x) (g x)) := by
  rintro ⟨p, hp, hpx⟩ ⟨q, hq, hqx⟩
  refine ⟨p ++ q, ?_, fun x => by rw [value_append, hpx, hqx, bit_xor]⟩
  intro s hs
  exact (List.mem_append.mp hs).elim (hp s) (hq s)

theorem deg_and : Deg d f → Deg e g → Deg (d + e) (fun x => f x && g x) := by
  rintro ⟨p, hp, hpx⟩ ⟨q, hq, hqx⟩
  refine ⟨p.flatMap (fun s => q.map (fun t => s ∪ t)), ?_,
    fun x => by rw [value_flatMap_union, hpx, hqx, bit_and]⟩
  intro u hu
  obtain ⟨s, hs, hu⟩ := List.mem_flatMap.mp hu
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
  exact (Finset.card_union_le s t).trans (Nat.add_le_add (hp s hs) (hq t ht))

private def extend (a : Fin m → Bool) (i : Nat) : Bool :=
  if hi : i < m then a ⟨i, hi⟩ else false

private theorem extend_fin (a : Fin m → Bool) (i : Fin m) : extend a i = a i := by
  simp [extend, i.isLt]

private def flip (j : Fin m) (a : Fin m → Bool) (i : Fin m) : Bool :=
  if i = j then !(a i) else a i

private theorem flip_flip (j : Fin m) (a : Fin m → Bool) : flip j (flip j a) = a := by
  funext i
  by_cases h : i = j <;> simp [flip, h]

private theorem flip_ne (j : Fin m) (a : Fin m → Bool) : flip j a ≠ a := by
  intro h
  have h' := congrFun h j
  cases hj : a j <;> simp [flip, hj] at h'

private theorem mon_flip (s : Finset Nat) (j : Fin m) (hj : (j : Nat) ∉ s) (a : Fin m → Bool) :
    mon (extend (flip j a)) s = mon (extend a) s := by
  have h : ∀ i ∈ s, extend (flip j a) i = extend a i := by
    intro i hi
    by_cases him : i < m
    · have hij : (⟨i, him⟩ : Fin m) ≠ j := by
        intro he
        exact hj (congrArg Fin.val he ▸ hi)
      simp [extend, him, flip, hij]
    · simp [extend, him]
  have he : (∀ i ∈ s, extend (flip j a) i = true) ↔ (∀ i ∈ s, extend a i = true) :=
    ⟨fun hp i hi => (h i hi).symm.trans (hp i hi), fun hp i hi => (h i hi).trans (hp i hi)⟩
  simp only [mon, he]

private theorem sum_mon_of_card_lt (s : Finset Nat) (hs : s.card < m) :
    (∑ a : Fin m → Bool, mon (extend a) s) = 0 := by
  have hex : ∃ j : Fin m, (j : Nat) ∉ s := by
    by_contra h
    have hsub : Finset.range m ⊆ s := by
      intro i hi
      by_contra his
      exact h ⟨⟨i, Finset.mem_range.mp hi⟩, his⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_range] at hle
    exact (Nat.not_le_of_lt hs) hle
  obtain ⟨j, hj⟩ := hex
  refine Finset.sum_ninvolution (flip j) ?_ (fun a _ => flip_ne j a) (fun _ => Finset.mem_univ _) (flip_flip j)
  intro a
  rw [mon_flip s j hj]
  exact ZModModule.add_self _

private theorem sum_value_of_card_lt (p : List (Finset Nat)) (hp : ∀ s ∈ p, s.card < m) :
    (∑ a : Fin m → Bool, value (extend a) p) = 0 := by
  induction p with
  | nil => simp [value]
  | cons s p ih =>
    simp only [value, Finset.sum_add_distrib]
    rw [sum_mon_of_card_lt s (hp s (List.mem_cons_self ..)), ih, add_zero]
    exact fun t ht => hp t (List.mem_cons_of_mem _ ht)

private theorem sum_and (m : Nat) :
    (∑ a : Fin m → Bool, bit (decide (∀ j : Fin m, extend a j = true))) = 1 := by
  rw [Finset.sum_eq_single (fun _ => true)]
  · simp [extend_fin, bit]
  · intro a _ ha
    have h : ¬ ∀ j : Fin m, a j = true := by
      intro h
      exact ha (funext h)
    simp [extend_fin, bit, h]
  · simp

theorem le_deg_and (h : Deg d (fun x => decide (∀ j : Fin m, x j = true))) : m ≤ d := by
  by_contra hmd
  obtain ⟨p, hp, hval⟩ := h
  have hzero := sum_value_of_card_lt p (fun s hs => (hp s hs).trans_lt (Nat.lt_of_not_ge hmd))
  simp_rw [hval] at hzero
  rw [sum_and] at hzero
  exact one_ne_zero hzero

end L40553Lower

namespace L40553Lower

open PEqualNP.CircuitLowerBounds

def nonlinear (g : Gate) : Bool := (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

def dStep (ds : List Nat) (g : Gate) : List Nat :=
  ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat]

def depth (w : Nat) (C : Circuit) : Nat :=
  (C.gates.foldl dStep (List.replicate w 0)).foldr max 0

private theorem unExp (a b x : Bool) :
    (if x then b else a) = xor a (xor a b && x) := by
  cases a <;> cases b <;> cases x <;> rfl

private theorem binExp (a b c d x y : Bool) :
    (if x then (if y then d else c) else (if y then b else a)) =
      xor (xor a (xor a c && x))
        (xor (xor a b && y) (xor (xor a b) (xor c d) && (x && y))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> cases y <;> rfl

private theorem ux (op : GateOp) (x : Bool) : op.eval [x] =
    xor (op.eval [false]) (xor (op.eval [false]) (op.eval [true]) && x) := by
  convert unExp (op.eval [false]) (op.eval [true]) x using 1
  cases x <;> rfl

private theorem bx (op : GateOp) (x y : Bool) : op.eval [x,y] =
    xor (xor (op.eval [false,false]) (xor (op.eval [false,false]) (op.eval [true,false]) && x))
        (xor (xor (op.eval [false,false]) (op.eval [false,true]) && y)
          (xor (xor (op.eval [false,false]) (op.eval [false,true]))
               (xor (op.eval [true,false]) (op.eval [true,true])) && (x && y))) := by
  convert binExp (op.eval [false,false]) (op.eval [false,true]) (op.eval [true,false])
    (op.eval [true,true]) x y using 1
  cases x <;> cases y <;> rfl

private theorem getD_foldr_max (ds : List Nat) (i : Nat) : ds.getD i 0 ≤ ds.foldr max 0 := by
  induction ds generalizing i with
  | nil => simp
  | cons v vs ih =>
    cases i with
    | zero => exact le_max_left _ _
    | succ i => exact (ih i).trans (le_max_right _ _)

private theorem mem_foldr_max (ds : List Nat) (j : Nat) (hj : j ∈ ds) : j ≤ ds.foldr max 0 := by
  induction ds with
  | nil => simp at hj
  | cons a ds ih =>
    rcases List.mem_cons.mp hj with rfl | hj
    · exact le_max_left _ _
    · exact (ih hj).trans (le_max_right _ _)

private theorem deg_gate (ds : List Nat) (w : (Nat → Bool) → List Bool) (base : Nat)
    (hw : ∀ i, Deg (base*2^(ds.getD i 0)) (fun x => (w x).getD i false))
    (g : Gate) (hg : g.inputs.length ≤ 2) :
    Deg (base*2^((g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat))
      (fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)) := by
  let l := (g.inputs.map (fun a => ds.getD a 0)).foldr max 0
  let d₀ := base*2^l
  have hwire (i : Nat) (hi : i ∈ g.inputs) : Deg d₀ (fun x => (w x).getD i false) := by
    apply deg_mono _ (hw i)
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by decide)
    exact mem_foldr_max _ _ (List.mem_map_of_mem hi)
  let B := fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)
  change Deg (base*2^(l+(nonlinear g).toNat)) B
  have left_le : d₀ ≤ base*2^(l+(nonlinear g).toNat) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))
  have dx (a : Bool) {f : (Nat → Bool) → Bool} (hf : Deg d₀ f) :
      Deg d₀ (fun x => a && f x) := by
    cases a
    · simpa only [Bool.false_and] using deg_const d₀ false
    · simpa only [Bool.true_and] using hf
  cases hi : g.inputs with
  | nil =>
    exact (show Deg _ B by simpa only [B, hi, List.map_nil] using deg_const _ (g.op.eval []))
  | cons a as =>
    have ha : Deg d₀ (fun x => (w x).getD a false) := hwire a (by rw [hi]; simp)
    cases as with
    | nil =>
      apply deg_mono left_le
      have h := deg_xor (deg_const d₀ (g.op.eval [false]))
          (dx (xor (g.op.eval [false]) (g.op.eval [true])) ha)
      convert h using 1
      funext x
      simpa only [B, hi, List.map_cons, List.map_nil] using ux g.op ((w x).getD a false)
    | cons b bs =>
      have hb : Deg d₀ (fun x => (w x).getD b false) := hwire b (by rw [hi]; simp)
      have hs : bs = [] := List.length_eq_zero_iff.mp (by simpa [hi] using hg)
      subst bs
      let q := xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
                   (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
      have hq : nonlinear g = q := by simp [nonlinear, hi, q]
      have hlin := deg_xor (deg_const d₀ (g.op.eval [false,false]))
        (dx (xor (g.op.eval [false,false]) (g.op.eval [true,false])) ha)
      have hlin' := dx (xor (g.op.eval [false,false]) (g.op.eval [false,true])) hb
      have hprod : Deg (base*2^(l+(nonlinear g).toNat))
          (fun x => q && ((w x).getD a false && (w x).getD b false)) := by
        cases hq' : q with
        | false => simpa only [hq', Bool.false_and] using deg_const _ false
        | true =>
          rw [hq, hq']
          have eq : base*2^(l+1) = d₀+d₀ := by simp [d₀, pow_succ, Nat.mul_add, Nat.mul_two]
          simpa only [hq', Bool.true_and, Bool.toNat_true, eq] using deg_and ha hb
      have h := deg_xor (deg_mono left_le hlin) (deg_xor (deg_mono left_le hlin') hprod)
      convert h using 1
      funext x
      simpa only [B, hi, List.map_cons, List.map_nil, q] using
        bx g.op ((w x).getD a false) ((w x).getD b false)

private theorem deg_fold (gs : List Gate) (base : Nat)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (ds : List Nat) (w : (Nat → Bool) → List Bool)
    (hlen : ∀ x, (w x).length = ds.length)
    (hw : ∀ i, Deg (base*2^(ds.getD i 0)) (fun x => (w x).getD i false))
    (i : Nat) : Deg (base*2^((gs.foldl dStep ds).getD i 0))
      (fun x => ((gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]) (w x)).getD i false)) := by
  induction gs generalizing ds w with
  | nil => exact hw i
  | cons g gs ih =>
    let v := fun x => w x ++ [g.op.eval (g.inputs.map fun j => (w x).getD j false)]
    change Deg (base*2^((gs.foldl dStep (dStep ds g)).getD i 0)) _
    apply ih (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) (dStep ds g) v
    · intro x; simp [v, dStep, hlen]
    · intro j
      unfold dStep v
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hlen]
      by_cases hj : j < ds.length
      · simpa only [ite_eq_left hj, ← List.getD_eq_getElem?_getD] using hw j
      · simp only [ite_eq_right hj]
        by_cases hj' : j = ds.length
        · simp only [hj', Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          exact deg_gate ds w base hw g (hg g (by simp))
        · have hpos : 0 < j - ds.length := by omega
          have hh {α : Type} (a : α) : ([a] : List α)[j - ds.length]? = none :=
            List.getElem?_eq_none (by simp only [List.length_singleton]; omega)
          simp only [hh, Option.getD_none]
          exact deg_const _ false

theorem deg_wires (C : Circuit) (base w : Nat) (v : (Nat → Bool) → List Bool)
    (hC : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hlen : ∀ x, (v x).length = w)
    (hv : ∀ i, Deg base (fun x => (v x).getD i false)) (i : Nat) :
    Deg (base*2^depth w C) (fun x => (C.wires (v x)).getD i false) := by
  have hv' (j : Nat) : Deg (base*2^((List.replicate w 0).getD j 0))
      (fun x => (v x).getD j false) := by
    by_cases hj : j < w <;>
      simpa [List.getD_eq_getElem?_getD, List.getElem?_replicate, hj] using hv j
  apply deg_mono _ (deg_fold C.gates base hC _ v
    (by simpa) hv' i)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (getD_foldr_max _ _))

end L40553Lower

namespace L40553Lower
open PEqualNP.CircuitLowerBounds

def valid (w : Nat) (C : Circuit) : Prop :=
  PEqualNP.MetaComplexity.NestedCover.ReadsBack w C ∧
  ∀ g ∈ C.gates, g.inputs.length ≤ 2

def feasible (h k start n p d K : Nat) : Prop :=
  let U := Fin n → Fin (2^(h+2))
  let w := 2*n*h
  let W := w+n*(k+9)
  let shift := fun (col : Bool) (x j : Nat) =>
    let bit := fun back : Nat => x.testBit ((start+j+k-back) % k)
    if col then xor (bit 1) (xor (bit 3) (bit 5))
    else xor (bit 0) (xor (bit 1) (bit 2))
  let observe := fun (col : Bool) (x u len : Nat) =>
    List.ofFn (fun i : Fin len =>
      LowerInv.chi (fun l => xor (u.testBit l) (shift col x l)) (h-len+i.val))
  ∃ (menu : Finset Nat) (P D : PEqualNP.CircuitLowerBounds.Circuit)
    (keyTap : Fin n → Fin k → Nat) (out : Fin n → Bool → Fin (h+2) → Nat),
    menu ⊆ Finset.range (2^k) ∧ menu.card = 3 ∧ valid w P ∧ valid W D ∧
    (∀ j i, keyTap j i < w+P.gates.length) ∧
    (∀ j col i, out j col i < W+D.gates.length) ∧
    P.gates.countP nonlinear+D.gates.countP nonlinear ≤ 64*n*(h+1) ∧
    d*(depth w P+depth W D) ≤ p*Nat.clog 2 (h+2)+K ∧
    ∀ (r c : U),
      let reply := fun (u : Nat) => List.ofFn (fun i : Fin h => LowerInv.chi (fun l => u.testBit l) i)
      let y := (List.ofFn (fun j : Fin n => reply (r j).val ++ reply (c j).val)).flatten
      let pre := P.wires y
      let chosen := fun j : Fin n =>
        ∑ i : Fin k, if pre.getD (keyTap j i) false then 2^i.val else 0
      (∀ j, chosen j ∈ menu) ∧
      let data := (List.ofFn (fun j : Fin n =>
        List.ofFn (fun i : Fin k => (chosen j).testBit i) ++
        observe false (chosen j) (r j).val 5 ++ observe true (chosen j) (c j).val 4)).flatten
      let wires := D.wires (y ++ data)
      ∀ j col i, wires.getD (out j col i) false = (if col then c j else r j).val.testBit i

private theorem packedBits {k : Nat} (f : Fin k → Bool) :
    (∑ j, if f j then (2 : Nat)^j.val else 0) < 2^k ∧
    ∀ i : Fin k, (∑ j, if f j then (2 : Nat)^j.val else 0).testBit i.val = f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    let t := ∑ j : Fin k, if f j.castSucc then (2 : Nat)^j.val else 0
    have ht := ih (fun i => f i.castSucc)
    have hsum : (∑ j, if f j then (2 : Nat)^j.val else 0) =
      t + if f (Fin.last k) then 2^k else 0 := by simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, t]
    rw [hsum]
    have hl : t < 2^k := ht.1
    constructor
    · rw [pow_succ, Nat.mul_two]
      split <;> omega
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.val_last]
        cases h : f (Fin.last k) with
        | false => simp [Nat.testBit_lt_two_pow hl]
        | true => simp [Nat.add_comm t, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hl]
      · rw [Fin.val_castSucc]
        cases h : f (Fin.last k) with
        | false => simpa only [h, Bool.false_eq_true, ite_false, Nat.add_zero] using ht.2 j
        | true =>
          simp only [ite_true]
          rw [Nat.add_comm t, Nat.testBit_two_pow_add_gt j.isLt]
          exact ht.2 j

private def graded (d : Nat) (v : (Nat → Bool) → List Bool) :=
  ∀ i : Nat, Deg d (fun x => (v x).getD i false)

private theorem graded_ofFn {n d : Nat} (v : Fin n → (Nat → Bool) → Bool)
    (hv : ∀ i, Deg d (v i)) : graded d (fun x => List.ofFn (fun i => v i x)) := by
  intro i
  by_cases hi : i < n
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some] using hv ⟨i,hi⟩
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right hi, Option.getD_none] using deg_const d false

private theorem graded_append {d n : Nat} {v z : (Nat → Bool) → List Bool}
    (hlen : ∀ x, (v x).length = n) (hv : graded d v) (hz : graded d z) :
    graded d (fun x => v x ++ z x) := by
  intro i
  by_cases hi : i < n
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_append, hlen, ite_eq_left hi] using hv i
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_append, hlen, ite_eq_right hi] using hz (i-n)

private theorem graded_mono {d e : Nat} {v : (Nat → Bool) → List Bool}
    (h : d ≤ e) (hv : graded d v) : graded e v := fun i => deg_mono h (hv i)

private theorem deg_not {d : Nat} {f : (Nat → Bool) → Bool} (hf : Deg d f) :
    Deg d (fun x => !f x) := by
  have hn : (fun x => !f x) = (fun x => xor true (f x)) := by funext x; cases f x <;> rfl
  rw [hn]
  exact deg_xor (deg_const d true) hf

theorem feasible_bound (m p d K : Nat) (hf : feasible (2*m+6) (2*m+6+6) 0 1 p d K) :
    ∃ t, m ≤ 2*2^t ∧ d*t ≤ p*Nat.clog 2 (2*m+6+2)+K := by
  let h := 2*m+6
  let k := h+6
  let w := 2*1*h
  let W := w+1*(k+9)
  have hf' : feasible h k 0 1 p d K := hf
  unfold feasible at hf'
  obtain ⟨menu, P, D, taps, out, _, _, hvP, hvD, _, _, _, hbound, hall⟩ := hf'
  refine ⟨depth w P + depth W D, ?_, hbound⟩
  let r (x : Nat → Bool) (_ : Fin 1) : Fin (2^(h+2)) := LowerInv.inv m x
  let c (_ : Fin 1) : Fin (2^(h+2)) := ⟨0, Nat.two_pow_pos _⟩
  let reply (u : Nat) := List.ofFn (fun i : Fin h => LowerInv.chi u.testBit i)
  let y (x : Nat → Bool) := (List.ofFn (fun j : Fin 1 => reply (r x j).val ++ reply (c j).val)).flatten
  have y_eq (x : Nat → Bool) : y x = reply (r x 0).val ++ reply (c 0).val := by
    simp [y, List.ofFn_succ]
  have ylen (x : Nat → Bool) : (y x).length = w := by
    simp only [y_eq, reply, List.length_append, List.length_ofFn, w, Nat.mul_one, Nat.two_mul]
  have yd : graded 1 y := by
    rw [show y = (fun x => reply (r x 0).val ++ reply (c 0).val) from funext y_eq]
    apply graded_append (n:=h) (fun x => List.length_ofFn)
    · apply graded_ofFn
      intro i
      change Deg 1 (fun x => LowerInv.chi (LowerInv.inv m x).val.testBit i.val)
      simp only [LowerInv.inv_reply]
      split
      · exact deg_const 1 true
      · split
        · exact deg_not (deg_coord (i.val/2))
        · exact deg_const 1 false
    · apply graded_ofFn
      intro i; exact deg_const 1 _
  let A := 2^depth w P
  let f (x : Nat → Bool) (i : Fin k) := (P.wires (y x)).getD (taps 0 i) false
  have fd (i : Fin k) : Deg A (fun x => f x i) := by
    simpa only [Nat.one_mul] using
      deg_wires P 1 w y hvP.2 ylen yd (taps 0 i)
  let key (x : Nat → Bool) : Nat := ∑ i : Fin k, if f x i then 2^i.val else 0
  have keybit (x : Nat → Bool) (i : Fin k) : (key x).testBit i = f x i := (packedBits (f x)).2 i
  have hk : 0 < k := by simp [k,h]
  let shift (col : Bool) (a j : Nat) :=
    let bit := fun back : Nat => a.testBit ((0+j+k-back) % k)
    if col then xor (bit 1) (xor (bit 3) (bit 5))
    else xor (bit 0) (xor (bit 1) (bit 2))
  have sd (col : Bool) (i : Nat) : Deg A (fun x => shift col (key x) i) := by
    have b (z : Nat) : Deg A (fun x => (key x).testBit ((0+i+k-z)%k)) := by
      let j : Fin k := ⟨(0+i+k-z)%k, Nat.mod_lt _ hk⟩
      simpa only [← keybit] using fd j
    cases col
    · exact deg_xor (b 0) (deg_xor (b 1) (b 2))
    · exact deg_xor (b 1) (deg_xor (b 3) (b 5))
  let obs (col : Bool) (a u len : Nat) := List.ofFn (fun i : Fin len =>
      LowerInv.chi (fun l => xor (u.testBit l) (shift col a l)) (h-len+i.val))
  have chiD {v : (Nat → Bool) → Nat → Bool} {i : Nat}
      (a : Deg A (fun x => v x i)) (b : Deg A (fun x => v x (i+1)))
      (c : Deg A (fun x => v x (i+2))) : Deg (A+A) (fun x => LowerInv.chi (v x) i) :=
    deg_xor (deg_mono (Nat.le_add_right ..) a) (deg_and (deg_not b) c)
  have rd : graded (A+A) (fun x => obs false (key x) (r x 0).val 5) := by
    apply graded_ofFn
    intro i
    have z (j : Nat) (hj : h-5+i.val ≤ j) : Deg A (fun x => (r x 0).val.testBit j) := by
      have tail (x : Nat → Bool) : (r x 0).val.testBit j = false :=
        LowerInv.raw_tail x m j (by dsimp only [h] at hj; omega)
      simp only [tail]
      exact deg_const A false
    exact chiD (deg_xor (z _ (by omega)) (sd false _))
      (deg_xor (z _ (by omega)) (sd false _)) (deg_xor (z _ (by omega)) (sd false _))
  have cd : graded (A+A) (fun x => obs true (key x) (c 0).val 4) := by
    apply graded_ofFn
    intro i
    apply chiD <;> apply deg_xor _ (sd true _) <;> exact deg_const A _
  let data (x : Nat → Bool) := List.ofFn (fun i : Fin k => (key x).testBit i) ++
    obs false (key x) (r x 0).val 5 ++ obs true (key x) (c 0).val 4
  have datad : graded (A+A) data := by
    simp only [data, List.append_assoc]
    apply graded_append (n:=k) (by simp only [List.length_ofFn, implies_true])
    · apply graded_ofFn
      intro i; simp only [keybit]
      exact deg_mono (Nat.le_add_right ..) (fd i)
    · exact graded_append (n:=5) (by simp [obs]) rd cd
  have hd : graded (A+A) (fun x => y x ++ data x) := by
    apply graded_append ylen _ datad
    apply graded_mono _ yd
    exact Nat.succ_le_of_lt (lt_of_lt_of_le (Nat.two_pow_pos _) (Nat.le_add_right ..))
  have hdlen (x : Nat → Bool) : (y x ++ data x).length = W := by
    simp only [data, obs, List.length_append, List.length_ofFn, ylen, W, Nat.one_mul, Nat.add_assoc]
  have Ans : Deg ((A+A)*2^depth W D) (fun x => decide (∀ j : Fin m, x j = true)) := by
    have ht := deg_wires D (A+A) W _ hvD.2 hdlen hd
      (out 0 false ⟨0, by omega⟩)
    convert ht using 1
    funext x
    have e := (hall (r x) c).2 0 false ⟨0, by omega⟩
    rw [← LowerInv.inv_bit_zero m x]
    symm
    simpa [y, reply, key, f, data, obs, shift, List.ofFn_succ] using e
  calc
    m ≤ (A+A)*2^depth W D := le_deg_and Ans
    _ = 2*2^(depth w P + depth W D) := by rw [pow_add, ← Nat.two_mul A, Nat.mul_assoc]

private theorem depth_asymptotic {p d K : Nat}
    (feas : ∀ m, ∃ t, m ≤ 2*2^t ∧ d*t ≤ p*Nat.clog 2 (2*m+6+2)+K) : d ≤ p := by
  by_contra! hp
  let a := d+2*p+K+3
  obtain ⟨t, hpow, hcost⟩ := feas (2^a)
  have hlog : Nat.clog 2 (2*(2^a)+6+2) ≤ a+2 := by
    apply Nat.clog_le_of_le_pow
    have he : (2:Nat)^(a+2) = 2^a*4 := pow_add 2 a 2
    rw [he]
    have h4 : 4 ≤ 2^a := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : Nat))).2 (show 2 ≤ a by omega)
    omega
  have hat : a ≤ t+1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2:Nat))).mp
    change (2:Nat)^a ≤ 2^(t+1)
    simpa only [Nat.pow_succ 2 t, Nat.mul_comm (2^t) 2] using hpow
  have c := (Nat.mul_le_mul_left d hat)
  have c' := Nat.mul_le_mul_right a (show p+1 ≤ d by omega)
  have hc := (Nat.mul_le_mul_left p hlog)
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at c c' hc
  rw [Nat.mul_comm p 2] at hc
  omega

theorem lower_exact (p d : Nat)
    (hyp : ∃ K : Nat, ∀ (h k start n : Nat), 5 ≤ h → h+6 ≤ k → feasible h k start n p d K) : d ≤ p := by
  obtain ⟨K,H⟩ := hyp
  apply depth_asymptotic (K:=K)
  intro m
  apply feasible_bound
  exact H (2*m+6) ((2*m+6)+6) 0 1 (by omega) (by omega)

end L40553Lower

namespace L40553Glue

open PEqualNP.CircuitLowerBounds
open scoped BigOperators

abbrev U (h n : Nat) := Fin n → Fin (2^(h+2))

abbrev y (h n : Nat) (r c : U h n) : List Bool :=
  (List.ofFn (Layout40553.yBlock h (X := Unit) (fun _ j => (r j).val)
    (fun _ j => (c j).val) ())).flatten

noncomputable def chosen (h k n : Nat) (P : Circuit) (keyTap : Fin n → Fin k → Nat)
    (r c : U h n) (j : Fin n) : Nat :=
  ∑ i : Fin k, if (P.wires (y h n r c)).getD (keyTap j i) false then 2^i.val else 0

theorem assemble (h k start n p d : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k) (hp : d ≤ p)
    (P D : Circuit) (keyTap : Fin n → Fin k → Nat) (out : Fin n → Bool → Fin (h+2) → Nat)
    (pv : L40553Lower.valid (2*n*h) P) (dv : L40553Lower.valid (2*n*h+n*(k+9)) D)
    (pk : ∀ j i, keyTap j i < 2*n*h+P.gates.length)
    (dt : ∀ j col i, out j col i < 2*n*h+n*(k+9)+D.gates.length)
    (pc : P.gates.countP Select.nonlinear ≤ 6*n)
    (dc : D.gates.countP Decode.nonlinear ≤ 161*n+Decode.Build.decoderBudget (2*n) h)
    (pd : L40553Lower.depth (2*n*h) P ≤ 3)
    (dd : Decode.peak (2*n*h+n*(k+9)) D ≤ Nat.clog 2 (h+2)+9)
    (ck : ∀ (r c : U h n) j, chosen h k n P keyTap r c j ∈ Select.menu k h start)
    (dw : ∀ (r c : U h n) j col i,
      let x := Layout40553.input h k start n (X := Unit) (fun _ t => (r t).val) (fun _ t => (c t).val)
        (fun _ t => chosen h k n P keyTap r c t) ()
      (D.wires x).getD (out j col i) false = (if col then c j else r j).val.testBit i) :
    L40553Lower.feasible h k start n p d (12*d) := by
  have B := Decode.Build.decoderBudget_bound167 n h hh
  have Pcount : P.gates.countP L40553Lower.nonlinear ≤ 6*n := pc
  have Dcount : D.gates.countP L40553Lower.nonlinear ≤ 161*n+Decode.Build.decoderBudget (2*n) h := dc
  have Ddepth : L40553Lower.depth (2*n*h+n*(k+9)) D ≤ Nat.clog 2 (h+2)+9 := dd
  have Dsum : L40553Lower.depth (2*n*h) P + L40553Lower.depth (2*n*h+n*(k+9)) D ≤ Nat.clog 2 (h+2)+12 := by omega
  have Count : P.gates.countP L40553Lower.nonlinear+D.gates.countP L40553Lower.nonlinear ≤ 64*n*(h+1) := by omega
  have Depth : d*(L40553Lower.depth (2*n*h) P + L40553Lower.depth (2*n*h+n*(k+9)) D) ≤ p*Nat.clog 2 (h+2)+12*d := by
    calc
      _ ≤ d*(Nat.clog 2 (h+2)+12) := Nat.mul_le_mul_left d Dsum
      _ = d*Nat.clog 2 (h+2)+12*d := by rw [Nat.mul_add, Nat.mul_comm d 12]
      _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right _ hp) _
  refine ⟨Select.menu k h start,P,D,keyTap,out,Select.menu_range k h start,
    Select.menu_card (by omega),pv,dv,pk,dt,Count,Depth,?_⟩
  intro r c
  exact ⟨ck r c, dw r c⟩

end L40553Glue

namespace L40553Glue

open PEqualNP.CircuitLowerBounds

theorem upperGivenDepth (h k start n p d : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k) (hp : d ≤ p)
    (pd : L40553Lower.depth (2*n*h) (Replicate.circuit h n) ≤ 3) :
    L40553Lower.feasible h k start n p d (12*d) := by
  let X := U h n × U h n
  let r : X → Fin n → Nat := fun x j => (x.1 j).val
  let c : X → Fin n → Nat := fun x j => (x.2 j).val
  let P := Replicate.circuit h n
  let tap := Replicate.keyTap h k start n
  let ky : X → Fin n → Nat := fun x => chosen h k n P tap x.1 x.2
  have hs : ∀ x j, ky x j = Select.key k h start
      (Select.pick (Select.sub 5 (Select.chi (r x j).testBit) (h-5))
        (Select.sub 4 (Select.chi (c x j).testBit) (h-4))) := by
    intro x j
    let yy := Replicate.replyPairs h n (r x) (c x)
    exact Replicate.chosen_key h k start n hh (by omega) yy
      (Replicate.replyPairs_length h n (r x) (c x)) _ _ (Replicate.raw_pairs h n hh (r x) (c x)) j
  obtain ⟨s,out,sc,sd,reads⟩ := Layout40553.literal_decoder h k start n hh hk r c ky hs
  have keymem : ∀ (a b : U h n) j, chosen h k n P tap a b j ∈ Select.menu k h start := by
    intro a b j
    change ky (a,b) j ∈ _
    rw [hs]
    exact Select.key_mem k h start _
  refine assemble h k start n p d hh hk hp P s.circ tap out
    (Replicate.circuit_valid h n hh) ⟨s.back,s.fan⟩
    (Replicate.keyTap_bound h k start n hh) (fun j col i => (reads j col i).1)
    (Replicate.circuit_count h n).le sc pd sd keymem ?_
  intro a b j col i
  cases col <;> exact (reads j _ i).2.1 (a,b)

end L40553Glue

end PEqualNP.Outside.L_meta_40553

open PEqualNP.Outside.L_meta_40553

theorem PEqualNP.Outside.L_meta_40553 : (
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
          (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
  let valid := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack w C ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2
  let chi := fun (u : Nat → Bool) (i : Nat) => xor (u i) (!(u (i+1)) && u (i+2))
  let depth := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (C.gates.foldl (fun (ds : List Nat) g =>
      ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
      (List.replicate w 0)).foldr max 0
  let feasible := fun (h k start n p d K : Nat) =>
    let U := Fin n → Fin (2^(h+2))
    let w := 2*n*h
    let W := w+n*(k+9)
    let shift := fun (col : Bool) (x j : Nat) =>
      let bit := fun back : Nat => x.testBit ((start+j+k-back) % k)
      if col then xor (bit 1) (xor (bit 3) (bit 5))
      else xor (bit 0) (xor (bit 1) (bit 2))
    let observe := fun (col : Bool) (x u len : Nat) =>
      List.ofFn (fun i : Fin len =>
        chi (fun l => xor (u.testBit l) (shift col x l)) (h-len+i.val))
    ∃ (menu : Finset Nat) (P D : PEqualNP.CircuitLowerBounds.Circuit)
      (keyTap : Fin n → Fin k → Nat) (out : Fin n → Bool → Fin (h+2) → Nat),
      menu ⊆ Finset.range (2^k) ∧ menu.card = 3 ∧ valid w P ∧ valid W D ∧
      (∀ j i, keyTap j i < w+P.gates.length) ∧
      (∀ j col i, out j col i < W+D.gates.length) ∧
      P.gates.countP nonlinear+D.gates.countP nonlinear ≤ 64*n*(h+1) ∧
      d*(depth w P+depth W D) ≤ p*Nat.clog 2 (h+2)+K ∧
      ∀ (r c : U),
        let reply := fun (u : Nat) => List.ofFn (fun i : Fin h => chi (fun l => u.testBit l) i)
        let y := (List.ofFn (fun j : Fin n => reply (r j).val ++ reply (c j).val)).flatten
        let pre := P.wires y
        let chosen := fun j : Fin n =>
          ∑ i : Fin k, if pre.getD (keyTap j i) false then 2^i.val else 0
        (∀ j, chosen j ∈ menu) ∧
        let data := (List.ofFn (fun j : Fin n =>
          List.ofFn (fun i : Fin k => (chosen j).testBit i) ++
          observe false (chosen j) (r j).val 5 ++ observe true (chosen j) (c j).val 4)).flatten
        let wires := D.wires (y ++ data)
        ∀ j col i, wires.getD (out j col i) false = (if col then c j else r j).val.testBit i
  ∀ (p d : Nat), 0 < d →
    ((∃ K : Nat, ∀ (h k start n : Nat), 5 ≤ h → h+6 ≤ k → feasible h k start n p d K) ↔
    d ≤ p)) := by
  change ∀ p d : Nat, 0 < d → ((∃ K : Nat, ∀ h k start n : Nat, 5 ≤ h → h+6 ≤ k →
    L40553Lower.feasible h k start n p d K) ↔ d ≤ p)
  intro p d _
  constructor
  · exact L40553Lower.lower_exact p d
  · intro hp
    exact ⟨12*d, fun h k start n hh hk => L40553Glue.upperGivenDepth h k start n p d hh hk hp (Replicate.circuit_depth_le h n hh)⟩

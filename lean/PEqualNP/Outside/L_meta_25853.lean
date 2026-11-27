import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25853_aux.Ranks

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h <;> rfl

theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

theorem zmod2_two : (2 : ZMod 2) = 0 := rfl

theorem zmod2_ite_eq (x : ZMod 2) : (if x = 1 then (1 : ZMod 2) else 0) = x := by
  by_cases h : x = 1
  · simp [h]
  · simp only [h, ite_false]
    fin_cases x
    · rfl
    · exact absurd rfl h

def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthsOf (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
    (List.replicate w 0)

def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem depthsOf_length (w : ℕ) (gs : List Gate) :
    (depthsOf w gs).length = w + gs.length := by
  unfold depthsOf
  have aux : ∀ (ds : List ℕ) (gs : List Gate),
      (gs.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat]) ds).length =
      ds.length + gs.length := by
    intro ds gs
    induction gs generalizing ds with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  rw [aux, List.length_replicate]

theorem wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (wiresOf x gs1) := by
  unfold wiresOf
  rw [List.foldl_append]

theorem depthsOf_append (w : ℕ) (gs1 gs2 : List Gate) :
    depthsOf w (gs1 ++ gs2) =
      gs2.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
        (depthsOf w gs1) := by
  unfold depthsOf
  rw [List.foldl_append]

theorem foldl_append_prefix {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

theorem wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  rw [wiresOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

theorem depthsOf_append_getD_lt (w : ℕ) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < w + gs1.length) :
    (depthsOf w (gs1 ++ gs2)).getD k 0 = (depthsOf w gs1).getD k 0 := by
  rw [depthsOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (ds : List ℕ) (g : Gate) =>
      (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat)
    gs2 (depthsOf w gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [depthsOf_length]; exact hk)]

theorem wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [wiresOf] using h

theorem depthsOf_getD_input (w : ℕ) (gs : List Gate) {k : ℕ} (hk : k < w) :
    (depthsOf w gs).getD k 0 = 0 := by
  have h := depthsOf_append_getD_lt w [] gs (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  unfold depthsOf
  simp only [List.foldl_nil]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_replicate]

theorem wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < x.length + idx) :
    (wiresOf x gs).getD (x.length + idx) false =
      (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlw : (wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [wiresOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]

theorem depthsOf_getD_gate (w : ℕ) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < w + idx) :
    (depthsOf w gs).getD (w + idx) 0 =
      ((gs[idx]).inputs.map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 +
        (nlGate (gs[idx])).toNat := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
  have hld : (depthsOf w (gs.take idx)).length = w + idx := by
    rw [depthsOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hld, Nat.sub_self, List.getD_cons_zero]
  congr 2
  apply List.map_congr_left
  intro a ha
  have halt : a < w + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append_getD_lt w (gs.take idx) [gs[idx]] halt]

theorem oneEach_length {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by
  simp [oneEach]

theorem oneEach_getD_left {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk : k < n) :
    (oneEach i j).getD k false = decide (k = i.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
  simp [Fin.ext_iff]

theorem oneEach_getD_right {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk1 : n ≤ k)
    (hk2 : k < n + m) :
    (oneEach i j).getD k false = decide (k - n = j.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp [hk1])]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  simp [Fin.ext_iff]

theorem anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

theorem anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

theorem card_filter_fin_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    have hsplit : (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card := by
      have hsum : ∀ (S : Finset (Fin (l.length + 1))), S.card =
          (if (0 : Fin (l.length + 1)) ∈ S then 1 else 0) +
          (Finset.univ.filter (fun idx : Fin l.length => idx.succ ∈ S)).card := by
        intro S
        have h1 : S.card = ∑ x : Fin (l.length + 1), if x ∈ S then 1 else 0 := by
          simp
        rw [h1, Fin.sum_univ_succ]
        congr 1
        simp
      have h2 := hsum (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true))
      simpa using h2
    rw [hsplit, ih]
    cases p a <;> simp [Nat.add_comm]


end PEqualNP.Outside.L_meta_25853_aux.Ranks
namespace PEqualNP.Outside.L_meta_25853_aux.Fourier
abbrev Cube (n : ℕ) := Fin n → ZMod 2
def sgn (b : ZMod 2) : ℤ := if b=0 then 1 else -1
def ch {n : ℕ} (a x : Cube n) : ℤ := sgn (dotProduct a x)

theorem sign_add (a b : ZMod 2) : sgn (a+b) = sgn a * sgn b := by
  revert a b
  decide

theorem symm {n : ℕ} (a x : Cube n) : ch a x = ch x a := by
  simp only [ch,dotProduct,mul_comm (a _) (x _)]

theorem ortho {n : ℕ} (a b : Cube n) :
    (∑ x : Cube n, ch a x * ch b x) = if a=b then (2:ℤ)^n else 0 := by
  classical
  by_cases eq : a=b
  · subst b
    have square (t : ZMod 2) : sgn t * sgn t = 1 := by revert t; decide
    simp [ch,square,ZMod.card]
  · rw [if_neg eq]
    obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by
      by_contra! h
      exact eq (funext h)
    let e : Cube n := fun j => if j=i then 1 else 0
    have shift (p x : Cube n) : ch p (x+e) = ch p x * sgn (p i) := by
      have unit : dotProduct p e = p i := by simp [dotProduct,e,mul_ite]
      rw [ch,dotProduct_add,unit,sign_add]
      rfl
    have opposite : ∀ u v : ZMod 2, u ≠ v → sgn u * sgn v = -1 := by decide
    let f (x : Cube n) := ch a x * ch b x
    have flip (x : Cube n) : f (x+e) = -f x := by
      dsimp only [f]
      rw [shift,shift]
      calc
        _ = (ch a x * ch b x) * (sgn (a i) * sgn (b i)) := by ring
        _ = _ := by rw [opposite _ _ hi]; ring
    have same := Equiv.sum_comp (Equiv.addRight e) f
    change (∑ x : Cube n, f (x+e)) = ∑ x : Cube n, f x at same
    simp_rw [flip] at same
    rw [Finset.sum_neg_distrib] at same
    change (∑ x : Cube n, f x) = 0
    omega

def transform {n : ℕ} (f : Cube n → ℤ) (a : Cube n) := ∑ x : Cube n, f x * ch a x

theorem adj {n : ℕ} (f h : Cube n → ℤ) :
    (∑ a : Cube n, transform f a * h a) = ∑ z : Cube n, f z * transform h z := by
  classical
  unfold transform
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro x _
  rw [symm x z]
  ring

theorem inv {n : ℕ} (f : Cube n → ℤ) (a : Cube n) :
    transform (transform f) a = (2:ℤ)^n * f a := by
  classical
  change (∑ x : Cube n, transform f x * ch a x) = _
  rw [adj]
  have lookup (z : Cube n) : transform (ch a) z = if a=z then (2:ℤ)^n else 0 := ortho a z
  simp_rw [lookup]
  simp [mul_ite,mul_comm]
end PEqualNP.Outside.L_meta_25853_aux.Fourier


namespace PEqualNP.Outside.L_meta_25853_aux
open Fourier
abbrev W (s : ℕ) := Cube s × Cube s
def χ {s} (x y : W s) := ch x.1 y.1 * ch x.2 y.2
def coeff {s} (f : W s → ℤ) (a : W s) := ∑ x, f x * χ a x
theorem paircard (s : ℕ) : Fintype.card (W s) = 4^s := by
  simp [W,Cube,ZMod.card,← mul_pow]
theorem ch_sym {s} (x y : W s) : χ x y=χ y x := by simp only [χ,symm]
theorem ch_add {s} (a x y : W s) : χ a (x+y)=χ a x*χ a y := by
  simp only [χ,Prod.fst_add,Prod.snd_add,ch,dotProduct_add,sign_add]; ring
theorem ch_ortho {s} (a b : W s) :
    ∑ x : W s, χ a x*χ b x = if a=b then (4:ℤ)^s else 0 := by
  rw [Fintype.sum_prod_type]
  change (∑ x,∑ y,ch a.1 x*ch a.2 y*(ch b.1 x*ch b.2 y))=_
  have turn (x y : Cube s) : ch a.1 x*ch a.2 y*(ch b.1 x*ch b.2 y)=
      ch a.1 x*ch b.1 x*(ch a.2 y*ch b.2 y) := by ring
  simp only [turn,←Finset.mul_sum,←Finset.sum_mul,ortho]
  by_cases h : a.1=b.1 <;> by_cases k : a.2=b.2 <;>
    simp [h,k,Prod.ext_iff,←mul_pow]
theorem pair_inv {s} (f : W s → ℤ) (x : W s) :
    ∑ a, coeff f a * χ a x = (4:ℤ)^s * f x := by
  simp only [coeff,Finset.sum_mul]
  rw [Finset.sum_comm]
  have one (y : W s) : (∑ a, f y*χ a y*χ a x)=f y*(if y=x then (4:ℤ)^s else 0) := by
    rw [←ch_ortho y x,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _; rw [ch_sym a y,ch_sym a x]; ring
  simp_rw [one]
  simp [mul_ite,mul_comm]
theorem sampleRank {s n m} (f : W s→ℤ) (r : Fin n → W s) (c : Fin m → W s) (u : Fin n→ℚ) (v : Fin m→ℚ) :
  let S := Finset.univ.filter (fun a => coeff f a ≠ 0)
  Matrix.rank (m:=Fin n) (n:=Fin m) (R:=ℚ) (fun i j => u i*v j*(f (r i+c j):ℚ)) ≤ S.card := by
  classical
  intro S
  let P : Matrix (Fin n) S ℚ := fun i a => u i*(χ a.1 (r i):ℚ)*(coeff f a.1:ℚ)/(4:ℚ)^s
  let Q : Matrix S (Fin m) ℚ := fun a j => v j*(χ a.1 (c j):ℚ)
  have factor : (fun i j => u i*v j*(f (r i+c j):ℚ) : Matrix (Fin n) (Fin m) ℚ)=P*Q := by
    ext i j
    have ih := pair_inv f (r i+c j)
    have prune : (∑ a ∈ S, coeff f a * χ a (r i+c j))=∑ a, coeff f a * χ a (r i+c j) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ nx
      have zero : coeff f x = 0 := by simpa [S] using nx
      simp [zero]
    rw [←prune] at ih
    have real_eq : (∑ a ∈ S, (coeff f a:ℚ) * (χ a (r i+c j):ℚ)) =
       (4:ℚ)^s*(f (r i+c j):ℚ) := by exact_mod_cast ih
    have weight : (4:ℚ)^s ≠ 0 := by positivity
    rw [← Finset.sum_coe_sort] at real_eq
    rw [Matrix.mul_apply]
    calc
      u i*v j*(f (r i+c j):ℚ) =
        (u i*v j/(4:ℚ)^s)*∑ a : S, (coeff f a:ℚ)*(χ a (r i+c j):ℚ) := by
          rw [real_eq]; field_simp
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _; simp only [P,Q,ch_add,Int.cast_mul]; ring
  rw [factor]
  apply (Matrix.rank_mul_le_left P Q).trans
  calc P.rank ≤ Module.finrank ℚ (S→ℚ) := LinearMap.finrank_range_le P.mulVecLin
    _ = S.card := by simp
end PEqualNP.Outside.L_meta_25853_aux


namespace PEqualNP.Outside.L_meta_25853_aux
abbrev Tri : Prop :=
  ∀ t : ℕ,
    let V := Fin t → ZMod 2
    ∀ (A B : Fin t → Fin t → ZMod 2) (γ : V),
      let sources := (Finset.univ : Finset (Fin t)).filter (fun j =>
        ∃ i, j < i ∧ (A i j ≠ 0 ∨ B i j ≠ 0))
      let c := fun (j : Fin t) (z : V × V) =>
        γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j)
      let live := (Finset.univ : Finset (V × V)).filter (fun z =>
        ∀ j, c j z ≠ 0 ∨ (z.1 j = 0 ∧ z.2 j = 0))
      let lhs := 2 * 4^sources.card * live.card
      let rhs := (4^sources.card + 1) * 4^t
      lhs ≤ rhs ∧
        (lhs = rhs ↔
          (∀ j, j ∉ sources → γ j = 1) ∧
          ∀ j ∈ sources, ∀ k ∈ sources, ∀ z, c j z = c k z)

abbrev Coeff : Prop :=
  ∀ s : ℕ,
    let V := Fin s → ZMod 2
    let dot := fun (u v : V) => ∑ i : Fin s, u i * v i
    let sign := fun (x : ZMod 2) => if x = 0 then (1 : ℤ) else -1
    ∀ (A B : Fin s → Fin s → ZMod 2) (γ : V) (Z : V → V → V),
    (∀ x y i, Z x y i =
      (x i + ∑ j ∈ Finset.Iio i, A i j * Z x y j) *
      (y i + ∑ j ∈ Finset.Iio i, B i j * Z x y j)) →
    ∀ p q : V,
      let c := fun (j : Fin s) =>
        γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j)
      (∑ x : V, ∑ y : V, sign (dot γ (Z x y) + dot p x + dot q y)) =
        ∏ j : Fin s,
          if c j = 0 then (if p j = 0 ∧ q j = 0 then 4 else 0)
          else 2 * sign (p j * q j)

end PEqualNP.Outside.L_meta_25853_aux

namespace PEqualNP.Outside.L_meta_25853_aux
open Ranks CircuitLowerBounds MetaComplexity.NestedCover Represents Fourier
abbrev F := ZMod 2
abbrev V (t : ℕ) := Fin t → F
abbrev Input (d : ℕ) := Fin d → Bool
def join {d} (x y : Input d) : Input d := fun i => xor (x i) (y i)
def nilIn (d) : Input d := fun _ => false
def delta {d} (f : Input d → F) (x y : Input d) := f x+f y+f (join x y)+f (nilIn d)
def Base {d} (f : Input d → F) := ∀ x y, delta f x y = 0
theorem bconst {d} (c:F) : Base (fun _ : Input d => c) := by
  intro x y; change c+c+c+c=0; rw [zmod2_add_self,zero_add,zmod2_add_self]
theorem badd {d} {f g : Input d→F} (hf : Base f) (hg : Base g) : Base (f+g) := by
  intro x y; have h:=hf x y; have k:=hg x y
  unfold delta at *; simp only [Pi.add_apply]; linear_combination h+k
theorem bscale {d} {f : Input d→F} (u:F) (h: Base f) : Base (fun x => u*f x) := by
  intro x y; have e:=h x y; unfold delta at *; linear_combination u*e
theorem bproj {d} (i : Fin d) : Base (fun x : Input d => b2z (x i)) := by
  intro x y
  simp only [delta,nilIn,join,b2z_xor]
  change b2z (x i)+b2z (y i)+(b2z (x i)+b2z (y i))+0=0
  rw [add_zero,zmod2_add_self]
def Aff {d t} (z : Fin t→Input d→F) (gate : Fin t→ℕ) (k : ℕ) (f : Input d→F) :=
  ∃ (u : Input d→F) (p : Fin t→F), Base u ∧ (∀ a, k < gate a → p a=0) ∧
    ∀ x, f x = u x + ∑ a, p a*z a x
theorem affBase {d t} (z : Fin t→Input d→F) (gate : Fin t→ℕ) (k) {u : Input d→F} (hu : Base u) :
    Aff z gate k u := ⟨u,fun _=>0,hu,by simp,by simp⟩
theorem affConst {d t} (z : Fin t→Input d→F) (gate : Fin t→ℕ) (k) (a:F) :
    Aff z gate k (fun _ => a) := affBase z gate k (bconst a)
theorem affAdd {d t} {z : Fin t→Input d→F} {gate : Fin t→ℕ} {k} {f g : Input d→F} :
    Aff z gate k f → Aff z gate k g → Aff z gate k (fun x => f x+g x) := by
  rintro ⟨u,p,bu,hp,h⟩ ⟨U,P,bU,hP,H⟩
  exact ⟨u+U,p+P,badd bu bU,fun a ha => by simp [hp a ha,hP a ha],fun x => by
    simp only [h,H,Pi.add_apply,add_mul,Finset.sum_add_distrib]; ring⟩
theorem affScale {d t} {z : Fin t→Input d→F} {gate : Fin t→ℕ} {k} {f : Input d→F} (a:F) :
    Aff z gate k f → Aff z gate k (fun x => a*f x) := by
  rintro ⟨u,p,bu,hp,h⟩
  refine ⟨fun x=>a*u x,fun i=>a*p i,bscale a bu,fun x hx => by simp [hp x hx],?_⟩
  intro x; dsimp only; rw [h]; simp only [mul_add,Finset.mul_sum,mul_assoc]
theorem affRelax {d t} {z : Fin t→Input d→F} {gate : Fin t→ℕ} {k l} {f : Input d→F} (le : k ≤ l) :
    Aff z gate k f → Aff z gate l f := by
  rintro ⟨u,p,b,cap,eq⟩
  exact ⟨u,p,b,fun a h => cap a (le.trans_lt h),eq⟩
theorem affProduct {d t} (z : Fin t→Input d→F) (gate : Fin t→ℕ) (a : Fin t) :
    Aff z gate (gate a) (z a) := by
  classical
  refine ⟨fun _=>0,fun i => if i=a then 1 else 0,bconst 0,?_,?_⟩
  · intro i hi; dsimp only; split_ifs with e
    · subst i; omega
    · rfl
  · intro x; simp [ite_mul]
def wire {d} (C : Circuit) (k : ℕ) : Input d → F :=
  fun x => b2z ((wiresOf (List.ofFn x) C.gates).getD k false)
def nodes (C : Circuit) := Finset.univ.filter (fun i : Fin C.gates.length => nlGate C.gates[i.val]=true)
def enumNode (C : Circuit) := (nodes C).orderIsoOfFin rfl
def addr (d : ℕ) (C : Circuit) (a : Fin (nodes C).card) := d+(enumNode C a).val.val
def pin (C : Circuit) (a : Fin (nodes C).card) (b : ℕ) := (C.gates[(enumNode C a).val.val]).inputs.getD b 0
def mon {d} (C : Circuit) (a : Fin (nodes C).card) : Input d→F :=
  fun x => wire C (pin C a 0) x*wire C (pin C a 1) x
theorem circuitAff {d} (C : Circuit) (ar : ∀ g∈C.gates,g.inputs.length≤2) (rb : ReadsBack d C)
    (k : ℕ) : Aff (mon (d:=d) C) (addr d C) k (wire C k) := by
  classical
  have back (idx : Fin C.gates.length) {a : ℕ} (ha : a∈C.gates[idx.val].inputs) : a < d+idx.val := by
    have h:=rb idx.val idx.isLt a
    unfold gateAt at h
    rw [List.getD_eq_getElem _ _ idx.isLt] at h
    exact h ha
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases raw : k < d
    · have e : wire (d:=d) C k=fun x=>b2z (x ⟨k,raw⟩) := by
        funext x; unfold wire; rw [wiresOf_getD_input _ _ (by simpa using raw)]
        simp [raw]
      rw [e]; exact affBase _ _ _ (bproj _)
    by_cases live : k < d+C.gates.length
    · let idx : Fin C.gates.length := ⟨k-d,by omega⟩
      let g := C.gates[idx.val]
      have eqk : d+idx.val=k := by dsimp [idx]; omega
      have arr := ar g (List.getElem_mem idx.isLt)
      have rv (a) (ha : a∈g.inputs) : a < k := (back idx ha).trans_eq eqk
      have val (x : Input d) : wire C k x =
          b2z (g.op.eval (g.inputs.map fun a => (wiresOf (List.ofFn x) C.gates).getD a false)) := by
        unfold wire; rw [←eqk]
        have h := wiresOf_getD_gate (List.ofFn x) C.gates idx.isLt (by
          intro a ha; rw [List.length_ofFn]; exact back idx ha)
        simpa only [List.length_ofFn] using congrArg b2z h

      match pinEq : g.inputs with
      | [] =>
        have e : wire (d:=d) C k = fun _ => b2z (g.op.eval []) := by
          funext x; rw [val,pinEq]; rfl
        rw [e]; apply affConst
      | [a] =>
        have ea : a < k := rv a (by simp [pinEq])
        let c0 := b2z (g.op.eval [false])
        let c1 := c0 + b2z (g.op.eval [true])
        have e : wire (d:=d) C k = fun x => c0+c1*wire C a x := by
          funext x; rw [val,pinEq]
          exact anf_one (fun x => g.op.eval [x]) _
        rw [e]
        exact affAdd (affConst _ _ _ _) (affScale c1 (affRelax ea.le (ih a ea)))
      | [a,b] =>
        have ea : a < k := rv a (by simp [pinEq])
        have eb : b < k := rv b (by simp [pinEq])
        let c0 := b2z (g.op.eval [false,false])
        let c1 := c0+b2z (g.op.eval [true,false])
        let c2 := c0+b2z (g.op.eval [false,true])
        have e : wire (d:=d) C k = fun x => c0+c1*wire C a x+c2*wire C b x+
            b2z (nlGate g)*(wire C a x*wire C b x) := by
          funext x; rw [val,pinEq]
          simpa only [nlGate,pinEq,List.length_cons,List.length_nil,beq_self_eq_true,Bool.true_and,List.map_cons,List.map_nil,wire,c0,c1,c2] using
            anf_two (fun x y => g.op.eval [x,y]) ((wiresOf (List.ofFn x) C.gates).getD a false)
                ((wiresOf (List.ofFn x) C.gates).getD b false)
        have lin := affAdd (affAdd (affConst _ _ _ c0) (affScale c1 (affRelax ea.le (ih a ea)))) (affScale c2 (affRelax eb.le (ih b eb)))
        rw [e]; apply affAdd lin
        by_cases h : nlGate g = true
        · let t := (enumNode C).symm ⟨idx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
          have ti : (enumNode C t).val = idx := congrArg Subtype.val ((enumNode C).apply_symm_apply _)
          have atK : addr d C t=k := by simp only [addr,ti,eqk]
          have m : mon (d:=d) C t = fun x => b2z (nlGate g)*(wire C a x*wire C b x) := by
            funext x
            simp only [mon,pin,ti,show C.gates[idx.val]=g from rfl,pinEq,h,b2z,ite_true,one_mul]
            rfl
          rw [←m,←atK]
          exact affProduct _ _ t
        · have hf : nlGate g=false := Bool.eq_false_iff.mpr h
          simp only [hf,b2z,Bool.false_eq_true,ite_false,zero_mul]
          apply affConst
      | _::_::_::_ =>
        rw [pinEq] at arr; simp at arr
    · have e : wire (d:=d) C k=fun _ => 0 := by
        funext x; unfold wire
        rw [List.getD_eq_default _ _ (by rw [wiresOf_length,List.length_ofFn];omega)]; rfl
      rw [e]; apply affConst

end PEqualNP.Outside.L_meta_25853_aux

namespace PEqualNP.Outside.L_meta_25853_aux
open Ranks CircuitLowerBounds MetaComplexity.NestedCover Represents Fourier
structure Data (d : ℕ) (C : Circuit) where
  bias : ℕ → Input d → F
  coef : ℕ → V (nodes C).card
  base : ∀ w, Base (bias w)
  cutoff : ∀ w i, w < addr d C i → coef w i=0
  val : ∀ w x, wire C w x=bias w x+∑ i,coef w i*mon C i x
theorem dataExists {d} (C : Circuit) (ar : ∀g∈C.gates,g.inputs.length≤2) (rb : ReadsBack d C) :
    Nonempty (Data d C) := by
  classical
  choose u p b cut val using circuitAff C ar rb
  exact ⟨⟨u,p,b,cut,val⟩⟩
def Data.A {d C} (D : Data d C) (i : Fin (nodes C).card) := D.coef (pin C i 0)
def Data.B {d C} (D : Data d C) (i : Fin (nodes C).card) := D.coef (pin C i 1)
def Data.gamma {d C} (D : Data d C) := D.coef C.output
theorem pinBound {d C} (rb : ReadsBack d C) (i : Fin (nodes C).card) (v : ℕ) (hv : v<2) :
    pin C i v < addr d C i := by
  let idx := (enumNode C i).val
  have hnl := (Finset.mem_filter.mp (enumNode C i).property).2
  have ar2 : (C.gates[idx.val]).inputs.length=2 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hnl).1
  have live : v < C.gates[idx.val].inputs.length := by omega
  have h := rb idx.val idx.isLt (pin C i v)
  apply h
  unfold gateAt pin
  rw [List.getD_eq_getElem _ _ idx.isLt,List.getD_eq_getElem _ _ live]
  exact List.getElem_mem _
theorem pinLater {d C} (D : Data d C) (rb : ReadsBack d C) (i j : Fin (nodes C).card) (ij : i ≤ j)
    (v : ℕ) (hv : v<2) : D.coef (pin C i v) j=0 := by
  apply D.cutoff
  exact (pinBound rb i v hv).trans_le (Nat.add_le_add_left ((enumNode C).monotone ij) _)
def active (C : Circuit) (w : ℕ) := ∃ g∈C.gates, nlGate g=true ∧ w∈g.inputs
theorem activePin {C w} (ha : active C w) :
    ∃ i : Fin (nodes C).card, w=pin C i 0 ∨ w=pin C i 1 := by
  obtain ⟨g,hg,hn,hw⟩:=ha
  obtain ⟨k,hk,hval⟩:=List.getElem_of_mem hg
  let idx : Fin C.gates.length := ⟨k,hk⟩
  have eg : C.gates[idx.val]=g := hval
  let i := (enumNode C).symm ⟨idx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eg.symm ▸ hn⟩⟩
  have ti : (enumNode C i).val=idx := congrArg Subtype.val ((enumNode C).apply_symm_apply _)
  have l : g.inputs.length=2 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hn).1
  refine ⟨i,?_⟩
  simp only [pin,ti,eg]
  match inp : g.inputs with
  | [a,b] => simpa [inp] using hw
  | [] | [_] | _::_::_::_ => simp [inp] at l
noncomputable def sources {t} (A B : Fin t→V t) : Finset (Fin t) := by
  classical
  exact Finset.univ.filter (fun j => ∃ i, j < i ∧ (A i j≠0 ∨ B i j≠0))
theorem supported {d C} (D : Data d C) (rb : ReadsBack d C) (w : ℕ) (ha : active C w)
    (j : Fin (nodes C).card) (outside : j∉sources D.A D.B) : D.coef w j=0 := by
  classical
  by_contra nz
  obtain ⟨i,h|h⟩ := activePin ha
  · subst w; apply outside; apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,i,lt_of_not_ge (fun no=>nz (pinLater D rb i j no 0 (by decide))),Or.inl nz⟩
  · subst w; apply outside; apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,i,lt_of_not_ge (fun no=>nz (pinLater D rb i j no 1 (by decide))),Or.inr nz⟩
def row {n} (m) (i : Fin n) (k : Fin (n+m)) := decide (k.val=i.val)
def col (n) {m} (j : Fin m) (k : Fin (n+m)) := decide (k.val=n+j.val)
theorem rowCol {n m} (i : Fin n) (j : Fin m) :
    List.ofFn (join (row m i) (col n j)) = oneEach i j := by
  apply List.ext_getElem
  · simp [oneEach_length]
  · intro k hk hl
    have h : k < n+m := by simpa using hk
    have cmp : (oneEach i j)[k] = (oneEach i j).getD k false := (List.getD_eq_getElem _ _ hl).symm
    rw [cmp,List.getElem_ofFn]
    by_cases lt : k < n
    · rw [oneEach_getD_left i j lt]; simp [join,row,col,show k≠n+j.val by omega]
    · rw [oneEach_getD_right i j (by omega) h]
      have e : k=n+j.val ↔ k-n=j.val := by omega
      simp [join,row,col,show k≠i.val by omega,e]
theorem baseSplit {n m} {f : Input (n+m)→F} (hf : Base f) (i : Fin n) (j : Fin m) :
    f (join (row m i) (col n j))=(f (row m i)+f (nilIn _))+f (col n j) := by
  have e:=hf (row m i) (col n j)
  unfold delta at e
  linear_combination e - zmod2_add_self (f (row m i)) -
    zmod2_add_self (f (col n j)) - zmod2_add_self (f (nilIn _))


end PEqualNP.Outside.L_meta_25853_aux

namespace PEqualNP.Outside.L_meta_25853_aux
open Ranks CircuitLowerBounds MetaComplexity.NestedCover Represents Fourier
def stage {t} (A B : Fin t→V t) (x y : V t) : V t :=
  wellFounded_lt.fix fun i rec =>
    (x i+∑ j ∈ Finset.Iio i, A i j * (if h : j < i then rec j h else 0)) *
    (y i+∑ j ∈ Finset.Iio i, B i j * (if h : j < i then rec j h else 0))
theorem stage_eq {t} (A B : Fin t→V t) (x y : V t) (i : Fin t) :
    stage A B x y i =
    (x i+∑ j ∈ Finset.Iio i, A i j * stage A B x y j) *
    (y i+∑ j ∈ Finset.Iio i, B i j * stage A B x y j) := by
  rw [stage,WellFounded.fix_eq]
  congr 2 <;> apply Finset.sum_congr rfl <;> intro j hj <;> simp [Finset.mem_Iio.mp hj,stage]
def score {t} (A B : Fin t→V t) (g : V t) (z : W t) := ∑ i,g i*stage A B z.1 z.2 i
def Data.label {d C} (D : Data d C) (x : Input d) : W (nodes C).card :=
  (fun i=>D.bias (pin C i 0) x,fun i=>D.bias (pin C i 1) x)
theorem Data.pred {d C} (D : Data d C) (rb : ReadsBack d C) (x : Input d) :
    wire C C.output x = D.bias C.output x + score D.A D.B D.gamma (D.label x) := by
  have corr (i : Fin (nodes C).card) : mon C i x = stage D.A D.B (D.label x).1 (D.label x).2 i := by
    refine @WellFounded.induction (Fin (nodes C).card) (· < ·) wellFounded_lt
      (fun a=>mon C a x = stage D.A D.B (D.label x).1 (D.label x).2 a) i ?_
    intro i ih
    rw [mon,D.val (pin C i 0),D.val (pin C i 1),stage_eq]
    have cut (v:ℕ) (hv:v<2) :
        (∑ a,D.coef (pin C i v) a*mon C a x)=
        ∑ a∈Finset.Iio i,D.coef (pin C i v) a*stage D.A D.B (D.label x).1 (D.label x).2 a := by
      rw [←Finset.sum_subset (Finset.subset_univ (Finset.Iio i)) (by
        intro a _ no; simp [pinLater D rb i a (by simpa using no) v hv])]
      exact Finset.sum_congr rfl fun a ha => by rw [ih a (Finset.mem_Iio.mp ha)]
    rw [cut 0 (by decide),cut 1 (by decide)]
    rfl
  rw [D.val]; simp only [score,Data.gamma,corr]
def Data.rowLab {n m C} (D : Data (n+m) C) (i : Fin n) := D.label (row m i)+D.label (nilIn _)
def Data.colLab {n m C} (D : Data (n+m) C) (j : Fin m) := D.label (col n j)
theorem Data.splitLabel {n m C} (D : Data (n+m) C) (i : Fin n) (j : Fin m) :
    D.label (join (row m i) (col n j))=D.rowLab i+D.colLab j := by
  apply Prod.ext <;> funext a <;> apply baseSplit (D.base _) i j
def valC {n m} (C : Circuit) (i : Fin n) (j : Fin m) := C.eval (oneEach i j)
theorem Data.splitPred {n m C} (D : Data (n+m) C) (rb : ReadsBack (n+m) C) (i : Fin n) (j : Fin m) :
    b2z (valC C i j) =
    (D.bias C.output (row m i)+D.bias C.output (nilIn _))+D.bias C.output (col n j)+
    score D.A D.B D.gamma (D.rowLab i+D.colLab j) := by
  have h:=D.pred rb (join (row m i) (col n j))
  rw [D.splitLabel,baseSplit (D.base _) i j] at h
  unfold wire at h; rw [rowCol] at h; exact h
def signMat {n m} (C : Circuit) : Matrix (Fin n) (Fin m) ℚ := fun i j => if valC C i j then -1 else 1
def sig {t} (A B : Fin t→V t) (g : V t) (z : W t) := sgn (score A B g z)
theorem Data.rankSupport {n m C} (D : Data (n+m) C) (rb : ReadsBack (n+m) C) :
    (signMat (n:=n) (m:=m) C).rank ≤ (Finset.univ.filter (fun p : W (nodes C).card => coeff (sig D.A D.B D.gamma) p ≠ 0)).card := by
  let u (i : Fin n) := D.bias C.output (row m i)+D.bias C.output (nilIn _)
  let v (j : Fin m) := D.bias C.output (col n j)
  have rr:=sampleRank (sig D.A D.B D.gamma) D.rowLab D.colLab (fun i=>(sgn (u i):ℚ)) (fun j=>(sgn (v j):ℚ))
  suffices e : signMat C = (fun i j => (sgn (u i):ℚ)*(sgn (v j):ℚ)*(sig D.A D.B D.gamma (D.rowLab i+D.colLab j):ℚ) : Matrix (Fin n) (Fin m) ℚ) by rw [e]; exact rr
  ext i j
  have flip (b:Bool) : (if b then (-1:ℚ) else 1)=(sgn (b2z b):ℚ) := by cases b <;> norm_num [sgn,b2z]
  simp only [signMat,flip,D.splitPred rb,sign_add,sig,Int.cast_mul,u,v]


end PEqualNP.Outside.L_meta_25853_aux

namespace PEqualNP.Outside.L_meta_25853_aux
open Ranks CircuitLowerBounds MetaComplexity.NestedCover Represents Fourier
def wireB {d} (C : Circuit) (w : ℕ) (x : Input d) := (C.wires (List.ofFn x)).getD w false
open Classical
noncomputable def defect {d} (C : Circuit) : Matrix (Fin (d+C.gates.length)) (Input d × Input d) F := by
  classical
  exact fun w v => if active C w.val ∧
    xor (xor (wireB C w.val v.1) (wireB C w.val v.2))
      (xor (wireB C w.val (join v.1 v.2)) (wireB C w.val (nilIn d)))=true then 1 else 0
theorem defect_wire {d} (C : Circuit) (w : Fin (d+C.gates.length)) (x y : Input d) :
    defect C w (x,y)=if active C w.val then delta (wire C w.val) x y else 0 := by
  classical
  by_cases h : active C w.val
  · simp only [defect,h,true_and,ite_true]
    change b2z (xor (xor (wireB C w.val x) (wireB C w.val y))
       (xor (wireB C w.val (join x y)) (wireB C w.val (nilIn d))))=_
    simp only [b2z_xor,delta]
    change _= (b2z (wireB C w.val x)+b2z (wireB C w.val y)+b2z (wireB C w.val (join x y)))+b2z (wireB C w.val (nilIn d))
    ring
  · simp [defect,h]
theorem delta_val {d C} (D : Data d C) (w : ℕ) (x y : Input d) :
    delta (wire C w) x y = ∑ i,D.coef w i*delta (mon C i) x y := by
  have b:=D.base w x y
  unfold delta at *; simp only [D.val,mul_add,Finset.sum_add_distrib]
  linear_combination b
theorem defect_le {d C} (D : Data d C) (rb : ReadsBack d C) :
    (defect (d:=d) C).rank ≤ (sources D.A D.B).card := by
  classical
  let S:=sources D.A D.B
  let P : Matrix (Fin (d+C.gates.length)) S F := fun w j=> if active C w.val then D.coef w.val j else 0
  let Q : Matrix S (Input d × Input d) F := fun j v=>delta (mon C j) v.1 v.2
  have e : defect C=P*Q := by
    ext w v; obtain ⟨x,y⟩:=v; rw [defect_wire,Matrix.mul_apply]
    by_cases h : active C w.val
    · simp only [P,Q,h,ite_true,delta_val D]
      calc
        _ = ∑ j∈S,D.coef w.val j*delta (mon C j) x y := by
          symm; apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj; rw [supported D rb w.val h j hj,zero_mul]
        _ = _ := by rw [←Finset.sum_coe_sort]
    · simp [P,Q,h]
  rw [e]
  apply (Matrix.rank_mul_le_left P Q).trans
  calc P.rank ≤ Module.finrank F (S→F) := LinearMap.finrank_range_le P.mulVecLin
    _ = S.card := by simp


end PEqualNP.Outside.L_meta_25853_aux

namespace PEqualNP.Outside.L_meta_25853_aux
open Ranks CircuitLowerBounds MetaComplexity.NestedCover Represents Fourier
def freq {t} (A B : Fin t→V t) (g : V t) (j : Fin t) (z : W t) :=
  g j+∑ i∈Finset.Ioi j,(z.1 i*A i j+z.2 i*B i j)
def live {t} (A B : Fin t→V t) (g : V t) := Finset.univ.filter (fun z : W t =>
   ∀ j,freq A B g j z≠0 ∨ (z.1 j=0 ∧ z.2 j=0))
theorem spectrum {t} (co : Coeff) (A B : Fin t→V t) (g : V t) (p q : V t) :
  coeff (sig A B g) (p,q)=∏ j,if freq A B g j (p,q)=0 then
    (if p j=0 ∧ q j=0 then (4:ℤ) else 0) else 2*sgn (p j*q j) := by
  have th := co t A B g (stage A B) (stage_eq A B) p q
  apply Eq.trans _ th
  unfold coeff; rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  change sgn _*(sgn _*sgn _)=sgn (_+_+_)
  rw [sign_add,sign_add]
  simp only [score,dotProduct]
  ring
theorem support_sub {t} (co : Coeff) (A B : Fin t→V t) (g : V t) :
    (Finset.univ.filter (fun p : W t=>coeff (sig A B g) p≠0)) ⊆ live A B g := by
  classical
  rintro ⟨p,q⟩ hz
  have nz := (Finset.mem_filter.mp hz).2
  rw [spectrum co] at nz
  apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,?_⟩
  intro j
  by_cases e : freq A B g j (p,q)=0
  · right; by_contra bad
    apply nz
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [e,bad]
  · exact Or.inl e
theorem weaken {d s k N : ℕ} (le : d ≤ s) (cap : 2*4^s*k ≤ (4^s+1)*N) :
    2*4^d*k ≤ (4^d+1)*N := by
  have powers : (4:ℕ)^d≤4^s := Nat.pow_le_pow_right (by decide) le
  by_cases rel : 2*k ≤ N
  · nlinarith [Nat.mul_le_mul_left (4^d) rel]
  · have e : (4:ℤ)^d≤4^s := by exact_mod_cast powers
    have diff : (N:ℤ)≤2*(k:ℤ) := by exact_mod_cast (by omega : N≤2*k)
    have h : 2*(4:ℤ)^s*(k:ℤ) ≤ ((4:ℤ)^s+1)*(N:ℤ) := by exact_mod_cast cap
    have z := mul_nonneg (sub_nonneg.mpr e) (sub_nonneg.mpr diff)
    exact_mod_cast (show 2*(4:ℤ)^d*(k:ℤ) ≤ ((4:ℤ)^d+1)*(N:ℤ) by nlinarith)
theorem sourceRank {n m C} (D : Data (n+m) C) (rb : ReadsBack (n+m) C) (tr : Tri) (co : Coeff) :
    2*4^(sources D.A D.B).card*(signMat (n:=n) (m:=m) C).rank ≤
       (4^(sources D.A D.B).card+1)*4^(nodes C).card := by
  have cap := (tr (nodes C).card D.A D.B D.gamma).1
  change 2*4^(sources D.A D.B).card*(live D.A D.B D.gamma).card≤_ at cap
  exact (Nat.mul_le_mul_left _ ((D.rankSupport rb).trans (Finset.card_le_card (support_sub co _ _ _)))).trans cap
def pack {t} (a b : V t) (i : Fin (2*t)) := Fin.append a b (Fin.cast (two_mul t) i)
theorem pack_dot {t} (a b c d : V t) :
    ∑ i, pack a b i * pack c d i = (∑ i, a i*c i)+∑ i,b i*d i := by
  have e:=Equiv.sum_comp (finCongr (two_mul t)) (fun i=>Fin.append a b i*Fin.append c d i)
  rw [Fin.sum_univ_add] at e
  simpa only [pack,finCongr_apply,Fin.append_left,Fin.append_right] using e
theorem bit_dec (z:F) : b2z (decide (z=1))=z := by revert z; decide
theorem simple {n m C} (D : Data (n+m) C) (rb : ReadsBack (n+m) C) (no : (sources D.A D.B).card=0) :
    ∃ (r : Fin n→V (2*(nodes C).card)) (c : Fin m→V (2*(nodes C).card)) (u : Fin n→Bool) (v : Fin m→Bool),
      ∀ i j,valC C i j=xor (xor (u i) (v j)) (decide ((∑ k,r i k*c j k)=1)) := by
  classical
  have empty := Finset.card_eq_zero.mp no
  have ab (i j : Fin (nodes C).card) (ji : j < i) : D.A i j=0 ∧ D.B i j=0 := by
    by_contra bad
    have nz : D.A i j≠0 ∨ D.B i j≠0 := by
      by_cases h : D.A i j=0
      · exact Or.inr (fun hb=>bad ⟨h,hb⟩)
      · exact Or.inl h
    have mem : j∈sources D.A D.B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,ji,nz⟩
    simp [empty] at mem
  have mult (x y : V (nodes C).card) (i) : stage D.A D.B x y i=x i*y i := by
    rw [stage_eq]
    have a : (∑ j∈Finset.Iio i,D.A i j*stage D.A D.B x y j)=0 :=
      Finset.sum_eq_zero (fun j h=>by rw [(ab i j (Finset.mem_Iio.mp h)).1,zero_mul])
    have b : (∑ j∈Finset.Iio i,D.B i j*stage D.A D.B x y j)=0 :=
      Finset.sum_eq_zero (fun j h=>by rw [(ab i j (Finset.mem_Iio.mp h)).2,zero_mul])
    simp [a,b]
  let r (i : Fin n) := pack (fun k=>D.gamma k*(D.rowLab i).1 k) (fun k=>D.gamma k*(D.rowLab i).2 k)
  let c (j : Fin m) := pack (D.colLab j).2 (D.colLab j).1
  let u (i : Fin n) := D.bias C.output (row m i)+D.bias C.output (nilIn _)+∑ k,D.gamma k*(D.rowLab i).1 k*(D.rowLab i).2 k
  let v (j : Fin m) := D.bias C.output (col n j)+∑ k,D.gamma k*(D.colLab j).1 k*(D.colLab j).2 k
  refine ⟨r,c,fun i=>decide (u i=1),fun j=>decide (v j=1),?_⟩
  intro i j
  apply b2z_inj
  rw [D.splitPred rb]; simp only [b2z_xor,bit_dec,r,c,pack_dot,mult,score,Prod.fst_add,Prod.snd_add,Pi.add_apply,u,v]
  simp only [mul_add,add_mul,Finset.sum_add_distrib,mul_assoc]
  have e : (∑ k,D.gamma k*((D.colLab j).1 k*(D.rowLab i).2 k))=∑ k,D.gamma k*((D.rowLab i).2 k*(D.colLab j).1 k) := by
    apply Finset.sum_congr rfl; intro k _; ring
  rw [e]; ring


end PEqualNP.Outside.L_meta_25853_aux

namespace PEqualNP.Outside.L_meta_25853_aux
theorem bridge : (
let triangularSupport : Prop :=
  ∀ t : ℕ,
    let V := Fin t → ZMod 2
    ∀ (A B : Fin t → Fin t → ZMod 2) (γ : V),
      let sources := (Finset.univ : Finset (Fin t)).filter (fun j =>
        ∃ i, j < i ∧ (A i j ≠ 0 ∨ B i j ≠ 0))
      let c := fun (j : Fin t) (z : V × V) =>
        γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j)
      let live := (Finset.univ : Finset (V × V)).filter (fun z =>
        ∀ j, c j z ≠ 0 ∨ (z.1 j = 0 ∧ z.2 j = 0))
      let lhs := 2 * 4^sources.card * live.card
      let rhs := (4^sources.card + 1) * 4^t
      lhs ≤ rhs ∧
        (lhs = rhs ↔
          (∀ j, j ∉ sources → γ j = 1) ∧
          ∀ j ∈ sources, ∀ k ∈ sources, ∀ z, c j z = c k z)
let coefficientProduct : Prop :=
  ∀ s : ℕ,
    let V := Fin s → ZMod 2
    let dot := fun (u v : V) => ∑ i : Fin s, u i * v i
    let sign := fun (x : ZMod 2) => if x = 0 then (1 : ℤ) else -1
    ∀ (A B : Fin s → Fin s → ZMod 2) (γ : V) (Z : V → V → V),
    (∀ x y i, Z x y i =
      (x i + ∑ j ∈ Finset.Iio i, A i j * Z x y j) *
      (y i + ∑ j ∈ Finset.Iio i, B i j * Z x y j)) →
    ∀ p q : V,
      let c := fun (j : Fin s) =>
        γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j)
      (∑ x : V, ∑ y : V, sign (dot γ (Z x y) + dot p x + dot q y)) =
        ∏ j : Fin s,
          if c j = 0 then (if p j = 0 ∧ q j = 0 then 4 else 0)
          else 2 * sign (p j * q j)
let conclusion : Prop :=
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
  ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C →
    let t := C.gates.countP nonlinear
    let raw := Fin (n+m) → Bool
    let W := fun (w : ℕ) (x : raw) => (C.wires (List.ofFn x)).getD w false
    let defect : Matrix (Fin (n+m+C.gates.length)) (raw × raw) (ZMod 2) := fun w v =>
      if (∃ g ∈ C.gates, nonlinear g = true ∧ w.val ∈ g.inputs) ∧
        xor (xor (W w.val v.1) (W w.val v.2))
            (xor (W w.val (fun i => xor (v.1 i) (v.2 i))) (W w.val (fun _ => false))) = true
      then 1 else 0
    let value := fun (a : Fin n) (b : Fin m) => C.eval (PEqualNP.Represents.oneEach a b)
    let K : Matrix (Fin n) (Fin m) ℚ := fun i j => if value i j then -1 else 1
    let V := Fin (2*t) → ZMod 2
    2 * 4^defect.rank * K.rank ≤ (4^defect.rank + 1) * 4^t ∧
    (5 * 4^t < 8 * K.rank → defect.rank = 0 ∧
      ∃ (row : Fin n → V) (col : Fin m → V) (Q : Fin n → Bool) (R : Fin m → Bool),
        ∀ i j, value i j = xor (xor (Q i) (R j))
          (decide ((∑ b : Fin (2*t), row i b * col j b) = 1)))
triangularSupport → coefficientProduct → conclusion
) := by
  classical
  intro tr co main ht hc
  intro n m C ar rb t raw W defect Kval K V
  have nt : (nodes C).card=t := Ranks.card_filter_fin_eq_countP C.gates Ranks.nlGate
  obtain ⟨D⟩:=dataExists C ar rb
  have de : defect = PEqualNP.Outside.L_meta_25853_aux.defect (d:=n+m) C := by
    ext w v; simp only [defect,PEqualNP.Outside.L_meta_25853_aux.defect,active,wireB,join,nilIn,W,Ranks.nlGate]
    split
    next h => exact (if_pos h).symm
    next h => exact (if_neg h).symm
  have ke : K=signMat (n:=n) (m:=m) C := rfl
  dsimp only [V]
  rw [de,ke,←nt]
  have cap := sourceRank D rb ht hc
  have below := defect_le D rb
  constructor
  · exact weaken below cap
  · intro h
    have zero : (sources D.A D.B).card=0 := by
      by_contra nz
      have atOne := weaken (by omega : 1≤(sources D.A D.B).card) cap
      norm_num at atOne
      omega
    exact ⟨by omega,simple D rb zero⟩


end PEqualNP.Outside.L_meta_25853_aux

namespace PEqualNP.Outside.L_meta_25853_aux.Support

private lemma card_VV (t : ℕ) :
    Fintype.card ((Fin t → ZMod 2) × (Fin t → ZMod 2)) = 4 ^ t := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← mul_pow]
  rfl

private def setCoord {t : ℕ} (j : Fin t) (a b : ZMod 2)
    (z : (Fin t → ZMod 2) × (Fin t → ZMod 2)) :
    (Fin t → ZMod 2) × (Fin t → ZMod 2) :=
  (Function.update z.1 j a, Function.update z.2 j b)

private lemma four_mul_fiber_card {t : ℕ} (j : Fin t)
    (S : Finset ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (hind : ∀ z a b, setCoord j a b z ∈ S ↔ z ∈ S) (a0 b0 : ZMod 2) :
    4 * (S.filter (fun z => z.1 j = a0 ∧ z.2 j = b0)).card = S.card := by
  have hfib_eq : ∀ a b : ZMod 2,
      (S.filter (fun z => z.1 j = a ∧ z.2 j = b)).card =
        (S.filter (fun z => z.1 j = a0 ∧ z.2 j = b0)).card := by
    intro a b
    refine Finset.card_bij (fun z _ => setCoord j a0 b0 z) ?_ ?_ ?_
    · intro z hz
      have h1 := (Finset.mem_filter.mp hz).1
      refine Finset.mem_filter.mpr ⟨(hind z a0 b0).mpr h1, ?_, ?_⟩
      · simp [setCoord]
      · simp [setCoord]
    · intro z1 hz1 z2 hz2 hEq
      have h1 := (Finset.mem_filter.mp hz1).2
      have h2 := (Finset.mem_filter.mp hz2).2
      apply Prod.ext
      · funext i
        by_cases hij : i = j
        · subst hij; rw [h1.1, h2.1]
        · have hv := congrFun (congrArg Prod.fst hEq) i
          dsimp only [setCoord] at hv
          simpa [Function.update, hij] using hv
      · funext i
        by_cases hij : i = j
        · subst hij; rw [h1.2, h2.2]
        · have hv := congrFun (congrArg Prod.snd hEq) i
          dsimp only [setCoord] at hv
          simpa [Function.update, hij] using hv
    · intro w hw
      have h1 := (Finset.mem_filter.mp hw).1
      have h2 := (Finset.mem_filter.mp hw).2
      refine ⟨setCoord j a b w, Finset.mem_filter.mpr ⟨(hind w a b).mpr h1, by simp [setCoord]⟩, ?_⟩
      apply Prod.ext
      · funext i
        by_cases hij : i = j
        · subst hij; simp [setCoord, h2.1]
        · simp [setCoord, Function.update, hij]
      · funext i
        by_cases hij : i = j
        · subst hij; simp [setCoord, h2.2]
        · simp [setCoord, Function.update, hij]
  have hpart : S.card = ∑ p : ZMod 2 × ZMod 2, (S.filter (fun z => z.1 j = p.1 ∧ z.2 j = p.2)).card := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun z : (Fin t → ZMod 2) × (Fin t → ZMod 2) => (z.1 j, z.2 j))
      (s := S) (t := (Finset.univ : Finset (ZMod 2 × ZMod 2))) (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    refine Finset.sum_congr rfl fun p _ => congrArg Finset.card (by ext z; simp [Prod.ext_iff])
  rw [hpart]
  have hconst : (∑ p : ZMod 2 × ZMod 2, (S.filter (fun z => z.1 j = p.1 ∧ z.2 j = p.2)).card) =
      ∑ _p : ZMod 2 × ZMod 2, (S.filter (fun z => z.1 j = a0 ∧ z.2 j = b0)).card :=
    Finset.sum_congr rfl fun p _ => hfib_eq p.1 p.2
  rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, smul_eq_mul]

private lemma card_hyperplane_two_mul {t : ℕ}
    (A B : Fin t → Fin t → ZMod 2) (γ : Fin t → ZMod 2) (j : Fin t)
    (hsrc : ∃ i, j < i ∧ (A i j ≠ 0 ∨ B i j ≠ 0)) :
    2 * (Finset.univ.filter (fun z : (Fin t → ZMod 2) × (Fin t → ZMod 2) =>
      γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j) = 0)).card = 4 ^ t := by
  rcases hsrc with ⟨i0, hi0, hAB⟩
  let cf : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) → ZMod 2 := fun z =>
    γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j)
  let H0 := Finset.univ.filter (fun z => cf z = 0)
  let H1 := Finset.univ.filter (fun z => cf z = 1)
  have h11 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
    intro x; fin_cases x
    · left; rfl
    · right; rfl
  have hdisj : Disjoint H0 H1 := by
    rw [Finset.disjoint_left]
    intro z h0 h1
    have a0 := (Finset.mem_filter.mp h0).2
    have a1 := (Finset.mem_filter.mp h1).2
    rw [a0] at a1; exact absurd a1 (by decide)
  have hunion : H0 ∪ H1 = Finset.univ := by
    ext z
    simp only [H0, H1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact h11 (cf z)
  have hflip : ∃ τ : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) → ((Fin t → ZMod 2) × (Fin t → ZMod 2)),
      (∀ z, τ (τ z) = z) ∧ (∀ z, cf (τ z) = cf z + 1) := by
    have hmem : i0 ∈ Finset.Ioi j := Finset.mem_Ioi.mpr hi0
    rcases hAB with hA | hB
    · have hA1 : A i0 j = 1 := by
        rcases h11 (A i0 j) with h0 | h1
        · exact absurd h0 hA
        · exact h1
      refine ⟨fun z => (Function.update z.1 i0 (z.1 i0 + 1), z.2), ?_, ?_⟩
      · intro z
        apply Prod.ext
        · funext i
          by_cases hi : i = i0
          · subst hi
            simp only [Function.update_self]
            generalize z.1 i = v; revert v; decide
          · simp [Function.update, hi]
        · rfl
      · intro z
        dsimp only [cf]
        rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
        have hrest :
            (∑ i ∈ (Finset.Ioi j).erase i0, (Function.update z.1 i0 (z.1 i0 + 1) i * A i j + z.2 i * B i j)) =
              ∑ i ∈ (Finset.Ioi j).erase i0, (z.1 i * A i j + z.2 i * B i j) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
          simp [Function.update, hne]
        rw [hrest, Function.update_self, hA1]
        ring
    · have hB1 : B i0 j = 1 := by
        rcases h11 (B i0 j) with h0 | h1
        · exact absurd h0 hB
        · exact h1
      refine ⟨fun z => (z.1, Function.update z.2 i0 (z.2 i0 + 1)), ?_, ?_⟩
      · intro z
        apply Prod.ext
        · rfl
        · funext i
          by_cases hi : i = i0
          · subst hi
            simp only [Function.update_self]
            generalize z.2 i = v; revert v; decide
          · simp [Function.update, hi]
      · intro z
        dsimp only [cf]
        rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
        have hrest :
            (∑ i ∈ (Finset.Ioi j).erase i0, (z.1 i * A i j + Function.update z.2 i0 (z.2 i0 + 1) i * B i j)) =
              ∑ i ∈ (Finset.Ioi j).erase i0, (z.1 i * A i j + z.2 i * B i j) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
          simp [Function.update, hne]
        rw [hrest, Function.update_self, hB1]
        ring
  rcases hflip with ⟨τ, hinv, hadd1⟩
  have hcard_eq : H0.card = H1.card := by
    refine Finset.card_bij (fun z _ => τ z) ?_ ?_ ?_
    · intro z hz
      have hc0 : cf z = 0 := (Finset.mem_filter.mp hz).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hadd1, hc0, zero_add]
    · intro z1 _ z2 _ hEq
      have := congrArg τ hEq
      rwa [hinv, hinv] at this
    · intro w hw
      have hc1 : cf w = 1 := (Finset.mem_filter.mp hw).2
      refine ⟨τ w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hinv w⟩
      rw [hadd1, hc1]
      decide
  have htot : H0.card + H1.card = 4 ^ t := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, card_VV]
  change 2 * H0.card = 4 ^ t
  omega

private lemma four_mul_union_update {t : ℕ} (j : Fin t)
    (H U : Finset ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (hHind : ∀ z a b, setCoord j a b z ∈ H ↔ z ∈ H)
    (hUind : ∀ z a b, setCoord j a b z ∈ U ↔ z ∈ U) :
    let D := H.filter (fun z => ¬ (z.1 j = 0 ∧ z.2 j = 0))
    4 * (D ∪ U).card = U.card + 3 * (H ∪ U).card := by
  intro D
  have hHUind : ∀ z a b, setCoord j a b z ∈ H ∪ U ↔ z ∈ H ∪ U := by
    intro z a b
    simp only [Finset.mem_union, hHind, hUind]
  have hpart : (D ∪ U).card =
      ∑ p : ZMod 2 × ZMod 2, ((D ∪ U).filter (fun z => z.1 j = p.1 ∧ z.2 j = p.2)).card := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun z : (Fin t → ZMod 2) × (Fin t → ZMod 2) => (z.1 j, z.2 j))
      (s := D ∪ U) (t := (Finset.univ : Finset (ZMod 2 × ZMod 2))) (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    refine Finset.sum_congr rfl fun p _ => congrArg Finset.card (by ext z; simp [Prod.ext_iff])
  have h00 : ((D ∪ U).filter (fun z => z.1 j = 0 ∧ z.2 j = 0)) =
      U.filter (fun z => z.1 j = 0 ∧ z.2 j = 0) := by
    ext z
    simp only [D, Finset.mem_filter, Finset.mem_union]
    tauto
  have hnz : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) →
      ((D ∪ U).filter (fun z => z.1 j = a ∧ z.2 j = b)) =
        (H ∪ U).filter (fun z => z.1 j = a ∧ z.2 j = b) := by
    intro a b hab
    ext z
    simp only [D, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h2, h3⟩
      · exact ⟨Or.inl h1.1, h3⟩
      · exact ⟨Or.inr h2, h3⟩
    · rintro ⟨h1 | h2, h3⟩
      · refine ⟨Or.inl ⟨h1, ?_⟩, h3⟩
        rintro ⟨ha, hb⟩
        rw [h3.1] at ha; rw [h3.2] at hb
        exact hab ⟨ha, hb⟩
      · exact ⟨Or.inr h2, h3⟩
  have hsum4 : (∑ p : ZMod 2 × ZMod 2, ((D ∪ U).filter (fun z => z.1 j = p.1 ∧ z.2 j = p.2)).card) =
      ((D ∪ U).filter (fun z => z.1 j = 0 ∧ z.2 j = 0)).card +
      ((D ∪ U).filter (fun z => z.1 j = 0 ∧ z.2 j = 1)).card +
      ((D ∪ U).filter (fun z => z.1 j = 1 ∧ z.2 j = 0)).card +
      ((D ∪ U).filter (fun z => z.1 j = 1 ∧ z.2 j = 1)).card := by
    have huniv : (Finset.univ : Finset (ZMod 2 × ZMod 2)) = {(0, 0), (0, 1), (1, 0), (1, 1)} := by
      decide
    rw [huniv]
    simp [add_assoc]
  rw [hpart, hsum4, h00,
    hnz 0 1 (by decide), hnz 1 0 (by decide), hnz 1 1 (by decide)]
  have e0 := four_mul_fiber_card j U hUind 0 0
  have e1 := four_mul_fiber_card j (H ∪ U) hHUind 0 1
  have e2 := four_mul_fiber_card j (H ∪ U) hHUind 1 0
  have e3 := four_mul_fiber_card j (H ∪ U) hHUind 1 1
  omega

private lemma hyperplane_inclusion_of_D_sub {t : ℕ}
    (A B : Fin t → Fin t → ZMod 2) (γ : Fin t → ZMod 2) (j m : Fin t) (hjm : j < m)
    (hsub : ∀ z : (Fin t → ZMod 2) × (Fin t → ZMod 2),
      (γ m + ∑ i ∈ Finset.Ioi m, (z.1 i * A i m + z.2 i * B i m) = 0) →
      ¬ (z.1 m = 0 ∧ z.2 m = 0) →
      γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j) = 0) :
    ∀ z : (Fin t → ZMod 2) × (Fin t → ZMod 2),
      (γ m + ∑ i ∈ Finset.Ioi m, (z.1 i * A i m + z.2 i * B i m) = 0) →
      γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j) = 0 := by
  intro z hcm
  by_cases hnz : ¬ (z.1 m = 0 ∧ z.2 m = 0)
  · exact hsub z hcm hnz
  · push_neg at hnz
    have hcm_ind : ∀ a b : ZMod 2,
        γ m + ∑ i ∈ Finset.Ioi m, ((setCoord m a b z).1 i * A i m + (setCoord m a b z).2 i * B i m) = 0 := by
      intro a b
      have hsum : (∑ i ∈ Finset.Ioi m, ((setCoord m a b z).1 i * A i m + (setCoord m a b z).2 i * B i m)) =
          ∑ i ∈ Finset.Ioi m, (z.1 i * A i m + z.2 i * B i m) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ m := ne_of_gt (Finset.mem_Ioi.mp hi)
        simp [setCoord, Function.update, hne]
      rw [hsum]; exact hcm
    have hcj_eval : ∀ a b : ZMod 2,
        γ j + ∑ i ∈ Finset.Ioi j, ((setCoord m a b z).1 i * A i j + (setCoord m a b z).2 i * B i j) =
          (γ j + ∑ i ∈ (Finset.Ioi j).erase m, (z.1 i * A i j + z.2 i * B i j)) + (a * A m j + b * B m j) := by
      intro a b
      have hm_mem : m ∈ Finset.Ioi j := Finset.mem_Ioi.mpr hjm
      rw [← Finset.add_sum_erase _ _ hm_mem]
      have hrest : (∑ i ∈ (Finset.Ioi j).erase m, ((setCoord m a b z).1 i * A i j + (setCoord m a b z).2 i * B i j)) =
          ∑ i ∈ (Finset.Ioi j).erase m, (z.1 i * A i j + z.2 i * B i j) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ m := (Finset.mem_erase.mp hi).1
        simp [setCoord, Function.update, hne]
      rw [hrest]
      simp only [setCoord, Function.update_self]
      ring
    have h10 := hsub (setCoord m 1 0 z) (hcm_ind 1 0) (by simp [setCoord])
    have h01 := hsub (setCoord m 0 1 z) (hcm_ind 0 1) (by simp [setCoord])
    have h11 := hsub (setCoord m 1 1 z) (hcm_ind 1 1) (by simp [setCoord])
    rw [hcj_eval 1 0] at h10
    rw [hcj_eval 0 1] at h01
    rw [hcj_eval 1 1] at h11
    have hm_mem : m ∈ Finset.Ioi j := Finset.mem_Ioi.mpr hjm
    have hbase : γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j) =
        γ j + ∑ i ∈ (Finset.Ioi j).erase m, (z.1 i * A i j + z.2 i * B i j) := by
      rw [← Finset.add_sum_erase _ _ hm_mem, hnz.1, hnz.2]
      ring
    rw [hbase]
    set S0 := γ j + ∑ i ∈ (Finset.Ioi j).erase m, (z.1 i * A i j + z.2 i * B i j)
    have hsum3 : (S0 + (1 * A m j + 0 * B m j)) + (S0 + (0 * A m j + 1 * B m j)) +
        (S0 + (1 * A m j + 1 * B m j)) = S0 := by
      have h20 : ∀ x : ZMod 2, x + x = 0 := by intro x; fin_cases x <;> decide
      calc
        (S0 + (1 * A m j + 0 * B m j)) + (S0 + (0 * A m j + 1 * B m j)) +
            (S0 + (1 * A m j + 1 * B m j))
            = (S0 + S0) + (A m j + A m j) + (B m j + B m j) + S0 := by ring
        _ = 0 + 0 + 0 + S0 := by rw [h20 S0, h20 (A m j), h20 (B m j)]
        _ = S0 := by ring
    rw [← hsum3, h10, h01, h11]
    simp

end PEqualNP.Outside.L_meta_25853_aux.Support

namespace PEqualNP.Outside.L_meta_25853_aux.Support
theorem sharp : (∀ t : ℕ,
  let V := Fin t → ZMod 2
  ∀ (A B : Fin t → Fin t → ZMod 2) (γ : V),
    let sources := (Finset.univ : Finset (Fin t)).filter (fun j =>
      ∃ i, j < i ∧ (A i j ≠ 0 ∨ B i j ≠ 0))
    let c := fun (j : Fin t) (z : V × V) =>
      γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j)
    let live := (Finset.univ : Finset (V × V)).filter (fun z =>
      ∀ j, c j z ≠ 0 ∨ (z.1 j = 0 ∧ z.2 j = 0))
    let lhs := 2 * 4^sources.card * live.card
    let rhs := (4^sources.card + 1) * 4^t
    lhs ≤ rhs ∧
      (lhs = rhs ↔
        (∀ j, j ∉ sources → γ j = 1) ∧
        ∀ j ∈ sources, ∀ k ∈ sources, ∀ z, c j z = c k z)) := by
  classical
  intro t V A B γ sources c live lhs rhs
  have h11 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
    intro x; fin_cases x
    · left; rfl
    · right; rfl
  have hc_nonsrc : ∀ j : Fin t, j ∉ sources → ∀ z : V × V, c j z = γ j := by
    intro j hj z
    dsimp only [c]
    have hzero : ∀ i ∈ Finset.Ioi j, z.1 i * A i j + z.2 i * B i j = 0 := by
      intro i hi
      have hnot : ¬ (A i j ≠ 0 ∨ B i j ≠ 0) := by
        intro hAB
        apply hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨i, Finset.mem_Ioi.mp hi, hAB⟩⟩
      push_neg at hnot
      rw [hnot.1, hnot.2]; ring
    rw [Finset.sum_eq_zero hzero, add_zero]
  by_cases hsink : ∀ j : Fin t, j ∉ sources → γ j = 1
  · let H : Fin t → Finset (V × V) := fun j => Finset.univ.filter (fun z => c j z = 0)
    let D : Fin t → Finset (V × V) := fun j => (H j).filter (fun z => ¬ (z.1 j = 0 ∧ z.2 j = 0))
    let Sk : ℕ → Finset (Fin t) := fun k => sources.filter (fun j => k ≤ j.val)
    let Uk : ℕ → Finset (V × V) := fun k => (Sk k).biUnion D
    have hc_ind_le : ∀ (j j0 : Fin t), j0 ≤ j → ∀ z a b,
        c j (PEqualNP.Outside.L_meta_25853_aux.Support.setCoord j0 a b z) = c j z := by
      intro j j0 hle z a b
      dsimp only [c]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hne : i ≠ j0 := ne_of_gt (lt_of_le_of_lt hle (Finset.mem_Ioi.mp hi))
      simp [PEqualNP.Outside.L_meta_25853_aux.Support.setCoord, Function.update, hne]
    have hHind : ∀ (j : Fin t) (z : V × V) (a b : ZMod 2),
        PEqualNP.Outside.L_meta_25853_aux.Support.setCoord j a b z ∈ H j ↔ z ∈ H j := by
      intro j z a b
      simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, hc_ind_le j j le_rfl]
    have hUind : ∀ (k : ℕ) (j0 : Fin t), j0.val < k → ∀ z a b,
        PEqualNP.Outside.L_meta_25853_aux.Support.setCoord j0 a b z ∈ Uk k ↔ z ∈ Uk k := by
      intro k j0 hlt z a b
      simp only [Uk, Finset.mem_biUnion]
      refine exists_congr fun j => and_congr_right fun hj => ?_
      have hk : k ≤ j.val := (Finset.mem_filter.mp hj).2
      have hj0lt : j0 < j := Fin.mk_lt_mk.mpr (by omega)
      have hjne : j ≠ j0 := ne_of_gt hj0lt
      simp only [D, H, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hc_ind_le j j0 (le_of_lt hj0lt)]
      simp only [PEqualNP.Outside.L_meta_25853_aux.Support.setCoord, Function.update, hjne, ↓reduceDIte]
    have hmain : ∀ r : ℕ, r ≤ t →
        let k := t - r
        (4 ^ (Sk k).card - 1) * 4 ^ t ≤ 2 * 4 ^ (Sk k).card * (Uk k).card ∧
        ((4 ^ (Sk k).card - 1) * 4 ^ t = 2 * 4 ^ (Sk k).card * (Uk k).card ↔
          ∀ j ∈ Sk k, Uk (j.val + 1) ⊆ H j) := by
      intro r
      induction r with
      | zero =>
        intro _
        dsimp only
        have hSk0 : Sk t = ∅ := by
          ext j; simp only [Sk, Finset.mem_filter, Finset.notMem_empty, iff_false]
          intro h; have := j.isLt; omega
        simp only [Nat.sub_zero, hSk0, Uk, Finset.biUnion_empty, Finset.card_empty]
        simp
      | succ r ih =>
        intro hr
        have hih := ih (by omega)
        dsimp only at hih ⊢
        set k := t - (r + 1)
        have hks : k + 1 = t - r := by omega
        have hklt : k < t := by omega
        let j0 : Fin t := ⟨k, hklt⟩
        by_cases hj0 : j0 ∈ sources
        · have hSk_eq : Sk k = insert j0 (Sk (k + 1)) := by
            ext j
            simp only [Sk, Finset.mem_insert, Finset.mem_filter]
            constructor
            · rintro ⟨hjs, hkj⟩
              by_cases hEq : j.val = k
              · left; exact Fin.ext hEq
              · right; exact ⟨hjs, by omega⟩
            · rintro (rfl | ⟨hjs, hkj⟩)
              · exact ⟨hj0, le_rfl⟩
              · exact ⟨hjs, by omega⟩
          have hj0_not : j0 ∉ Sk (k + 1) := by
            simp only [Sk, Finset.mem_filter, j0]
            omega
          have hcard_S : (Sk k).card = (Sk (k + 1)).card + 1 := by
            rw [hSk_eq, Finset.card_insert_of_notMem hj0_not]
          have hUk_eq : Uk k = D j0 ∪ Uk (k + 1) := by
            dsimp only [Uk]
            rw [hSk_eq, Finset.biUnion_insert]
          have h4 := PEqualNP.Outside.L_meta_25853_aux.Support.four_mul_union_update j0 (H j0) (Uk (k + 1))
            (hHind j0) (hUind (k + 1) j0 (by dsimp [j0]; omega))
          have h4' : 4 * (Uk k).card = (Uk (k + 1)).card + 3 * (H j0 ∪ Uk (k + 1)).card := by
            rw [hUk_eq]; exact h4
          have hHcard : 2 * (H j0).card = 4 ^ t :=
            PEqualNP.Outside.L_meta_25853_aux.Support.card_hyperplane_two_mul A B γ j0
              (Finset.mem_filter.mp hj0).2
          have hHle : (H j0).card ≤ (H j0 ∪ Uk (k + 1)).card :=
            Finset.card_le_card Finset.subset_union_left
          rw [← hks] at hih
          set s := (Sk (k + 1)).card
          have hs_pos : 1 ≤ 4 ^ s := Nat.one_le_pow _ _ (by decide)
          have hs1_pos : 1 ≤ 4 ^ (s + 1) := Nat.one_le_pow _ _ (by decide)
          have hpow : 4 ^ (s + 1) = 4 * 4 ^ s := by ring
          have h8 : 2 * (Uk (k + 1)).card + 3 * 4 ^ t ≤ 8 * (Uk k).card := by
            omega
          have hineq : (4 ^ (Sk k).card - 1) * 4 ^ t ≤ 2 * 4 ^ (Sk k).card * (Uk k).card := by
            rw [hcard_S]
            have hstep1 : 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) ≤ 4 ^ s * (8 * (Uk k).card) :=
              Nat.mul_le_mul_left _ h8
            have hstep2 : (4 ^ s - 1) * 4 ^ t + 3 * 4 ^ s * 4 ^ t = (4 ^ (s + 1) - 1) * 4 ^ t := by
              zify [hs_pos, hs1_pos]
              ring
            have hstep3 : 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) =
                2 * 4 ^ s * (Uk (k + 1)).card + 3 * 4 ^ s * 4 ^ t := by ring
            have hstep4 : 4 ^ s * (8 * (Uk k).card) = 2 * 4 ^ (s + 1) * (Uk k).card := by
              rw [hpow]; ring
            have hih1 := hih.1
            omega
          refine ⟨hineq, ?_⟩
          constructor
          · intro hEq j hj
            rw [hcard_S] at hEq
            have hstep1 : 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) ≤ 4 ^ s * (8 * (Uk k).card) :=
              Nat.mul_le_mul_left _ h8
            have hstep2 : (4 ^ s - 1) * 4 ^ t + 3 * 4 ^ s * 4 ^ t = (4 ^ (s + 1) - 1) * 4 ^ t := by
              zify [hs_pos, hs1_pos]; ring
            have hstep3 : 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) =
                2 * 4 ^ s * (Uk (k + 1)).card + 3 * 4 ^ s * 4 ^ t := by ring
            have hstep4 : 4 ^ s * (8 * (Uk k).card) = 2 * 4 ^ (s + 1) * (Uk k).card := by
              rw [hpow]; ring
            have hih1 := hih.1
            have h4s_pos : 0 < 4 ^ s := Nat.pow_pos (by decide)
            have hEq_prev : (4 ^ s - 1) * 4 ^ t = 2 * 4 ^ s * (Uk (k + 1)).card := by omega
            have hEq_8 : 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) = 4 ^ s * (8 * (Uk k).card) := by
              omega
            have h8eq : 2 * (Uk (k + 1)).card + 3 * 4 ^ t = 8 * (Uk k).card :=
              Nat.eq_of_mul_eq_mul_left h4s_pos hEq_8
            have hHeq : (H j0).card = (H j0 ∪ Uk (k + 1)).card := by omega
            have hHunion : H j0 = H j0 ∪ Uk (k + 1) :=
              Finset.eq_of_subset_of_card_le Finset.subset_union_left (le_of_eq hHeq.symm)
            have hUsubH : Uk (k + 1) ⊆ H j0 := by
              intro z hz
              rw [hHunion]
              exact Finset.mem_union_right _ hz
            rw [hSk_eq] at hj
            rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact hUsubH
            · exact hih.2.mp hEq_prev j hj'
          · intro hall
            have hUsubH : Uk (k + 1) ⊆ H j0 := hall j0 (by rw [hSk_eq]; exact Finset.mem_insert_self _ _)
            have hprev_eq : (4 ^ s - 1) * 4 ^ t = 2 * 4 ^ s * (Uk (k + 1)).card :=
              hih.2.mpr fun j hj => hall j (by rw [hSk_eq]; exact Finset.mem_insert_of_mem hj)
            have hHunion : H j0 ∪ Uk (k + 1) = H j0 := Finset.union_eq_left.mpr hUsubH
            rw [hHunion] at h4'
            rw [hcard_S]
            have hstep2 : (4 ^ s - 1) * 4 ^ t + 3 * 4 ^ s * 4 ^ t = (4 ^ (s + 1) - 1) * 4 ^ t := by
              zify [hs_pos, hs1_pos]; ring
            have h8eq : 8 * (Uk k).card = 2 * (Uk (k + 1)).card + 3 * 4 ^ t := by omega
            calc
              (4 ^ (s + 1) - 1) * 4 ^ t = (4 ^ s - 1) * 4 ^ t + 3 * 4 ^ s * 4 ^ t := hstep2.symm
              _ = 2 * 4 ^ s * (Uk (k + 1)).card + 3 * 4 ^ s * 4 ^ t := by rw [hprev_eq]
              _ = 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) := by ring
              _ = 4 ^ s * (8 * (Uk k).card) := by rw [h8eq]
              _ = 2 * 4 ^ (s + 1) * (Uk k).card := by rw [hpow]; ring
        · have hSk_eq : Sk k = Sk (k + 1) := by
            ext j
            simp only [Sk, Finset.mem_filter]
            constructor
            · rintro ⟨hjs, hkj⟩
              refine ⟨hjs, ?_⟩
              by_contra hlt
              have hEq : j = j0 := Fin.ext (by dsimp [j0]; omega)
              rw [hEq] at hjs
              exact hj0 hjs
            · rintro ⟨hjs, hkj⟩
              exact ⟨hjs, by omega⟩
          have hUk_eq : Uk k = Uk (k + 1) := by dsimp only [Uk]; rw [hSk_eq]
          rw [← hks] at hih
          rw [hSk_eq, hUk_eq]
          exact hih
    have h0 := hmain t le_rfl
    dsimp only at h0
    rw [Nat.sub_self] at h0
    have hSk0 : Sk 0 = sources := by
      ext j; simp [Sk]
    have hlive_comp : live.card + (Uk 0).card = 4 ^ t := by
      have hdisj : Disjoint live (Uk 0) := by
        rw [Finset.disjoint_left]
        intro z hzl hzu
        have hl := (Finset.mem_filter.mp hzl).2
        rcases Finset.mem_biUnion.mp hzu with ⟨j, _, hjD⟩
        have hD := Finset.mem_filter.mp hjD
        have hc0 := (Finset.mem_filter.mp hD.1).2
        rcases hl j with hne | h00
        · exact hne hc0
        · exact hD.2 h00
      have hunion : live ∪ Uk 0 = Finset.univ := by
        ext z
        simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        by_cases hl : z ∈ live
        · exact Or.inl hl
        · right
          simp only [live, Finset.mem_filter, Finset.mem_univ, true_and] at hl
          push_neg at hl
          rcases hl with ⟨j, hcj, hnz⟩
          have hjs : j ∈ sources := by
            by_contra hnot
            have h1 := hsink j hnot
            rw [hc_nonsrc j hnot z, h1] at hcj
            exact absurd hcj (by decide)
          refine Finset.mem_biUnion.mpr ⟨j, by rw [hSk0]; exact hjs, ?_⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ z, hcj⟩, ?_⟩
          rintro ⟨h1, h2⟩
          exact hnz h1 h2
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ,
        PEqualNP.Outside.L_meta_25853_aux.Support.card_VV]
    rw [hSk0] at h0
    set s := sources.card
    have hs_pos : 1 ≤ 4 ^ s := Nat.one_le_pow _ _ (by decide)
    have hconv : (4 ^ s - 1) * 4 ^ t + (4 ^ s + 1) * 4 ^ t = 2 * 4 ^ s * 4 ^ t := by
      zify [hs_pos]; ring
    have hlive_eq : 2 * 4 ^ s * live.card + 2 * 4 ^ s * (Uk 0).card = 2 * 4 ^ s * 4 ^ t := by
      rw [← mul_add, hlive_comp]
    refine ⟨?_, ?_⟩
    · change 2 * 4 ^ s * live.card ≤ (4 ^ s + 1) * 4 ^ t
      have h01 := h0.1
      omega
    · change 2 * 4 ^ s * live.card = (4 ^ s + 1) * 4 ^ t ↔ _
      have hiff_eq : 2 * 4 ^ s * live.card = (4 ^ s + 1) * 4 ^ t ↔
          (4 ^ s - 1) * 4 ^ t = 2 * 4 ^ s * (Uk 0).card := by omega
      rw [hiff_eq, h0.2]
      constructor
      · intro hall
        refine ⟨hsink, ?_⟩
        have hlt_eq : ∀ j ∈ sources, ∀ k ∈ sources, j < k → ∀ z, c j z = c k z := by
          intro j hj k hk hjk
          have hsub : H k ⊆ H j := by
            intro z hz
            have hck : c k z = 0 := (Finset.mem_filter.mp hz).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
            apply PEqualNP.Outside.L_meta_25853_aux.Support.hyperplane_inclusion_of_D_sub A B γ j k hjk
            · intro w hcw hnz
              have hwU : w ∈ Uk (j.val + 1) := by
                refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, by omega⟩, ?_⟩
                exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ w, hcw⟩, hnz⟩
              exact (Finset.mem_filter.mp (hall j hj hwU)).2
            · exact hck
          have hck_card : 2 * (H k).card = 4 ^ t :=
            PEqualNP.Outside.L_meta_25853_aux.Support.card_hyperplane_two_mul A B γ k (Finset.mem_filter.mp hk).2
          have hcj_card : 2 * (H j).card = 4 ^ t :=
            PEqualNP.Outside.L_meta_25853_aux.Support.card_hyperplane_two_mul A B γ j (Finset.mem_filter.mp hj).2
          have hHeq : H k = H j := Finset.eq_of_subset_of_card_le hsub (by omega)
          intro z
          have hiff0 : c k z = 0 ↔ c j z = 0 := by
            have := Finset.ext_iff.mp hHeq z
            simpa [H] using this
          rcases h11 (c j z) with hj0 | hj1 <;> rcases h11 (c k z) with hk0 | hk1
          · rw [hj0, hk0]
          · exfalso; have := hiff0.mpr hj0; rw [hk1] at this; exact absurd this (by decide)
          · exfalso; have := hiff0.mp hk0; rw [hj1] at this; exact absurd this (by decide)
          · rw [hj1, hk1]
        intro j hj k hk z
        rcases lt_trichotomy j k with hlt | rfl | hgt
        · exact hlt_eq j hj k hk hlt z
        · rfl
        · exact (hlt_eq k hk j hj hgt z).symm
      · rintro ⟨_, hceq⟩ j hj z hz
        rcases Finset.mem_biUnion.mp hz with ⟨k, hk, hkD⟩
        have hks : k ∈ sources := (Finset.mem_filter.mp hk).1
        have hck0 : c k z = 0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hkD).1).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
        rw [hceq j hj k hks z, hck0]
  · push_neg at hsink
    rcases hsink with ⟨j0, hj0_not, hγne⟩
    have hγ0 : γ j0 = 0 := by
      rcases h11 (γ j0) with h0 | h1
      · exact h0
      · exact absurd h1 hγne
    have hlive_sub : live ⊆ Finset.univ.filter (fun z : V × V => z.1 j0 = 0 ∧ z.2 j0 = 0) := by
      intro z hz
      have hl := (Finset.mem_filter.mp hz).2 j0
      rw [hc_nonsrc j0 hj0_not z, hγ0] at hl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
      rcases hl with hne | h00
      · exact absurd rfl hne
      · exact h00
    have h4live : 4 * live.card ≤ 4 ^ t := by
      have hcard_le : live.card ≤
          (Finset.univ.filter (fun z : (Fin t → ZMod 2) × (Fin t → ZMod 2) => z.1 j0 = 0 ∧ z.2 j0 = 0)).card :=
        Finset.card_le_card hlive_sub
      have hfib := PEqualNP.Outside.L_meta_25853_aux.Support.four_mul_fiber_card j0
        (Finset.univ : Finset ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
        (fun _ _ _ => by simp) 0 0
      rw [Finset.card_univ, PEqualNP.Outside.L_meta_25853_aux.Support.card_VV] at hfib
      omega
    have hstrict : lhs < rhs := by
      dsimp only [lhs, rhs]
      have hpow_pos : 0 < 4 ^ t := Nat.pow_pos (by decide)
      have h4s_pos : 0 < 4 ^ sources.card := Nat.pow_pos (by decide)
      have hmul : 2 * (2 * 4 ^ sources.card * live.card) = 4 ^ sources.card * (4 * live.card) := by ring
      have hle1 : 4 ^ sources.card * (4 * live.card) ≤ 4 ^ sources.card * 4 ^ t :=
        Nat.mul_le_mul_left _ h4live
      have hlt2 : 4 ^ sources.card * 4 ^ t < 2 * ((4 ^ sources.card + 1) * 4 ^ t) := by
        have h1 : 4 ^ sources.card * 4 ^ t < (2 * 4 ^ sources.card + 2) * 4 ^ t := by
          exact Nat.mul_lt_mul_of_pos_right (by omega) hpow_pos
        linarith
      omega
    refine ⟨le_of_lt hstrict, ?_⟩
    constructor
    · intro hEq; omega
    · rintro ⟨hall, _⟩
      exact absurd (hall j0 hj0_not) hγne

end PEqualNP.Outside.L_meta_25853_aux.Support

namespace PEqualNP.Outside.L_meta_25853_aux.Product

abbrev K := ZMod 2
def sg (a : K) : ℤ := if a=0 then 1 else -1
theorem sg_add (a b : K) : sg (a+b) = sg a * sg b := by revert a b; decide
theorem twice (a : K) : a+a=0 := by revert a; decide
theorem sg_sum {ι : Type*} (S : Finset ι) (f : ι → K) :
    sg (∑ i ∈ S, f i) = ∏ i ∈ S, sg (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sg]
  | insert i S hi ih => simp [hi, sg_add, ih]
theorem localSum (c p q : K) :
    (∑ v : K × K, sg (c * (v.1*v.2) + p*v.1 + q*v.2)) =
      if c=0 then (if p=0 ∧ q=0 then 4 else 0) else 2*sg (p*q) := by
  revert c p q
  decide
theorem flipSum {s : ℕ} (f : Fin s → Fin s → K) :
    (∑ i, ∑ j ∈ Finset.Iio i, f i j) = ∑ j, ∑ i ∈ Finset.Ioi j, f i j := by
  classical
  have lo (i : Fin s) : Finset.Iio i = Finset.univ.filter (fun j => j < i) := by ext; simp
  have hi (j : Fin s) : Finset.Ioi j = Finset.univ.filter (fun i => j < i) := by ext; simp
  simp_rw [lo,hi,Finset.sum_filter]
  rw [Finset.sum_comm]
theorem transposeSum {s : ℕ} (p z : Fin s → K) (M : Fin s → Fin s → K) :
    (∑ i, p i * ∑ j ∈ Finset.Iio i, M i j * z j) =
    ∑ j, (∑ i ∈ Finset.Ioi j, p i * M i j) * z j := by
  simp_rw [Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  exact flipSum _

end PEqualNP.Outside.L_meta_25853_aux.Product



namespace PEqualNP.Outside.L_meta_25853_aux.Product
theorem coeffs : ∀ s : ℕ,
  let V := Fin s → ZMod 2
  let dot := fun (u v : V) => ∑ i : Fin s, u i * v i
  let sign := fun (x : ZMod 2) => if x = 0 then (1 : ℤ) else -1
  ∀ (A B : Fin s → Fin s → ZMod 2) (γ : V) (Z : V → V → V),
  (∀ x y i, Z x y i =
    (x i + ∑ j ∈ Finset.Iio i, A i j * Z x y j) *
    (y i + ∑ j ∈ Finset.Iio i, B i j * Z x y j)) →
  ∀ p q : V,
    let c := fun (j : Fin s) =>
      γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j)
    (∑ x : V, ∑ y : V, sign (dot γ (Z x y) + dot p x + dot q y)) =
      ∏ j : Fin s,
        if c j = 0 then (if p j = 0 ∧ q j = 0 then 4 else 0)
        else 2 * sign (p j * q j) := by
  classical
  intro s V dot sign A B γ Z hz p q c
  let Pair := Fin s → K × K
  let z : Pair → V := fun e i => (e i).1 * (e i).2
  let h := fun (M : Fin s → Fin s → K) (v : V) (i : Fin s) => ∑ j ∈ Finset.Iio i, M i j * v j
  let decode : Pair → V × V := fun e =>
    (fun i => (e i).1 + h A (z e) i, fun i => (e i).2 + h B (z e) i)
  let encode : V × V → Pair := fun u i => (u.1 i + h A (Z u.1 u.2) i, u.2 i + h B (Z u.1 u.2) i)
  have after (e : Pair) : Z (decode e).1 (decode e).2 = z e := by
    funext i
    refine @WellFounded.induction (Fin s) (· < ·) wellFounded_lt (fun j => Z (decode e).1 (decode e).2 j = z e j) i ?_
    intro i ih
    have ht (M : Fin s → Fin s → K) : h M (Z (decode e).1 (decode e).2) i = h M (z e) i :=
      Finset.sum_congr rfl (fun j hj => congrArg (fun a : K => M i j * a) (ih j (Finset.mem_Iio.mp hj)))
    rw [hz]
    change (((e i).1 + h A (z e) i) + h A _ i) * (((e i).2 + h B (z e) i) + h B _ i) = _
    rw [ht A,ht B]
    simp [add_assoc,twice,z]
  let bij : Pair ≃ V × V := {
    toFun := decode
    invFun := encode
    left_inv := by intro e; funext i; simp [encode,after,decode,add_assoc,twice]
    right_inv := by
      intro u
      have eqz : z (encode u) = Z u.1 u.2 := funext (fun i => (hz u.1 u.2 i).symm)
      apply Prod.ext <;> funext i <;> simp [decode,eqz,encode,add_assoc,twice] }
  let phase := fun (u : V × V) => sg (dot γ (Z u.1 u.2) + dot p u.1 + dot q u.2)
  let term := fun i (v : K × K) => sg (c i * (v.1*v.2) + p i*v.1 + q i*v.2)
  have decomp (e : Pair) : phase (bij e) = ∏ i, term i (e i) := by
    change sg (dot γ (Z (decode e).1 (decode e).2) + dot p (decode e).1 + dot q (decode e).2) = _
    rw [after]
    unfold term
    rw [← sg_sum]
    congr 1
    change _ = ∑ i, (c i * z e i + p i * (e i).1 + q i * (e i).2)
    dsimp only [dot,decode,h,c]
    simp only [mul_add,add_mul,Finset.sum_add_distrib]
    rw [transposeSum,transposeSum]
    abel
  calc
    _ = ∑ u : V × V, phase u := (Fintype.sum_prod_type phase).symm
    _ = ∑ e : Pair, phase (bij e) := (Equiv.sum_comp bij phase).symm
    _ = ∑ e : Pair, ∏ i, term i (e i) := Finset.sum_congr rfl (fun e _ => decomp e)
    _ = ∏ i, ∑ v : K × K, term i v := (Fintype.prod_sum term).symm
    _ = _ := Finset.prod_congr rfl (fun i _ => localSum _ _ _)

end PEqualNP.Outside.L_meta_25853_aux.Product


namespace PEqualNP.Outside.L_meta_25853_aux
open Ranks CircuitLowerBounds Represents MetaComplexity.NestedCover
theorem rankEquality {C : Circuit} (rep : Represents (fun i j : Fin 16=>decide (i=j)) C) :
    16 ≤ (signMat (n:=16) (m:=16) C).rank := by
  let J : Matrix (Fin 16) (Fin 16) ℚ := fun _ _=>1
  have JJ : J*J=(16:ℚ) • J := by
    ext i j
    rw [Matrix.mul_apply,Matrix.smul_apply]
    norm_num [J]
  have eq : signMat C=J-(2:ℚ) • (1: Matrix (Fin 16) (Fin 16) ℚ) := by
    ext i j
    rw [Matrix.sub_apply,Matrix.smul_apply]
    change (if C.eval (oneEach i j) then (-1:ℚ) else 1)=1-(2:ℚ) • (1:Matrix (Fin 16) (Fin 16) ℚ) i j
    rw [rep i j]
    by_cases h:i=j <;> norm_num [Matrix.one_apply,h]
  let L := J-(14:ℚ) • (1:Matrix (Fin 16) (Fin 16) ℚ)
  have mul : signMat C*L=(28:ℚ) • (1:Matrix (Fin 16) (Fin 16) ℚ) := by
    rw [eq]; unfold L
    simp only [sub_mul,mul_sub,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,one_mul,mul_one,JJ,smul_sub,smul_smul]
    module
  have inv : signMat C*((1/28:ℚ) • L)=1 := by
    rw [Algebra.mul_smul_comm,mul,smul_smul]; norm_num
  calc 16 = (1:Matrix (Fin 16) (Fin 16) ℚ).rank := by simp
       _ = (signMat C*((1/28:ℚ) • L)).rank := by rw [inv]
       _ ≤ _ := Matrix.rank_mul_le_left _ _
theorem identity_minor {t} (r c : Fin 16 → V (2*t)) (u v : Fin 16→Bool)
    (model : ∀ i j : Fin 16,decide (i=j)=xor (xor (u i) (v j)) (decide ((∑ k,r i k*c j k)=1))) :
    5≤2*t := by
  classical
  let f (i : Fin 5) : Fin 16 := ⟨i.val,by omega⟩
  let P : Matrix (Fin 5) (Fin (2*t)) F := fun i k=>r (f i) k+r 14 k
  let Q : Matrix (Fin (2*t)) (Fin 5) F := fun k j=>c (f j) k+c 15 k
  have law (i j : Fin 16) : b2z (decide (i=j))=b2z (u i)+b2z (v j)+∑ k,r i k*c j k := by
    rw [model i j,b2z_xor,b2z_xor,bit_dec]
  have minor (i j : Fin 5) : (1:Matrix (Fin 5) (Fin 5) F) i j =
      b2z (decide (f i=f j))+b2z (decide (f i=(15:Fin 16)))+
      b2z (decide ((14:Fin 16)=f j))+b2z (decide ((14:Fin 16)=15)) := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  have fact : (1:Matrix (Fin 5) (Fin 5) F)=P*Q := by
    ext i j; rw [minor,Matrix.mul_apply]
    simp only [law,P,Q,add_mul,mul_add,Finset.sum_add_distrib]
    linear_combination (zmod2_add_self (b2z (u (f i))))+(zmod2_add_self (b2z (v (f j))))+
      (zmod2_add_self (b2z (u 14)))+(zmod2_add_self (b2z (v 15)))
  have rk:=Matrix.rank_mul_le_left P Q
  rw [←fact,Matrix.rank_one] at rk
  have dim:=LinearMap.finrank_range_le P.mulVecLin
  change P.rank≤_ at dim
  simpa using rk.trans dim
theorem impossible (C : Circuit) (ar : ∀ g∈C.gates,g.inputs.length ≤ 2) (rb : ReadsBack 32 C)
    (rep : Represents (fun i j : Fin 16=>decide (i=j)) C) (cap : C.gates.countP nlGate≤2) : False := by
  classical
  have h:= bridge Support.sharp Product.coeffs 16 16 C ar rb
  let t:=C.gates.countP nlGate
  have rank:=rankEquality rep
  have pow : 4^t≤16 := (Nat.pow_le_pow_right (by decide : 0<4) cap).trans_eq (by decide)
  have high : 5*4^t < 8*(signMat (n:=16) (m:=16) C).rank := by omega
  obtain ⟨_,r,c,u,v,model⟩:=h.2 high
  have d:=identity_minor r c u v (fun i j=> (rep i j).symm.trans (model i j))
  change 5≤2*t at d; omega


end PEqualNP.Outside.L_meta_25853_aux

open PEqualNP.Outside.L_meta_25853_aux in
theorem PEqualNP.Outside.L_meta_25853 : (
¬ (let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD C.output 0
∃ C : PEqualNP.CircuitLowerBounds.Circuit,
  (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack 32 C ∧
  PEqualNP.Represents.Represents (fun u v : Fin 16 => decide (u = v)) C ∧
  depth 32 C ≤ 2 ∧ C.gates.countP nonlinear ≤ 2)
) := by
  rintro ⟨C,ar,rb,rep,_,cap⟩
  exact impossible C ar rb rep cap

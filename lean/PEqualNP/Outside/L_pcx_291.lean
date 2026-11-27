import PEqualNP.Defs
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin

/-! Two endpoint probes determine one open digit. Average the decoder errors over public seeds, then encode each good row by its message and its bit-error support. -/

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_291_aux

def Target : Prop :=
    ∀ (a p d b W : ℕ),
      let Q := 2^b
      let Dig := fun j : ℕ => Fin j → Fin Q
      let energy := fun {j : ℕ} (x y : Dig j) => ∑ i : Fin j, (Nat.dist (x i).val (y i).val)^2
      let Row := (Dig a × Dig a) × Dig p
      let Col := Dig p × (Dig d × Dig d)
      let test := fun (v : Row) (w : Col) =>
        (energy v.1.1 v.1.2 + energy v.2 w.1 + energy w.2.1 w.2.2)/W
      let states := (Finset.univ.image test).card
      let H := p*b
      0 < b → 0 < W → W < Q →
        (Q^p ≤ states ∧ states ≤ Q^p * (1+a*(Q-1)^2)) ∧
        (∀ (R s : ℕ), 0 < R →
          ∀ (send : Fin R → Row → Fin (2^s)) (readout : Fin R → Fin (2^s) → Col → ℕ),
            (∀ v w, 64 * (Finset.univ.filter (fun i : Fin R => readout i (send i v) w ≠ test v w)).card ≤ R) →
            2^H ≤ 2^(s+1) * ∑ j ∈ Finset.range (H/16+1), H.choose j)

end PEqualNP.Outside.L_pcx_291_aux

namespace PEqualNP.Outside.L_pcx_291_aux

theorem bucket_diffs {A B W : ℕ} (hW : 0 < W) (h : A/W = B/W) :
    (A : ℤ) - B < W ∧ (B : ℤ) - A < W := by
  have ha := Nat.mod_lt A hW
  have hb := Nat.mod_lt B hW
  have ea := Nat.mod_add_div A W
  have eb := Nat.mod_add_div B W
  rw [h] at ea
  omega

theorem two_probe_unique {L W C D x y : ℕ}
    (hW : 0 < W) (hWL : W ≤ L) (hx : x ≤ L) (hy : y ≤ L)
    (near : (C+x^2)/W = (D+y^2)/W)
    (far : (C+(L-x)^2)/W = (D+(L-y)^2)/W) : x = y := by
  obtain ⟨n₁,n₂⟩ := bucket_diffs hW near
  obtain ⟨f₁,f₂⟩ := bucket_diffs hW far
  push_cast [Nat.cast_sub hx, Nat.cast_sub hy] at n₁ n₂ f₁ f₂
  have eq₁ :
      ((C : ℤ) + ((L : ℤ)-x)^2 - ((D : ℤ)+((L : ℤ)-y)^2)) -
        ((C : ℤ)+ (x : ℤ)^2 - ((D : ℤ)+(y : ℤ)^2)) =
        2*(L : ℤ)*((y : ℤ)-x) := by ring
  have nn : 0 ≤ 2*(L : ℤ) := by positivity
  rcases lt_trichotomy x y with lt | eq | gt
  · have one : (1 : ℤ) ≤ (y : ℤ)-x := by omega
    have big := mul_le_mul_of_nonneg_left one nn
    rw [mul_one] at big
    omega
  · exact eq
  · have one : (1 : ℤ) ≤ (x : ℤ)-y := by omega
    have big := mul_le_mul_of_nonneg_left one nn
    rw [mul_one] at big
    have flip : 2*(L : ℤ)*((x : ℤ)-y) = -(2*(L : ℤ)*((y : ℤ)-x)) := by ring
    omega

end PEqualNP.Outside.L_pcx_291_aux

open scoped BigOperators
namespace PEqualNP.Outside.L_pcx_291_aux

abbrev Dig (Q j : ℕ) := Fin j → Fin Q
abbrev Row (Q a p : ℕ) := (Dig Q a × Dig Q a) × Dig Q p
abbrev Col (Q p d : ℕ) := Dig Q p × (Dig Q d × Dig Q d)

noncomputable def energy {Q j : ℕ} (x y : Dig Q j) : ℕ :=
  ∑ i : Fin j, (Nat.dist (x i).val (y i).val)^2

noncomputable def test {Q a p d : ℕ} (W : ℕ) (v : Row Q a p) (w : Col Q p d) : ℕ :=
  (energy v.1.1 v.1.2 + energy v.2 w.1 + energy w.2.1 w.2.2)/W

def zeroDig {Q j : ℕ} (hQ : 0 < Q) : Dig Q j := fun _ => ⟨0,hQ⟩
def high {Q : ℕ} (hQ : 0 < Q) : Fin Q := ⟨Q-1, by omega⟩
def canonicalRow {Q a p : ℕ} (hQ : 0 < Q) (x : Dig Q p) : Row Q a p :=
  ((zeroDig hQ,zeroDig hQ),x)
def colProbe {Q p d : ℕ} (hQ : 0 < Q) (i : Fin p) (z : Fin Q) : Col Q p d :=
  (Function.update (zeroDig hQ) i z, (zeroDig hQ,zeroDig hQ))

theorem energy_self {Q j : ℕ} (x : Dig Q j) : energy x x = 0 := by
  simp [energy, Nat.dist_self]

noncomputable def baseEnergy {Q p : ℕ} (x : Dig Q p) (i : Fin p) : ℕ :=
  ∑ j ∈ Finset.univ.erase i, (x j).val^2

theorem energy_probe {Q p : ℕ} (hQ : 0 < Q) (x : Dig Q p) (i : Fin p) (z : Fin Q) :
    energy x (Function.update (zeroDig hQ) i z) =
      baseEnergy x i + Nat.dist (x i).val z.val ^ 2 := by
  let f : Fin p → ℕ := fun j => (Nat.dist (x j).val ((Function.update (zeroDig hQ) i z) j).val)^2
  change (∑ j, f j) = _
  rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)]
  simp only [f, Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  simp [zeroDig, Nat.dist_zero_right]

theorem coordinate {Q a p d W : ℕ} (hQ : 0 < Q) (hW : 0 < W) (hWL : W < Q)
    (v w : Row Q a p) (i : Fin p)
    (hn : test (d:=d) W v (colProbe hQ i ⟨0,hQ⟩) = test (d:=d) W w (colProbe hQ i ⟨0,hQ⟩))
    (hf : test (d:=d) W v (colProbe hQ i (high hQ)) = test (d:=d) W w (colProbe hQ i (high hQ))) :
    v.2 i = w.2 i := by
  have hv : (v.2 i).val ≤ Q-1 := by have := (v.2 i).isLt; omega
  have hw : (w.2 i).val ≤ Q-1 := by have := (w.2 i).isLt; omega
  unfold test colProbe at hn hf
  simp only [energy_self, add_zero, energy_probe, Nat.add_assoc] at hn hf
  simp only [Nat.dist_zero_right] at hn
  change _ / W = _ / W at hf
  simp only [high, Nat.dist_eq_sub_of_le hv, Nat.dist_eq_sub_of_le hw] at hf
  apply Fin.ext
  exact two_probe_unique (C:=energy v.1.1 v.1.2 + baseEnergy v.2 i)
    (D:=energy w.1.1 w.1.2 + baseEnergy w.2 i) hW (by omega) hv hw
    (by simpa only [← Nat.add_assoc] using hn)
    (by simpa only [← Nat.add_assoc] using hf)

theorem energy_bound {Q a : ℕ} (x y : Dig Q a) : energy x y ≤ a*(Q-1)^2 := by
  unfold energy
  calc
    (∑ i, Nat.dist (x i).val (y i).val ^ 2) ≤ ∑ _ : Fin a, (Q-1)^2 := by
      gcongr with i
      have hx := (x i).isLt
      have hy := (y i).isLt
      unfold Nat.dist
      omega
    _ = _ := by simp

noncomputable def states {Q a p d : ℕ} (W : ℕ) : ℕ := by
  classical
  exact (Finset.univ.image (test (Q:=Q) (a:=a) (p:=p) (d:=d) W)).card

theorem states_bounds {Q a p d W : ℕ} (hQ : 0 < Q) (hW : 0 < W) (hWL : W < Q) :
    Q^p ≤ states (Q:=Q) (a:=a) (p:=p) (d:=d) W ∧
      states (Q:=Q) (a:=a) (p:=p) (d:=d) W ≤ Q^p * (1+a*(Q-1)^2) := by
  classical
  let f : Row Q a p → Col Q p d → ℕ := test W
  change Q^p ≤ (Finset.univ.image f).card ∧ _ ≤ _
  constructor
  · let g : Dig Q p → Col Q p d → ℕ := fun x => f (canonicalRow hQ x)
    have inj : Function.Injective g := by
      intro x y h
      funext i
      exact coordinate (d:=d) hQ hW hWL (canonicalRow hQ x) (canonicalRow hQ y) i
        (congrFun h (colProbe hQ i ⟨0,hQ⟩)) (congrFun h (colProbe hQ i (high hQ)))
    have hcard : (Finset.univ.image g).card = Q^p := by
      rw [Finset.card_image_of_injective _ inj]
      simp
    rw [←hcard]
    apply Finset.card_le_card
    intro v hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨canonicalRow hQ x,Finset.mem_univ _,rfl⟩
  · let g : Dig Q p × Fin (1+a*(Q-1)^2) → Col Q p d → ℕ :=
      fun x w => (x.2.val + energy x.1 w.1 + energy w.2.1 w.2.2)/W
    calc
      (Finset.univ.image f).card ≤ (Finset.univ.image g).card := by
        apply Finset.card_le_card
        intro v hv
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
        apply Finset.mem_image.mpr
        refine ⟨(x.2, ⟨energy x.1.1 x.1.2, ?_⟩),Finset.mem_univ _, rfl⟩
        have h := energy_bound x.1.1 x.1.2
        omega
      _ ≤ Fintype.card (Dig Q p × Fin (1+a*(Q-1)^2)) := by
        simpa only [Finset.card_univ] using (Finset.card_image_le (s:=Finset.univ) (f:=g))
      _ = _ := by simp

end PEqualNP.Outside.L_pcx_291_aux

open scoped BigOperators
namespace PEqualNP.Outside.L_pcx_291_aux

noncomputable def count {S : Type} [Fintype S] (P : S → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter P).card

theorem count_eq_card {S : Type} [Fintype S] (P : S → Prop) [DecidablePred P] :
    count P = (Finset.univ.filter P).card := by
  unfold count
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter]

theorem count_as_sum {S : Type} [Fintype S] (P : S → Prop) :
    count P = ∑ x : S, @ite ℕ (P x) (Classical.propDecidable (P x)) 1 0 := by
  classical
  simp [count]

theorem count_complement {S : Type} [Fintype S] (P : S → Prop) :
    count P + count (fun x => ¬P x) = Fintype.card S := by
  classical
  rw [count_as_sum, count_as_sum, ← Finset.sum_add_distrib]
  trans ∑ _ : S, (1 : ℕ)
  · apply Finset.sum_congr rfl
    intro x _
    by_cases h : P x <;> simp [h]
  · simp

theorem sum_count_comm {S X : Type} [Fintype S] [Fintype X] (P : S → X → Prop) :
    (∑ s : S, count (P s)) = ∑ x : X, count (fun s => P s x) := by
  classical
  simp only [count_as_sum]
  exact Finset.sum_comm

theorem a_good_seed {R p : ℕ} {X : Type} [Fintype X]
    (hR : 0 < R) (E : Fin R → X → Fin p → Prop)
    (per : ∀ x i, 32 * count (fun r => E r x i) ≤ R) :
    ∃ r : Fin R, Fintype.card X ≤ 2*count (fun x => count (E r x) ≤ p/16) := by
  classical
  let n := fun (r : Fin R) (x : X) => count (E r x)
  let good := fun (r : Fin R) (x : X) => n r x ≤ p/16
  have hs (x : X) : 32*(∑ r : Fin R, n r x) ≤ p*R := by
    change 32*(∑ r : Fin R, count (E r x)) ≤ p*R
    rw [sum_count_comm (fun r i => E r x i), Finset.mul_sum]
    calc
      (∑ i : Fin p, 32 * count (fun r => E r x i)) ≤ ∑ _ : Fin p, R := by
        exact Finset.sum_le_sum fun i _ => per x i
      _ = _ := by simp
  have hhalf (x : X) : R ≤ 2*count (fun r => good r x) := by
    have hpair := count_complement (fun r => good r x)
    rw [Fintype.card_fin] at hpair
    suffices hbad : 2*count (fun r => ¬ good r x) ≤ R by omega
    by_cases hp : p = 0
    · subst p
      have ez : ∀ r, good r x := by
        intro r
        simp [good,n,count]
      simp [count,ez]
    · let bad := Finset.univ.filter (fun r : Fin R => ¬good r x)
      have hbadSum : p * bad.card ≤ 16*(∑ r : Fin R, n r x) := by
        calc
          p * bad.card = ∑ _ ∈ bad, p := by simp [Nat.mul_comm]
          _ ≤ ∑ r ∈ bad, 16*n r x := by
            apply Finset.sum_le_sum
            intro r hr
            have h := (Finset.mem_filter.mp hr).2
            change ¬n r x ≤ p/16 at h
            omega
          _ ≤ 16*(∑ r : Fin R, n r x) := by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have all := calc
        p * (2 * bad.card) = 2*(p*bad.card) := by ac_rfl
        _ ≤ 2*(16*(∑ r : Fin R, n r x)) := Nat.mul_le_mul_left 2 hbadSum
        _ ≤ p*R := by rw [← Nat.mul_assoc]; exact hs x
      have goal : 2*bad.card ≤ R := Nat.le_of_mul_le_mul_left all (Nat.pos_of_ne_zero hp)
      rw [count_eq_card]
      exact goal
  have hcross : R * Fintype.card X ≤ 2*(∑ r : Fin R, count (good r)) := by
    calc
      R * Fintype.card X = ∑ _ : X, R := by simp [Nat.mul_comm]
      _ ≤ ∑ x : X, 2 * count (fun r => good r x) :=
        Finset.sum_le_sum fun x _ => hhalf x
      _ = _ := by rw [←Finset.mul_sum, ←sum_count_comm good]
  by_contra no
  push_neg at no
  have hx : ∑ r : Fin R, (2*count (good r)+1) ≤ ∑ _ : Fin R, Fintype.card X :=
    Finset.sum_le_sum fun r _ => by have := no r; exact this
  have h1 : (∑ _ : Fin R, (1 : ℕ)) = R := by simp
  have h2 : (∑ _ : Fin R, Fintype.card X) = R*Fintype.card X := by simp
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2] at hx
  omega

end PEqualNP.Outside.L_pcx_291_aux

open scoped BigOperators
namespace PEqualNP.Outside.L_pcx_291_aux

noncomputable def decodeDigit {Q a p d W : ℕ} (hQ : 0 < Q) (i : Fin p) (n f : ℕ) : Fin Q := by
  classical
  exact if h : ∃ v : Row Q a p,
    test (d:=d) W v (colProbe hQ i ⟨0,hQ⟩) = n ∧
    test (d:=d) W v (colProbe hQ i (high hQ)) = f
    then h.choose.2 i else ⟨0,hQ⟩

theorem decodeDigit_correct {Q a p d W : ℕ} (hQ : 0 < Q) (hW : 0 < W)
    (hWL : W < Q) (i : Fin p) (v : Row Q a p) (n f : ℕ)
    (hn : test (d:=d) W v (colProbe hQ i ⟨0,hQ⟩) = n)
    (hf : test (d:=d) W v (colProbe hQ i (high hQ)) = f) :
    decodeDigit (a:=a) (d:=d) (W:=W) hQ i n f = v.2 i := by
  classical
  unfold decodeDigit
  have ex : ∃ z : Row Q a p,
      test (d:=d) W z (colProbe hQ i ⟨0,hQ⟩) = n ∧
      test (d:=d) W z (colProbe hQ i (high hQ)) = f := ⟨v,hn,hf⟩
  rw [dif_pos ex]
  exact coordinate (d:=d) hQ hW hWL ex.choose v i
    (ex.choose_spec.1.trans hn.symm) (ex.choose_spec.2.trans hf.symm)

noncomputable def decoder {Q a p d W R s : ℕ} (hQ : 0 < Q)
    (readout : Fin R → Fin (2^s) → Col Q p d → ℕ) (r : Fin R) (m : Fin (2^s)) : Dig Q p :=
  fun i => decodeDigit (a:=a) (d:=d) (W:=W) hQ i
    (readout r m (colProbe hQ i ⟨0,hQ⟩))
    (readout r m (colProbe hQ i (high hQ)))

theorem decoder_errors {Q a p d W R s : ℕ} (hQ : 0 < Q) (hW : 0 < W) (hWL : W < Q)
    (send : Fin R → Row Q a p → Fin (2^s)) (readout : Fin R → Fin (2^s) → Col Q p d → ℕ)
    (ex : ∀ v w, 64 * count (fun r => readout r (send r v) w ≠ test W v w) ≤ R)
    (x : Dig Q p) (i : Fin p) :
    32 * count (fun r => decoder (a:=a) (W:=W) hQ readout r (send r (canonicalRow hQ x)) i ≠ x i) ≤ R := by
  classical
  let v : Row Q a p := canonicalRow hQ x
  let w0 : Col Q p d := colProbe hQ i ⟨0,hQ⟩
  let w1 : Col Q p d := colProbe hQ i (high hQ)
  let e0 := Finset.univ.filter (fun r : Fin R => readout r (send r v) w0 ≠ test W v w0)
  let e1 := Finset.univ.filter (fun r : Fin R => readout r (send r v) w1 ≠ test W v w1)
  let bad := Finset.univ.filter (fun r : Fin R =>
    decoder (a:=a) (W:=W) hQ readout r (send r v) i ≠ x i)
  have sub : bad ⊆ e0 ∪ e1 := by
    intro r hr
    contrapose! hr
    have hn : readout r (send r v) w0 = test W v w0 := by
      by_contra no
      exact hr (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,no⟩))
    have hf : readout r (send r v) w1 = test W v w1 := by
      by_contra no
      exact hr (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,no⟩))
    intro inBad
    apply (Finset.mem_filter.mp inBad).2
    exact decodeDigit_correct hQ hW hWL i v _ _ hn.symm hf.symm
  have hbad := (Finset.card_le_card sub).trans (Finset.card_union_le e0 e1)
  have h0 : 64*e0.card ≤ R := by simpa only [count_eq_card] using ex v w0
  have h1 : 64*e1.card ≤ R := by simpa only [count_eq_card] using ex v w1
  rw [count_eq_card]
  change 32*bad.card ≤ R
  omega

end PEqualNP.Outside.L_pcx_291_aux

open scoped BigOperators
namespace PEqualNP.Outside.L_pcx_291_aux

theorem packing {p b s : ℕ}
    (send : (Fin p → Fin (2^b)) → Fin (2^s))
    (decode : Fin (2^s) → Fin p → Fin (2^b))
    (half : Fintype.card (Fin p → Fin (2^b)) ≤
      2*count (fun x => count (fun i => decode (send x) i ≠ x i) ≤ p/16)) :
    2^(p*b) ≤ 2^(s+1) * ∑ j ∈ Finset.range (p*b/16+1), (p*b).choose j := by
  classical
  let enc : Fin (2^b) ≃ (Fin b → Bool) := Fintype.equivOfCardEq (by simp)
  let err := fun (x : Fin p → Fin (2^b)) =>
    Finset.univ.filter fun k : Fin p × Fin b =>
      enc (x k.1) k.2 ≠ enc (decode (send x) k.1) k.2
  let wrong := fun (x : Fin p → Fin (2^b)) =>
    Finset.univ.filter fun i : Fin p => decode (send x) i ≠ x i
  let good := Finset.univ.filter fun x : Fin p → Fin (2^b) => (wrong x).card ≤ p/16
  let pool := (Finset.range (p*b/16+1)).biUnion fun j =>
    (Finset.univ : Finset (Fin p × Fin b)).powersetCard j
  let encode := fun x => (send x,err x)
  have errSub (x : Fin p → Fin (2^b)) : err x ⊆ (wrong x).product Finset.univ := by
    intro k hk
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,Finset.mem_univ _⟩
    intro eq
    exact (Finset.mem_filter.mp hk).2 (by rw [eq])
  have errBound (x : Fin p → Fin (2^b)) (hx : x ∈ good) : (err x).card ≤ p*b/16 := by
    have h0 := (Finset.mem_filter.mp hx).2
    have h1 := Finset.card_le_card (errSub x)
    rw [Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,Fintype.card_fin] at h1
    apply h1.trans
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    calc
      ((wrong x).card * b)*16 = ((wrong x).card*16)*b := by ac_rfl
      _ ≤ p*b := Nat.mul_le_mul_right _ (by omega)
  have encMap : Set.MapsTo encode (↑good) (↑((Finset.univ : Finset (Fin (2^s))).product pool)) := by
    intro x hx
    change encode x ∈ (Finset.univ : Finset (Fin (2^s))).product pool
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(err x).card,Finset.mem_range.mpr (by have := errBound x hx; omega),?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,rfl⟩
  have encInj : Set.InjOn encode (↑good) := by
    intro x _ y _ he
    have hm : send x = send y := congrArg Prod.fst he
    have hb : err x = err y := congrArg Prod.snd he
    funext i
    apply enc.injective
    funext j
    have hmemb : (i,j) ∈ err x ↔ (i,j) ∈ err y := by rw [hb]
    simp only [err, Finset.mem_filter,Finset.mem_univ,true_and] at hmemb
    rw [←hm] at hmemb
    cases hx : enc (x i) j <;> cases hy : enc (y i) j <;>
      cases hc : enc (decode (send x) i) j <;> simp_all
  have hg : good.card ≤ 2^s * pool.card := by
    have hc := Finset.card_le_card_of_injOn encode encMap encInj
    simpa [Finset.card_product] using hc
  have hpool : pool.card ≤ ∑ j ∈ Finset.range (p*b/16+1), (p*b).choose j := by
    unfold pool
    refine Finset.card_biUnion_le.trans_eq ?_
    simp [Finset.card_powersetCard,Fintype.card_prod]
  have hh : 2^(p*b) ≤ 2*good.card := by
    have hf : Fintype.card (Fin p → Fin (2^b)) = 2^(p*b) := by
      simp [Fintype.card_fun, ← pow_mul, Nat.mul_comm]
    have hc (x : Fin p → Fin (2^b)) :
        count (fun i => decode (send x) i ≠ x i) = (wrong x).card := count_eq_card _
    simp_rw [hc] at half
    have hcount : count (fun x => (wrong x).card ≤ p/16) = good.card := count_eq_card _
    rw [hf,hcount] at half
    exact half
  calc
    2^(p*b) ≤ 2*good.card := hh
    _ ≤ 2*(2^s*pool.card) := Nat.mul_le_mul_left 2 hg
    _ ≤ 2*(2^s*∑ j ∈ Finset.range (p*b/16+1), (p*b).choose j) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpool)
    _ = _ := by rw [pow_succ]; ac_rfl

end PEqualNP.Outside.L_pcx_291_aux

open scoped BigOperators
namespace PEqualNP.Outside.L_pcx_291_aux

theorem states_eq_card {Q a p d : ℕ} (W : ℕ) [DecidableEq (Col Q p d → ℕ)] :
    states (Q:=Q) (a:=a) (p:=p) (d:=d) W =
      (Finset.univ.image (test (Q:=Q) (a:=a) (p:=p) (d:=d) W)).card := by
  unfold states
  apply congrArg Finset.card
  ext f
  simp only [Finset.mem_image]

theorem solveTarget : Target := by
  unfold Target
  intro a p d b W
  dsimp only
  intro hb hW hWL
  have hQ : 0 < (2:ℕ)^b := by positivity
  refine ⟨?_,?_⟩
  · have h := states_bounds (a:=a) (p:=p) (d:=d) hQ hW hWL
    rw [states_eq_card] at h
    exact h
  · intro R s hR send readout ex
    have hErr : ∀ v w, 64 * count (fun r => readout r (send r v) w ≠ test (Q:=2^b) W v w) ≤ R := by
      intro v w
      rw [count_eq_card]
      exact ex v w
    let goodErr := fun (r : Fin R) (x : Dig (2^b) p) (i : Fin p) =>
      decoder (a:=a) (W:=W) hQ readout r (send r (canonicalRow hQ x)) i ≠ x i
    have per : ∀ x i, 32*count (fun r => goodErr r x i) ≤ R :=
      decoder_errors hQ hW hWL send readout hErr
    obtain ⟨r, hr⟩ := a_good_seed hR goodErr per
    exact packing (fun x => send r (canonicalRow hQ x))
      (decoder (a:=a) (W:=W) hQ readout r) hr

end PEqualNP.Outside.L_pcx_291_aux

theorem PEqualNP.Outside.L_pcx_291 :
    ∀ (a p d b W : ℕ),
      let Q := 2^b
      let Dig := fun j : ℕ => Fin j → Fin Q
      let energy := fun {j : ℕ} (x y : Dig j) => ∑ i : Fin j, (Nat.dist (x i).val (y i).val)^2
      let Row := (Dig a × Dig a) × Dig p
      let Col := Dig p × (Dig d × Dig d)
      let test := fun (v : Row) (w : Col) =>
        (energy v.1.1 v.1.2 + energy v.2 w.1 + energy w.2.1 w.2.2)/W
      let states := (Finset.univ.image test).card
      let H := p*b
      0 < b → 0 < W → W < Q →
        (Q^p ≤ states ∧ states ≤ Q^p * (1+a*(Q-1)^2)) ∧
        (∀ (R s : ℕ), 0 < R →
          ∀ (send : Fin R → Row → Fin (2^s)) (readout : Fin R → Fin (2^s) → Col → ℕ),
            (∀ v w, 64 * (Finset.univ.filter (fun i : Fin R => readout i (send i v) w ≠ test v w)).card ≤ R) →
            2^H ≤ 2^(s+1) * ∑ j ∈ Finset.range (H/16+1), H.choose j) :=
  PEqualNP.Outside.L_pcx_291_aux.solveTarget


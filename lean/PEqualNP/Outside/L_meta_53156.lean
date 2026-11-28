import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53156_aux

namespace Dervish53156Donor
namespace Donor1196
namespace DervishBuild1196

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

abbrev Legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

structure Build (w : Nat) where
  gates : List Gate
  back : ReadsBack w ⟨gates,0⟩
  fan : ∀ g ∈ gates, Legal g

namespace Build

variable {w : Nat} {X : Type}

def circ (s : Build w) : Circuit := ⟨s.gates,0⟩
def empty (w : Nat) : Build w := ⟨[], by simp [ReadsBack], by simp⟩
def size (s : Build w) : Nat := w+s.gates.length
def cost (s : Build w) : Nat := s.gates.length
def nots (s : Build w) : Nat := PEqualNP.NotBracket.notCount s.circ
def Ext (s s' : Build w) : Prop := s.gates <+: s'.gates

def Read (input : X → List Bool) (s : Build w) (r : Nat) (f : X → Bool) : Prop :=
  r < s.size ∧ ∀ x, (s.circ.wires (input x)).getD r false = f x

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

theorem read_persist {input : X → List Bool} (hinput : ∀ x, (input x).length = w)
    {s s' : Build w} {r f} (E : Ext s s') (V : Read input s r f) : Read input s' r f := by
  refine ⟨V.1.trans_le (Nat.add_le_add_left E.length_le _), ?_⟩
  intro x
  rw [Ext.getD (wires_prefix E _) (by rw [wires_len, hinput]; exact V.1)]
  exact V.2 x

theorem read_input {input : X → List Bool} (hinput : ∀ x, (input x).length = w)
    (s : Build w) (i : Nat) (hi : i < w) : Read input s i (fun x => (input x).getD i false) := by
  have E : Ext (empty w) s := List.nil_prefix
  apply read_persist hinput E
  exact ⟨by simpa [size,empty] using hi, fun _ => rfl⟩

def push (s : Build w) (g : Gate) (fan : Legal g)
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

theorem emit (input : X → List Bool) (hinput : ∀ x, (input x).length = w)
    (s : Build w) (g : Gate) (ok : Legal g) (back : ∀ i ∈ g.inputs, i < s.size)
    (f : X → Bool)
    (sem : ∀ x, g.op.eval (g.inputs.map (fun i => (s.circ.wires (input x)).getD i false)) = f x) :
    ∃ s' t, Ext s s' ∧ Read input s' t f ∧ s'.cost = s.cost+1 ∧
      s'.nots = s.nots + PEqualNP.NotBracket.notCount ⟨[g],0⟩ := by
  refine ⟨s.push g ok back,s.size,List.prefix_append ..,⟨by simp [size,push],?_⟩,?_ ,?_⟩
  · intro x
    have hl : (s.circ.wires (input x)).length = s.size := by rw [wires_len,hinput]; rfl
    unfold Circuit.wires circ push
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change ((s.circ.wires (input x)) ++ [_]).getD s.size false = _
    rw [← hl, getD_snoc]
    exact sem x
  · simp [cost,push]
  · simp [nots,circ,push,PEqualNP.NotBracket.notCount]

section
variable {input : X → List Bool} (hinput : ∀ x, (input x).length = w)
include hinput

theorem emitAnd {s : Build w} {a b f g} (ha : Read input s a f) (hb : Read input s b g) :
    ∃ t c, Ext s t ∧ Read input t c (fun x => f x && g x) ∧ t.cost ≤ s.cost+1 ∧ t.nots = s.nots := by
  obtain ⟨t,c,E,V,eq,n⟩ := emit input hinput s ⟨.and,[a,b]⟩ (by simp [Legal])
    (by intro j hj; simp at hj; rcases hj with rfl | rfl; exact ha.1; exact hb.1)
    (fun x => f x && g x) (by intro x; simp only [List.map_cons,List.map_nil,ha.2 x,hb.2 x] <;> cases f x <;> cases g x <;> rfl)
  exact ⟨t,c,E,V,eq.le,by simpa [PEqualNP.NotBracket.notCount] using n⟩

theorem emitOr {s : Build w} {a b f g} (ha : Read input s a f) (hb : Read input s b g) :
    ∃ t c, Ext s t ∧ Read input t c (fun x => f x || g x) ∧ t.cost ≤ s.cost+1 ∧ t.nots = s.nots := by
  obtain ⟨t,c,E,V,eq,n⟩ := emit input hinput s ⟨.or,[a,b]⟩ (by simp [Legal])
    (by intro j hj; simp at hj; rcases hj with rfl | rfl; exact ha.1; exact hb.1)
    (fun x => f x || g x) (by intro x; simp only [List.map_cons,List.map_nil,ha.2 x,hb.2 x] <;> cases f x <;> cases g x <;> rfl)
  exact ⟨t,c,E,V,eq.le,by simpa [PEqualNP.NotBracket.notCount] using n⟩

theorem emitNot {s : Build w} {a f} (ha : Read input s a f) :
    ∃ t c, Ext s t ∧ Read input t c (fun x => !(f x)) ∧ t.cost ≤ s.cost+1 ∧ t.nots = s.nots+1 := by
  obtain ⟨t,c,E,V,eq,n⟩ := emit input hinput s ⟨.not,[a]⟩ (by simp [Legal])
    (by intro j hj; simp at hj; subst j; exact ha.1)
    (fun x => !(f x)) (by intro x; simp only [List.map_cons,List.map_nil,ha.2 x] <;> cases f x <;> rfl)
  exact ⟨t,c,E,V,eq.le,by simpa [PEqualNP.NotBracket.notCount] using n⟩

end

end Build
end DervishBuild1196
namespace Upper1196Unary

private def T (m j : Nat) : Bool := decide (j ≤ m)
private def H (m d : Nat) : Bool := !(T m d)
private def U (m d j : Nat) : Bool := (H m d && T m j) || T m (d+j)

theorem comparator_reverse (a b : Bool) :
    (!(a || b) || (!(a && b) && b)) = !a ∧
    (!(a || b) || (!(a && b) && a)) = !b := by
  cases a <;> cases b <;> decide

theorem comparator_gate_law (a b : Bool) :
    PEqualNP.CircuitLowerBounds.GateOp.eval .and [a,b] = (a && b) ∧
    PEqualNP.CircuitLowerBounds.GateOp.eval .or [a,b] = (a || b) ∧
    PEqualNP.CircuitLowerBounds.GateOp.eval .not [a] = (!a) := by
  cases a <;> cases b <;> decide

theorem unary_forward (m d j : Nat) :
    U m d j = T (if m < d then m else m-d) j := by
  by_cases hm : m < d
  · have hnot : ¬ d ≤ m := by omega
    have hnot' : ¬ d+j ≤ m := by omega
    simp [U, H, T, hm, hnot, hnot']
  · have hle : d ≤ m := by omega
    have hiff : d+j ≤ m ↔ j ≤ m-d := by omega
    simp [U, H, T, hm, hle, hiff]

theorem unary_decode_low (m d j : Nat) (hj : j < d) :
    (!(T m j)) = (H m d && (!(U m d j))) := by
  by_cases hm : m < d
  · have hnot : ¬ d ≤ m := by omega
    have hnot' : ¬ d+j ≤ m := by omega
    simp [U, H, T, hm, hnot, hnot']
  · have hle : d ≤ m := by omega
    have hjle : j ≤ m := by omega
    simp [U, H, T, hle, hjle]

theorem unary_decode_mid (m d : Nat) : (!(T m d)) = H m d := rfl

theorem unary_decode_high (m d j : Nat) :
    (!(T m (d+j))) = (H m d || (!(U m d j))) := by
  by_cases hm : m < d
  · have hnot : ¬ d ≤ m := by omega
    have hnot' : ¬ d+j ≤ m := by omega
    simp [U, H, T, hnot, hnot']
  · have hle : d ≤ m := by omega
    simp [U, H, T, hle]

theorem unary_range (k m : Nat) (hm : m ≤ k) :
    (if m < k/2+1 then m else m-(k/2+1)) ≤ k/2 := by
  split_ifs <;> omega

theorem recursion_not_budget (k r : Nat) (h : k < 2^(r+1)) : k/2 < 2^r := by
  rw [pow_succ] at h
  omega

theorem unary_fold_budget (F : Nat → Nat) (h0 : F 0 = 0)
    (hs : ∀ k : Nat, 0 < k → F k ≤ k + 2*(k/2) + F (k/2)) :
    ∀ k : Nat, F k ≤ 4*k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
      by_cases hk : k = 0
      · simp [hk, h0]
      · have hsmall : k/2 < k := by omega
        have hrec := hs k (by omega)
        have hi := ih (k/2) hsmall
        omega

theorem sorting_unsorting_budget (k : Nat) :
    3*k*(k-1) + 4*k = 3*k^2 + k := by
  cases k with
  | zero => norm_num
  | succ k =>
      simp only [Nat.succ_sub_one]
      ring

theorem total_upper_budget (k m : Nat) (hm : m ≤ 3*k^2+k) :
    m+4*k ≤ 3*k^2+13*k := by omega

end Upper1196Unary
namespace Unary1196Fold
open DervishBuild1196
open DervishBuild1196.Build
open Upper1196Unary

def thresh (m : Nat) (j : Nat) : Bool := decide (j+1 ≤ m)
def reduced (m d : Nat) : Nat := if m < d then m else m-d

private theorem forward_sem (m d j : Nat) (hd : 0 < d) :
    ((!thresh m (d-1) && thresh m j) || thresh m (d+j)) =
      thresh (reduced m d) j := by
  have h := unary_forward m d (j+1)
  have hd' : d-1+1=d := by omega
  simpa [thresh, reduced, Upper1196Unary.U, Upper1196Unary.H, Upper1196Unary.T,
    hd', Nat.add_assoc] using h

private theorem low_sem (m d j : Nat) (h : j+1 < d) :
    (!thresh m j) = (!thresh m (d-1) && !thresh (reduced m d) j) := by
  have hh := unary_decode_low m d (j+1) h
  rw [unary_forward] at hh
  have hd' : d-1+1=d := by omega
  simpa [thresh, reduced, Upper1196Unary.H, Upper1196Unary.T, hd'] using hh

private theorem high_sem (m d j : Nat) (hd : 0<d) :
    (!thresh m (d+j)) = (!thresh m (d-1) || !thresh (reduced m d) j) := by
  have hh := unary_decode_high m d (j+1)
  rw [unary_forward] at hh
  have hd' : d-1+1=d := by omega
  simpa [thresh, reduced, Upper1196Unary.H, Upper1196Unary.T, hd', Nat.add_assoc] using hh

variable {w : Nat} {X : Type} {input : X → List Bool} (hlen : ∀ x, (input x).length = w)
include hlen

private theorem forward_loop (m : X → Nat) (k d q : Nat) (hm : ∀ x, m x ≤ k)
    (hd : d=q+1) (hindex : d ≤ k) (s : Build w) (z h : Nat)
    (vz : Read input s z (fun _ => false))
    (vh : Read input s h (fun x => !thresh (m x) (d-1)))
    (tap : Nat → Nat) (vt : ∀ j, j < k → Read input s (tap j) (fun x => thresh (m x) j)) :
    ∀ n, n ≤ q → ∃ t : Build w, ∃ u : Nat → Nat,
      Ext s t ∧ t.cost ≤ s.cost+2*n ∧ t.nots = s.nots ∧
      (∀ j, j < n → Read input t (u j) (fun x => thresh (reduced (m x) d) j)) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨s,fun _ => z,List.prefix_rfl,by omega,rfl,by intro j hj; omega⟩
  | succ n ih =>
      intro hn
      obtain ⟨t,u,E,cb,nb,vu⟩ := ih (by omega)
      have vH := read_persist hlen E vh
      have vlow := read_persist hlen E (vt n (by omega))
      obtain ⟨a,ra,Ea,va,ca,na⟩ := emitAnd hlen vH vlow
      have hhi : d+n+1 ≤ k ∨ k < d+n+1 := by omega
      have vhi : Read input a (if d+n < k then tap (d+n) else z)
           (fun x => thresh (m x) (d+n)) := by
        by_cases hv : d+n < k
        · simpa [hv] using read_persist hlen (E.trans Ea) (vt (d+n) hv)
        · have zero : ∀ x, thresh (m x) (d+n) = false := by
            intro x
            simp [thresh, decide_eq_false_iff_not, show ¬ d+n+1 ≤ m x by have := hm x; omega]
          simpa only [if_neg hv, zero] using read_persist hlen (E.trans Ea) vz
      obtain ⟨b,rb,Eb,vb,cb',nb'⟩ := emitOr hlen va vhi
      refine ⟨b,fun j => if j=n then rb else u j,(E.trans Ea).trans Eb,?_,?_,?_⟩
      · omega
      · omega
      · intro j hj
        by_cases he : j=n
        · subst j
          have vr : Read input b rb (fun x => thresh (reduced (m x) d) n) := by
            convert vb using 1
            funext x
            exact (forward_sem (m x) d n (by omega)).symm
          simpa using vr
        · simpa only [if_neg he] using read_persist hlen (Ea.trans Eb) (vu j (by omega))

private theorem low_loop (m : X → Nat) (d q : Nat) (hd : d=q+1)
    (s : Build w) (h : Nat) (vh : Read input s h (fun x => !thresh (m x) (d-1)))
    (u : Nat → Nat)
    (vu : ∀ j, j<q → Read input s (u j) (fun x => !thresh (reduced (m x) d) j)) :
    ∀ n, n ≤ q → ∃ t : Build w, ∃ v : Nat → Nat,
      Ext s t ∧ t.cost ≤ s.cost+n ∧ t.nots = s.nots ∧
      (∀ j, j<n → Read input t (v j) (fun x => !thresh (m x) j)) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨s,fun _ => h,List.prefix_rfl,by omega,rfl,by intro j hj; omega⟩
  | succ n ih =>
      intro hn
      obtain ⟨t,v,E,cb,nb,vv⟩ := ih (by omega)
      obtain ⟨a,ra,Ea,va,ca,na⟩ := emitAnd hlen (read_persist hlen E vh)
        (read_persist hlen E (vu n (by omega)))
      refine ⟨a,fun j => if j=n then ra else v j,E.trans Ea,?_,?_,?_⟩
      · omega
      · omega
      · intro j hj
        by_cases he : j=n
        · subst j
          have vr : Read input a ra (fun x => !thresh (m x) n) := by
            convert va using 1
            funext x
            exact low_sem (m x) d n (by omega)
          simpa using vr
        · simpa only [if_neg he] using read_persist hlen Ea (vv j (by omega))

private theorem high_loop (m : X → Nat) (d q : Nat) (hd : d=q+1)
    (s : Build w) (h : Nat) (vh : Read input s h (fun x => !thresh (m x) (d-1)))
    (u : Nat → Nat)
    (vu : ∀ j, j<q → Read input s (u j) (fun x => !thresh (reduced (m x) d) j)) :
    ∀ n, n ≤ q → ∃ t : Build w, ∃ v : Nat → Nat,
      Ext s t ∧ t.cost ≤ s.cost+n ∧ t.nots = s.nots ∧
      (∀ j, j<n → Read input t (v j) (fun x => !thresh (m x) (d+j))) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨s,fun _ => h,List.prefix_rfl,by omega,rfl,by intro j hj; omega⟩
  | succ n ih =>
      intro hn
      obtain ⟨t,v,E,cb,nb,vv⟩ := ih (by omega)
      obtain ⟨a,ra,Ea,va,ca,na⟩ := emitOr hlen (read_persist hlen E vh)
        (read_persist hlen E (vu n (by omega)))
      refine ⟨a,fun j => if j=n then ra else v j,E.trans Ea,?_,?_,?_⟩
      · omega
      · omega
      · intro j hj
        by_cases he : j=n
        · subst j
          have vr : Read input a ra (fun x => !thresh (m x) (d+n)) := by
            convert va using 1
            funext x
            exact high_sem (m x) d n (by omega)
          simpa using vr
        · simpa only [if_neg he] using read_persist hlen Ea (vv j (by omega))

theorem invert (r : Nat) : ∀ (k : Nat) (hk : k < 2^r)
    (m : X → Nat) (hm : ∀ x, m x ≤ k)
    (s : Build w) (zero : Nat)
    (vzero : Read input s zero (fun _ => false))
    (tap : Nat → Nat)
    (vt : ∀ j, j<k → Read input s (tap j) (fun x => thresh (m x) j)),
    ∃ t : Build w, ∃ inv : Nat → Nat,
      Ext s t ∧ t.cost ≤ s.cost+4*k ∧ t.nots ≤ s.nots+r ∧
      (∀ j, j<k → Read input t (inv j) (fun x => !thresh (m x) j)) := by
  induction r with
  | zero =>
      intro k hk m hm s zero vzero tap vt
      have kz : k=0 := by simpa using hk
      subst k
      exact ⟨s,fun _ => zero,List.prefix_rfl,by omega,by omega,by intro j hj; omega⟩
  | succ r ih =>
      intro k hk m hm s zero vzero tap vt
      by_cases kz : k=0
      · subst k
        exact ⟨s,fun _ => zero,List.prefix_rfl,by omega,by omega,by intro j hj; omega⟩
      · let q := k/2
        let d := q+1
        have hq : q<k := by dsimp [q]; omega
        have hd : d≤k := by dsimp [d,q]; omega
        have hrec : q < 2^r := by
          dsimp [q]
          exact recursion_not_budget k r (by simpa using hk)
        obtain ⟨sH,H,EH,VH,cH,nH⟩ := emitNot hlen (vt q hq)
        have VHz : Read input sH zero (fun _ => false) := read_persist hlen EH vzero
        have VHT : Read input sH H (fun x => !thresh (m x) (d-1)) := by
          simpa [d,q] using VH
        have vtH : ∀ j, j<k → Read input sH (tap j) (fun x => thresh (m x) j) :=
          fun j hj => read_persist hlen EH (vt j hj)
        obtain ⟨sF,u,EF,cF,nF,vu⟩ :=
          forward_loop hlen m k d q hm (by dsimp [d]) hd sH zero H VHz VHT tap vtH q (by omega)
        have mred : ∀ x, reduced (m x) d ≤ q := by
          intro x
          simpa [reduced,d,q] using unary_range k (m x) (hm x)
        obtain ⟨sR,v,ER,cR,nR,vR⟩ :=
          ih q hrec (fun x => reduced (m x) d) mred sF zero
            (read_persist hlen EF VHz) u vu
        have VRH : Read input sR H (fun x => !thresh (m x) (d-1)) :=
          read_persist hlen (EF.trans ER) VHT
        obtain ⟨sL,l,EL,cL,nL,vl⟩ :=
          low_loop hlen m d q (by dsimp [d]) sR H VRH v vR q (by omega)
        have vHR : Read input sL H (fun x => !thresh (m x) (d-1)) :=
          read_persist hlen EL VRH
        have vrL : ∀ j, j<q → Read input sL (v j) (fun x => !thresh (reduced (m x) d) j) :=
          fun j hj => read_persist hlen EL (vR j hj)
        have hkD : k-d ≤ q := by dsimp [d,q]; omega
        obtain ⟨sT,uH,ET,cT,nT,vuH⟩ :=
          high_loop hlen m d q (by dsimp [d]) sL H vHR v vrL (k-d) hkD
        refine ⟨sT,fun j => if j<q then l j else if j=q then H else uH (j-d),
          (((EH.trans EF).trans ER).trans EL).trans ET,?_,?_,?_⟩
        · dsimp [d,q] at *
          omega
        · dsimp [d,q] at *
          omega
        · intro j hj
          by_cases jl : j<q
          · simpa [jl] using read_persist hlen ET (vl j jl)
          · by_cases je : j=q
            · subst j
              have hmid : d-1=q := by dsimp [d]
              have vr := read_persist hlen (EL.trans ET) VRH
              rw [hmid] at vr
              simpa [jl] using vr
            · have jhigh : d ≤ j := by dsimp [d]; omega
              have jbound : j-d < k-d := by omega
              have jeq : d+(j-d)=j := by omega
              simpa only [if_neg jl, if_neg je, jeq] using vuH (j-d) jbound

end Unary1196Fold

end Donor1196
namespace Wiring1270
open Dervish53156Donor.Donor1196
open DervishBuild1196 DervishBuild1196.Build

variable {n : Nat}
def input (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
theorem input_len (x : Finset (Fin n)) : (input x).length = n+2 := by simp [input]
theorem bit (x : Finset (Fin n)) (j : Fin n) :
    (input x).getD j.val false = decide (j ∈ x) := by
  rw [input, getD_append_left (by simp)]
  simp
theorem zero (x : Finset (Fin n)) : (input x).getD n false = false := by
  rw [input, List.getD_append_right _ _ _ _ (by simp)]
  simp

def good (s : Build (n+2)) (f : Finset (Fin n) → Bool) : Prop :=
  ∃ a, Read input s a f

theorem good_persist {s t : Build (n+2)} {f} (E : Ext s t)
    (h : good s f) : good t f := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a, read_persist input_len E ha⟩

theorem good_bit (s : Build (n+2)) (j : Fin n) :
    good s (fun x => decide (j ∈ x)) := by
  refine ⟨j.val,?_⟩
  have h := read_input (input := input (n:=n)) input_len s j.val (by omega : j.val<n+2)
  convert h using 1
  funext x
  exact (bit x j).symm

theorem good_zero (s : Build (n+2)) : good s (fun _ => false) := by
  refine ⟨n,?_⟩
  have h := read_input (input := input (n:=n)) input_len s n (by omega : n<n+2)
  convert h using 1
  funext x
  exact (zero x).symm

theorem good_one (s : Build (n+2)) : good s (fun _ => true) := by
  refine ⟨n+1,?_⟩
  have h := read_input (input := input (n:=n)) input_len s (n+1) (by omega : n+1<n+2)
  convert h using 1
  funext x
  rw [input, List.getD_append_right _ _ _ _ (by simp)]
  simp

def conj (y x : Finset (Fin n)) : Bool := decide (y ⊆ x)

def any_bools {I : Type} (idx : Finset I)
    (fs : I → Finset (Fin n) → Bool) (x : Finset (Fin n)) : Bool :=
  decide (∃ i ∈ idx, fs i x = true)

end Wiring1270
end Dervish53156Donor


namespace DervishSampleBasis53156
variable {n m : ℕ}
abbrev X (n : ℕ) := Finset (Fin n)

noncomputable def sampleRank (S : Finset (X n)) (h : X n → ℕ) (x : X n) : ℕ := by
  classical
  exact (S.filter (fun y => y ⊆ x)).sup h

theorem sampleRank_le (S : Finset (X n)) (h : X n → ℕ) (L : ℕ)
    (hh : ∀ y ∈ S, h y ≤ L) (x : X n) : sampleRank S h x ≤ L := by
  classical
  exact Finset.sup_le_iff.mpr (fun y hy => hh y (Finset.mem_filter.mp hy).1)

theorem sampleRank_mono (S : Finset (X n)) (h : X n → ℕ) : Monotone (sampleRank S h) := by
  classical
  intro x z hx
  apply Finset.sup_mono
  intro y hy
  obtain ⟨hyS, hxy⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_filter.mpr ⟨hyS,hxy.trans hx⟩

theorem sampleRank_on (S : Finset (X n)) (h : X n → ℕ) (hh : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x ≤ h y)
    (x : X n) (hx : x ∈ S) : sampleRank S h x = h x := by
  classical
  apply Nat.le_antisymm
  · exact Finset.sup_le_iff.mpr (fun y hy => hh y (Finset.mem_filter.mp hy).1 x hx (Finset.mem_filter.mp hy).2)
  · exact Finset.le_sup (Finset.mem_filter.mpr ⟨hx,Finset.Subset.rfl⟩)

theorem threshold_on (S : Finset (X n)) (h : X n → ℕ) (x : X n) (u : ℕ) :
    u+1 ≤ sampleRank S h x ↔ ∃ y ∈ S, y ⊆ x ∧ u+1 ≤ h y := by
  classical
  constructor
  · intro hz
    by_contra hn
    have hub : sampleRank S h x ≤ u := by
      apply Finset.sup_le_iff.mpr
      intro y hy
      obtain ⟨hyS,hyx⟩ := Finset.mem_filter.mp hy
      by_contra hbad
      exact hn ⟨y,hyS,hyx,by omega⟩
    omega
  · rintro ⟨y,hy,hyx,hu⟩
    exact hu.trans (Finset.le_sup (Finset.mem_filter.mpr ⟨hy,hyx⟩))

noncomputable def basis (S : Finset (X n)) (h : X n → ℕ) (y x : X n) : Bool := by
  classical
  exact decide (y ⊆ x ∧ sampleRank S h x ≤ h y)

noncomputable def report (S : Finset (X n)) (h : X n → ℕ) (v : X n → Fin m → Bool)
    (j : Fin m) (x : X n) : Bool := by
  classical
  exact decide (∃ y ∈ S, v y j = true ∧ basis S h y x = true)

theorem report_exact (S : Finset (X n)) (h : X n → ℕ) (v : X n → Fin m → Bool)
    (hh : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x ≤ h y)
    (hv : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x = h y → ∀ j, v x j = true → v y j = true)
    (x : X n) (hx : x ∈ S) (j : Fin m) : report S h v j x = v x j := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [report, basis, decide_eq_true_eq, sampleRank_on S h hh x hx]
  constructor
  · rintro ⟨y,hy,hyj,hyx,hhxy⟩
    exact hv y hy x hx hyx (Nat.le_antisymm (hh y hy x hx hyx) hhxy) j hyj
  · intro hxj
    exact ⟨x,hx,hxj,Finset.Subset.rfl,Nat.le_refl _⟩

end DervishSampleBasis53156


namespace DervishBudget53156
open Dervish53156Donor
open Donor1196 DervishBuild1196 DervishBuild1196.Build Wiring1270
variable {n : ℕ}
abbrev X (n : ℕ) := Finset (Fin n)

theorem goodAnd {s : Build (n+2)} {f g : X n → Bool} (hf : good s f) (hg : good s g) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+1 ∧ good t (fun x => f x && g x) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  obtain ⟨u,w,he,hr,hc,hn⟩ := emitAnd input_len ha hb
  exact ⟨u,he,hn,hc,w,hr⟩

theorem goodOr {s : Build (n+2)} {f g : X n → Bool} (hf : good s f) (hg : good s g) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+1 ∧ good t (fun x => f x || g x) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  obtain ⟨u,w,he,hr,hc,hn⟩ := emitOr input_len ha hb
  exact ⟨u,he,hn,hc,w,hr⟩

theorem conjBudget (s : Build (n+2)) (y : X n) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+y.card ∧ good t (conj y) := by
  classical
  induction y using Finset.induction_on generalizing s with
  | empty =>
    refine ⟨s,List.prefix_rfl,rfl,by simp,?_⟩
    convert good_one s using 1
    funext x
    simp [conj]
  | @insert j y hj ih =>
    obtain ⟨u,E,N,C,V⟩ := ih s
    obtain ⟨t,Et,Nt,Ct,Vt⟩ := goodAnd (good_bit u j) V
    refine ⟨t,E.trans Et,Nt.trans N,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hj]
      omega
    · convert Vt using 1
      funext x
      simp [conj, Finset.insert_subset_iff]

theorem orBudget {I : Type} [DecidableEq I] (idx : Finset I) (fs : I → X n → Bool)
    (s : Build (n+2)) (hf : ∀ j ∈ idx, good s (fs j)) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+idx.card ∧ good t (any_bools idx fs) := by
  classical
  induction idx using Finset.induction_on generalizing s with
  | empty =>
    refine ⟨s,List.prefix_rfl,rfl,by simp,?_⟩
    convert good_zero s using 1
    funext x
    simp [any_bools]
  | @insert j idx hj ih =>
    obtain ⟨u,E,N,C,V⟩ := ih s (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨t,Et,Nt,Ct,Vt⟩ := goodOr (good_persist E (hf j (Finset.mem_insert_self ..))) V
    refine ⟨t,E.trans Et,Nt.trans N,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hj]
      omega
    · convert Vt using 1
      funext x
      simp [any_bools,Finset.mem_insert]

theorem buildMany {I : Type} [DecidableEq I] (idx : Finset I) (fs : I → X n → Bool)
    (C : ℕ) (s₀ s : Build (n+2)) (E₀ : Ext s₀ s)
    (make : ∀ i ∈ idx, ∀ u : Build (n+2), Ext s₀ u →
      ∃ t, Ext u t ∧ t.nots = u.nots ∧ t.cost ≤ u.cost+C ∧ good t (fs i)) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+idx.card*C ∧ ∀ i ∈ idx, good t (fs i) := by
  classical
  induction idx using Finset.induction_on generalizing s with
  | empty => exact ⟨s,List.prefix_rfl,rfl,by simp,by simp⟩
  | @insert j idx hj ih =>
    obtain ⟨u,E,N,H,V⟩ := make j (Finset.mem_insert_self ..) s E₀
    obtain ⟨t,Et,Nt,Ht,Vt⟩ := ih u (E₀.trans E)
      (fun i hi => make i (Finset.mem_insert_of_mem hi))
    refine ⟨t,E.trans Et,Nt.trans N,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hj, Nat.add_mul, Nat.one_mul]
      omega
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact good_persist Et V
      · exact Vt i hi

end DervishBudget53156

namespace DervishCeil53156
open Dervish53156Donor
open Donor1196 DervishBuild1196 DervishBuild1196.Build Wiring1270
open DervishSampleBasis53156 DervishBudget53156
variable {n : ℕ}

theorem sampleContainments (S : Finset (Finset (Fin n))) (s : Build (n+2)) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+S.card*n ∧ ∀ y ∈ S, good t (conj y) := by
  apply buildMany S conj n s s List.prefix_rfl
  intro y hy u _
  obtain ⟨t,E,N,C,V⟩ := conjBudget u y
  have hy' : y.card ≤ n := by
    simpa using (Finset.card_le_univ y)
  exact ⟨t,E,N,by omega,V⟩

theorem positiveThresholds (S : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℕ)
    (L : ℕ) (s : Build (n+2)) (hs : ∀ y ∈ S, good s (conj y)) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+L*S.card ∧
      ∀ l : Fin L, good t (fun x => decide (l.val+1 ≤ sampleRank S h x)) := by
  classical
  let idx : Finset (Fin L) := Finset.univ
  let fs (j : Fin L) (x : Finset (Fin n)) : Bool := decide (j.val+1 ≤ sampleRank S h x)
  have make (i : Fin L) (_ : i ∈ idx) (u : Build (n+2)) (E : Ext s u) :
      ∃ t, Ext u t ∧ t.nots = u.nots ∧ t.cost ≤ u.cost+S.card ∧ good t (fs i) := by
    let ys := S.filter (fun y => i.val+1 ≤ h y)
    have hs' : ∀ y ∈ ys, good u (conj y) := fun y hy =>
      good_persist E (hs y (Finset.mem_filter.mp hy).1)
    obtain ⟨t,Et,Nt,Ct,Vt⟩ := orBudget ys conj u hs'
    have hsz : ys.card ≤ S.card := Finset.card_filter_le _ _
    have eq : any_bools ys conj = fs i := by
      funext x
      apply Bool.eq_iff_iff.mpr
      simp only [any_bools,ys,fs,conj,decide_eq_true_eq,Finset.mem_filter,threshold_on]
      constructor
      · rintro ⟨y,⟨hy,hr⟩,hx⟩
        exact ⟨y,hy,hx,hr⟩
      · rintro ⟨y,hy,hx,hr⟩
        exact ⟨y,⟨hy,hr⟩,hx⟩
    rw [eq] at Vt
    exact ⟨t,Et,Nt,by omega,Vt⟩
  obtain ⟨t,E,N,C,H⟩ := buildMany idx fs S.card s s List.prefix_rfl make
  exact ⟨t,E,N,by simpa [idx] using C,fun i => H i (Finset.mem_univ _)⟩

theorem ceilThresholds (S : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℕ)
    (L b : ℕ) (hPow : L < 2^b) (hBound : ∀ y ∈ S, h y ≤ L)
    (s : Build (n+2))
    (hs : ∀ l : Fin L, good s (fun x => decide (l.val+1 ≤ sampleRank S h x))) :
    ∃ t, Ext s t ∧ t.nots ≤ s.nots+b ∧ t.cost ≤ s.cost+4*L ∧
      ∀ y ∈ S, good t (fun x => decide (sampleRank S h x ≤ h y)) := by
  classical
  let R := sampleRank S h
  have hm : ∀ x, R x ≤ L := sampleRank_le S h L hBound
  choose addr hr using hs
  obtain ⟨z,hz⟩ := good_zero s
  let tap (j : ℕ) : ℕ := if hj : j < L then addr ⟨j,hj⟩ else z
  have vow : ∀ j, j<L → Read input s (tap j) (fun x => Unary1196Fold.thresh (R x) j) := by
    intro j hj
    simpa only [tap,dif_pos hj,R,Unary1196Fold.thresh] using (hr ⟨j,hj⟩)
  obtain ⟨t,it,E,C,N,vi⟩ := Unary1196Fold.invert
    (input := input (n:=n)) input_len b L hPow R hm s z hz tap vow
  refine ⟨t,E,N,C,?_⟩
  intro y hy
  by_cases hlt : h y < L
  · refine ⟨it (h y),?_⟩
    convert vi (h y) hlt using 1
    funext x
    change decide (R x ≤ h y) = !(decide (h y+1 ≤ R x))
    by_cases he : R x ≤ h y
    · have hn : ¬ h y+1 ≤ R x := by omega
      simp [he,hn]
    · have hp : h y+1 ≤ R x := by omega
      simp [he,hp]
  · convert good_one t using 1
    funext x
    exact decide_eq_true ((hm x).trans (Nat.le_of_not_gt hlt))

end DervishCeil53156

namespace DervishCompileSlot53156
open PEqualNP PEqualNP.CircuitLowerBounds
open Dervish53156Donor
open Donor1196 DervishBuild1196 DervishBuild1196.Build Wiring1270
open DervishSampleBasis53156 DervishBudget53156 DervishCeil53156
variable {n m : ℕ}

theorem basisBank (S : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℕ) (s : Build (n+2))
    (hc : ∀ y ∈ S, good s (conj y))
    (hr : ∀ y ∈ S, good s (fun x => decide (sampleRank S h x ≤ h y))) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+S.card ∧
      ∀ y ∈ S, good t (basis S h y) := by
  classical
  have hMany := buildMany S (basis S h) 1 s s List.prefix_rfl
  obtain ⟨t,E,N,C,H⟩ := hMany (by
    intro y hy u e
    obtain ⟨v,Ev,Nv,Cv,Vv⟩ := goodAnd (good_persist e (hc y hy)) (good_persist e (hr y hy))
    refine ⟨v,Ev,Nv,Cv,?_⟩
    convert Vv using 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [basis,conj,Bool.and_eq_true,decide_eq_true_eq])
  exact ⟨t,E,N,by simpa using C,H⟩

theorem reportBank (S : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℕ)
    (v : Finset (Fin n) → Fin m → Bool) (s : Build (n+2))
    (hs : ∀ y ∈ S, good s (basis S h y)) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+m*S.card ∧
      ∀ j, good t (report S h v j) := by
  classical
  let idx : Finset (Fin m) := Finset.univ
  have make (j : Fin m) (_ : j ∈ idx) (u : Build (n+2)) (E : Ext s u) :
      ∃ t, Ext u t ∧ t.nots = u.nots ∧ t.cost ≤ u.cost+S.card ∧ good t (report S h v j) := by
    let ys := S.filter (fun y => v y j = true)
    obtain ⟨t,E',N,C,H⟩ := orBudget ys (basis S h) u
      (fun y hy => good_persist E (hs y (Finset.mem_filter.mp hy).1))
    have hCard : ys.card ≤ S.card := Finset.card_filter_le _ _
    refine ⟨t,E',N,by omega,?_⟩
    convert H using 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [report,any_bools,ys,Finset.mem_filter,decide_eq_true_eq,and_assoc]
  obtain ⟨t,E,N,C,H⟩ := buildMany idx (report S h v) S.card s s List.prefix_rfl make
  exact ⟨t,E,N,by simpa [idx] using C,fun j => H j (Finset.mem_univ _)⟩

private theorem cost_arithmetic (n m s L : ℕ) (hL : L ≤ n) :
    s*n + L*s + 4*L + s + m*s ≤ 32*(n+1)*(m+1)*(s+1) := by
  have hls := Nat.mul_le_mul_right s hL
  have h4 := Nat.mul_le_mul_left 4 hL
  calc
    s*n + L*s + 4*L + s + m*s ≤ s*n + n*s + 4*n + s + m*s := by omega
    _ ≤ 32*(n+1)*(m+1)*(s+1) := by ring_nf; omega

theorem compile_slot (S : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℕ)
    (v : Finset (Fin n) → Fin m → Bool) (L b : ℕ) (hL : L ≤ n) (hPow : L < 2^b)
    (hBound : ∀ y ∈ S, h y ≤ L)
    (hh : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x ≤ h y)
    (hv : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x = h y → ∀ j, v x j = true → v y j = true) :
    ∃ (C : Circuit) (tap : Fin m → Fin (n+2+C.size)),
      MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ NotBracket.notCount C ≤ b ∧
      C.size ≤ 32*(n+1)*(m+1)*(S.card+1) ∧
      ∀ x ∈ S, ∀ j, (C.wires (input x)).getD (tap j).val false = v x j := by
  classical
  let s : Build (n+2) := Build.empty _
  obtain ⟨u,_,N₁,C₁,V₁⟩ := sampleContainments S s
  obtain ⟨p,E₂,N₂,C₂,V₂⟩ := positiveThresholds S h L u V₁
  obtain ⟨a,E₃,N₃,C₃,V₃⟩ := ceilThresholds S h L b hPow hBound p V₂
  obtain ⟨d,_,N₄,C₄,V₄⟩ := basisBank S h a
    (fun y hy => good_persist (E₂.trans E₃) (V₁ y hy)) V₃
  obtain ⟨e,_,N₅,C₅,V₅⟩ := reportBank S h v d V₄
  have hzero : s.cost = 0 ∧ s.nots = 0 := by
    simp [s,Build.empty,Build.cost,Build.nots,Build.circ,NotBracket.notCount]
  have hBig := cost_arithmetic n m S.card L hL
  have hCost : e.cost ≤ 32*(n+1)*(m+1)*(S.card+1) := by omega
  have hNots : e.nots ≤ b := by omega
  choose addr hadd using V₅
  let C : Circuit := ⟨e.gates,0⟩
  let tap : Fin m → Fin (n+2+C.size) := fun j =>
    ⟨addr j, by
      have h := (hadd j).1
      simpa only [C,Circuit.size,Build.size,Build.cost] using h⟩
  refine ⟨C,tap,e.fan,e.back,by simp [C],hNots,hCost,?_⟩
  intro x hx j
  exact ((hadd j).2 x).trans (report_exact S h v hh hv x hx j)

end DervishCompileSlot53156



namespace Endpoint53156Prefix

noncomputable def prefixCount (T : Nat) (t : Fin T) (q : Nat) : Nat :=
  ((Finset.range q).filter (fun a => a % T = t.val)).card

lemma prefixCount_diff (T : Nat) (t : Fin T) (R B : Nat) (hRB : R ≤ B) :
    (((Finset.Ico R B).filter (fun a => a % T = t.val)).card) =
    prefixCount T t B - prefixCount T t R := by
  classical
  have hrange : Finset.range B = Finset.range R ∪ Finset.Ico R B := by
    ext q
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint ((Finset.range R).filter (fun a => a % T = t.val))
      ((Finset.Ico R B).filter (fun a => a % T = t.val)) := by
    apply Finset.disjoint_left.mpr
    intro q hq hr
    have h1 := (Finset.mem_filter.mp hq).1
    have h2 := (Finset.mem_filter.mp hr).1
    have h1' := Finset.mem_range.mp h1
    have h2' := Finset.mem_Ico.mp h2
    omega
  have hsum : prefixCount T t B = prefixCount T t R +
      ((Finset.Ico R B).filter (fun a => a % T = t.val)).card := by
    unfold prefixCount
    rw [hrange, Finset.filter_union, Finset.card_union_of_disjoint hdisj]
  omega

lemma prefixCount_high_iff (T : Nat) (t : Fin T) (R B : Nat) (hRB : R ≤ B) :
    prefixCount T t R < prefixCount T t B ↔
    ∃ q : Nat, R ≤ q ∧ q < B ∧ q % T = t.val := by
  classical
  rw [← Nat.sub_pos_iff_lt, ← prefixCount_diff T t R B hRB]
  constructor
  · intro hpos
    obtain ⟨q,hq⟩ := Finset.card_pos.mp hpos
    have hqi : q ∈ Finset.Ico R B := (Finset.mem_filter.mp hq).1
    have hmod : q % T = t.val := (Finset.mem_filter.mp hq).2
    have hlo : R ≤ q := (Finset.mem_Ico.mp hqi).1
    have hhi : q < B := (Finset.mem_Ico.mp hqi).2
    exact ⟨q,hlo,hhi,hmod⟩
  · rintro ⟨q,hlo,hhi,hmod⟩
    apply Finset.card_pos.mpr
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlo,hhi⟩,hmod⟩⟩

lemma prefixCount_mono (T : Nat) (t : Fin T) {a c : Nat} (hac : a ≤ c) :
    prefixCount T t a ≤ prefixCount T t c := by
  unfold prefixCount
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqa,hqt⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hqa) hac),hqt⟩

lemma prefixCount_le_cap (T n q : Nat) (hT : 0 < T) (hq : q ≤ T*n) (t : Fin T) :
    prefixCount T t q ≤ n := by
  classical
  let s : Finset Nat := (Finset.range q).filter (fun a => a % T = t.val)
  have hinj : Set.InjOn (fun a : Nat => a/T) ↑s := by
    intro a ha c hc hdiv
    have ha' : a % T = t.val := (Finset.mem_filter.mp ha).2
    have hc' : c % T = t.val := (Finset.mem_filter.mp hc).2
    have hdiv' : a / T = c / T := hdiv
    calc
      a = a % T + T*(a/T) := (Nat.mod_add_div a T).symm
      _ = c % T + T*(c/T) := by rw [ha', hc', hdiv']
      _ = c := Nat.mod_add_div c T
  have hsubset : s.image (fun a : Nat => a/T) ⊆ Finset.range n := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have ha_lt : a < q := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have ha_cap : a < T*n := lt_of_lt_of_le ha_lt hq
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hT).mpr (by simpa [mul_comm] using ha_cap))
  calc
    prefixCount T t q = s.card := rfl
    _ = (s.image (fun a : Nat => a/T)).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range n).card := Finset.card_le_card hsubset
    _ = n := Finset.card_range n

lemma high_mono_of_equal_prefixCount (T : Nat) (t : Fin T)
    {R B R' B' : Nat} (_hR : R ≤ R') (hB : B ≤ B')
    (hA : prefixCount T t R = prefixCount T t R') :
    prefixCount T t R < prefixCount T t B →
    prefixCount T t R' < prefixCount T t B' := by
  intro hhigh
  have hPB := prefixCount_mono T t hB
  omega


end Endpoint53156Prefix

namespace DervishRepresentatives53156
open Endpoint53156Prefix

private theorem mul_add_lt_iff {T q j : Nat} (hT : 0 < T) (t : Fin T) :
    T*j+t.val < q ↔ j < q/T + (if t.val < q % T then 1 else 0) := by
  have hd := Nat.mod_add_div q T
  have hr := Nat.mod_lt q hT
  have ht := t.isLt
  by_cases hl : j < q/T
  · have hmul := Nat.mul_le_mul_left T (show j+1 ≤ q/T by omega)
    rw [Nat.mul_succ] at hmul
    constructor <;> intro hh <;> omega
  by_cases he : j = q/T
  · subst j
    by_cases hq : t.val < q % T <;> simp only [hq,if_true,if_false] <;> omega
  · have hmul := Nat.mul_le_mul_left T (show q/T+1 ≤ j by omega)
    rw [Nat.mul_succ] at hmul
    by_cases hq : t.val < q % T <;> simp only [hq,if_true,if_false] <;> omega

theorem prefix_formula (T q : Nat) (hT : 0 < T) (t : Fin T) :
    prefixCount T t q = q/T + (if t.val < q % T then 1 else 0) := by
  classical
  let s := (Finset.range q).filter (fun a => a % T = t.val)
  have hi : Set.InjOn (fun a : Nat => a/T) ↑s := by
    intro a ha b hb hdiv
    change a / T = b / T at hdiv
    have ha' : a % T = t.val := (Finset.mem_filter.mp ha).2
    have hb' : b % T = t.val := (Finset.mem_filter.mp hb).2
    calc
      a = a % T + T*(a/T) := (Nat.mod_add_div a T).symm
      _ = b % T + T*(b/T) := by rw [ha',hb',hdiv]
      _ = b := Nat.mod_add_div b T
  have himg : s.image (fun a : Nat => a/T) = Finset.range (q/T+(if t.val < q % T then 1 else 0)) := by
    ext j
    simp only [Finset.mem_image,Finset.mem_range]
    constructor
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨h1,h2⟩ := Finset.mem_filter.mp ha
      apply (mul_add_lt_iff hT t).mp
      have hd := Nat.mod_add_div a T
      rw [h2] at hd
      have h := Finset.mem_range.mp h1
      omega
    · intro hj
      have ht : t.val < T := t.isLt
      let a := t.val+T*j
      have hm : a % T = t.val := by simp [a, Nat.mod_eq_of_lt ht]
      have hd : a/T = j := by
        have h := Nat.mod_add_div a T
        rw [hm] at h
        have he : T*(a/T)=T*j := by simpa [a] using (Nat.add_left_cancel h)
        exact Nat.eq_of_mul_eq_mul_left hT he
      have hlt : a < q := by
        have h := (mul_add_lt_iff hT t).mpr hj
        simpa [a,Nat.add_comm] using h
      exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt,hm⟩,hd⟩
  calc
    prefixCount T t q = s.card := rfl
    _ = (s.image (fun a : Nat => a/T)).card := (Finset.card_image_iff.mpr hi).symm
    _ = _ := by rw [himg,Finset.card_range]

variable {I J : Type} [DecidableEq I] [DecidableEq J] [Fintype J]

def breaks (T : Nat) (hT : 0 < T) (S : Finset I) (R : I → Nat) (B : I → J → Nat) : Finset (Fin T) :=
  insert ⟨0,hT⟩ ((S.image (fun x => ⟨R x % T, Nat.mod_lt _ hT⟩)) ∪
    ((S ×ˢ (Finset.univ : Finset J)).image (fun p => ⟨B p.1 p.2 % T, Nat.mod_lt _ hT⟩)))

theorem breaks_card (T : Nat) (hT : 0 < T) (S : Finset I) (R : I → Nat) (B : I → J → Nat) :
    (breaks T hT S R B).card ≤ 1+(Fintype.card J+1)*S.card := by
  classical
  let X : Finset (Fin T) := S.image (fun x => ⟨R x % T, Nat.mod_lt _ hT⟩)
  let Y : Finset (Fin T) := (S ×ˢ (Finset.univ : Finset J)).image
    (fun p => ⟨B p.1 p.2 % T, Nat.mod_lt _ hT⟩)
  have hx : X.card ≤ S.card := Finset.card_image_le
  have hy : Y.card ≤ S.card * Fintype.card J := by
    simpa only [Y,Finset.card_product,Finset.card_univ] using
      (Finset.card_image_le (s := S ×ˢ (Finset.univ : Finset J))
        (f := fun p => (⟨B p.1 p.2 % T, Nat.mod_lt _ hT⟩ : Fin T)))
  calc
    (breaks T hT S R B).card ≤ (X ∪ Y).card + 1 := Finset.card_insert_le _ _
    _ ≤ X.card + Y.card + 1 := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 1 + (Fintype.card J+1)*S.card := by
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (Fintype.card J) S.card]
      omega

theorem shares_breaks (T : Nat) (hT : 0 < T) (S : Finset I) (R : I → Nat) (B : I → J → Nat)
    (t : Fin T) : ∃ r ∈ breaks T hT S R B,
      (∀ x ∈ S, prefixCount T r (R x) = prefixCount T t (R x)) ∧
      (∀ x ∈ S, ∀ j, prefixCount T r (B x j) = prefixCount T t (B x j)) := by
  classical
  let K := breaks T hT S R B
  let Kt := K.filter (fun c => c ≤ t)
  have hne : Kt.Nonempty := ⟨⟨0,hT⟩,Finset.mem_filter.mpr
    ⟨Finset.mem_insert_self ..,show (⟨0,hT⟩ : Fin T) ≤ t from Nat.zero_le _⟩⟩
  let r := Kt.max' hne
  have hrm : r ∈ Kt := Finset.max'_mem Kt hne
  obtain ⟨hrK,hrt⟩ := Finset.mem_filter.mp hrm
  have share (q : Nat) (hq : (⟨q % T,Nat.mod_lt _ hT⟩ : Fin T) ∈ K) :
      prefixCount T r q = prefixCount T t q := by
    have he : r.val < q % T ↔ t.val < q % T := by
      constructor
      · intro h
        by_contra hn
        have hc : (⟨q % T,Nat.mod_lt _ hT⟩ : Fin T) ≤ r :=
          Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hq,Nat.le_of_not_gt hn⟩)
        exact (not_lt_of_ge hc) h
      · intro h
        exact lt_of_le_of_lt hrt h
    rw [prefix_formula T q hT r,prefix_formula T q hT t]
    simp only [he]
  refine ⟨r,hrK,?_,?_⟩
  · intro x hx
    apply share
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  · intro x hx j
    apply share
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(x,j),Finset.mem_product.mpr ⟨hx,Finset.mem_univ _⟩,rfl⟩

end DervishRepresentatives53156


namespace Endpoint53156

variable {n m T b : Nat}
abbrev X (n : Nat) := Finset (Fin n)
variable (S : Finset (X n)) (lo hi : X n → Fin m → Nat)

def drop (x y : X n) : Nat := (Finset.univ : Finset (Fin m)).sup (fun j => lo x j - hi y j)

def path (x : X n) (v : Nat) : Prop :=
  ∃ (k : Nat) (xs : Fin (k+1) → X n),
    (∀ i, xs i ∈ S) ∧ (∀ i : Fin k, xs i.castSucc ⊆ xs i.succ) ∧
    xs (Fin.last k) = x ∧
    (Finset.univ : Finset (Fin k)).sum (fun i => drop lo hi (xs i.castSucc) (xs i.succ)) = v

noncomputable def rank (x : X n) : Nat := sSup {v : Nat | path S lo hi x v}

def lowerEnd (R : X n → Nat) (x : X n) (j : Fin m) : Nat :=
  (S.filter (fun y => y ⊆ x)).sup (fun y => R y + lo y j)

lemma lowerEnd_bounds (R : X n → Nat)
    (hstep : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → R x + drop lo hi x y ≤ R y)
    (hvalid : ∀ x ∈ S, ∀ j, lo x j ≤ hi x j ∧ hi x j ≤ T)
    (x : X n) (hx : x ∈ S) (j : Fin m) :
    R x + lo x j ≤ lowerEnd S lo R x j ∧
    lowerEnd S lo R x j ≤ R x + hi x j ∧
    lowerEnd S lo R x j ≤ R x + T := by
  have hmem : x ∈ S.filter (fun y => y ⊆ x) := Finset.mem_filter.mpr ⟨hx, Finset.Subset.rfl⟩
  have hlow : R x + lo x j ≤ lowerEnd S lo R x j := by
    unfold lowerEnd
    exact Finset.le_sup (f := fun y => R y + lo y j) hmem
  have hhigh : lowerEnd S lo R x j ≤ R x + hi x j := by
    unfold lowerEnd
    apply Finset.sup_le
    intro y hy
    obtain ⟨hyS, hyx⟩ := Finset.mem_filter.mp hy
    have hj : lo y j - hi x j ≤ drop lo hi y x := by
      exact Finset.le_sup (f := fun j => lo y j - hi x j) (Finset.mem_univ j)
    have hr := hstep y hyS x hx hyx
    omega
  exact ⟨hlow, hhigh, hhigh.trans (Nat.add_le_add_left (hvalid x hx j).2 _)⟩

lemma rank_path
    (hchains : ∀ (k : Nat) (xs : Fin (k+1) → X n),
      (∀ i, xs i ∈ S) → (∀ i : Fin k, xs i.castSucc ⊆ xs i.succ) →
      (Finset.univ : Finset (Fin k)).sum
        (fun i => drop lo hi (xs i.castSucc) (xs i.succ)) ≤ T*(2^b-1))
    (x : X n) (hx : x ∈ S) :
    path S lo hi x (rank S lo hi x) := by
  have hzero : path S lo hi x 0 := by
    refine ⟨0, (fun _ => x), ?_, ?_, ?_, ?_⟩
    · intro i; exact hx
    · intro i; exact i.elim0
    · rfl
    · simp
  have hn : {v | path S lo hi x v}.Nonempty := ⟨0, hzero⟩
  have hb : BddAbove {v | path S lo hi x v} := by
    refine ⟨T*(2^b-1), ?_⟩
    intro v hv
    obtain ⟨k, xs, hS, hmono, _, hsum⟩ := hv
    rw [← hsum]
    exact hchains k xs hS hmono
  exact Nat.sSup_mem hn hb

lemma rank_le_of_chains
    (hchains : ∀ (k : Nat) (xs : Fin (k+1) → X n),
      (∀ i, xs i ∈ S) → (∀ i : Fin k, xs i.castSucc ⊆ xs i.succ) →
      (Finset.univ : Finset (Fin k)).sum
        (fun i => drop lo hi (xs i.castSucc) (xs i.succ)) ≤ T*(2^b-1))
    (x : X n) (hx : x ∈ S) : rank S lo hi x ≤ T*(2^b-1) := by
  obtain ⟨k, xs, hS, hmono, _, hsum⟩ := rank_path S lo hi hchains x hx
  rw [← hsum]
  exact hchains k xs hS hmono

lemma path_extend {x y : X n} {v : Nat} (hp : path S lo hi x v)
    (hy : y ∈ S) (hxy : x ⊆ y) : path S lo hi y (v + drop lo hi x y) := by
  obtain ⟨k, xs, hS, hm, he, hw⟩ := hp
  let ys : Fin (k+2) → X n := Fin.snoc xs y
  refine ⟨k+1, ys, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [ys] using hy
    · simpa [ys] using hS i
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [ys, he] using hxy
    · simpa only [Fin.succ_castSucc, ys, Fin.snoc_castSucc] using hm i
  · simp [ys]
  · rw [Fin.sum_univ_castSucc]
    simp only [ys, Fin.succ_castSucc, Fin.snoc_castSucc]
    simpa [he] using congrArg (fun z : Nat => z + drop lo hi x y) hw

lemma rank_step
    (hchains : ∀ (k : Nat) (xs : Fin (k+1) → X n),
      (∀ i, xs i ∈ S) → (∀ i : Fin k, xs i.castSucc ⊆ xs i.succ) →
      (Finset.univ : Finset (Fin k)).sum
        (fun i => drop lo hi (xs i.castSucc) (xs i.succ)) ≤ T*(2^b-1))
    (x : X n) (hx : x ∈ S) (y : X n) (hy : y ∈ S) (hxy : x ⊆ y) :
    rank S lo hi x + drop lo hi x y ≤ rank S lo hi y := by
  have hp := path_extend S lo hi (rank_path S lo hi hchains x hx) hy hxy
  have hb : BddAbove {v | path S lo hi y v} := by
    refine ⟨T*(2^b-1), ?_⟩
    intro v hv
    obtain ⟨k, xs, hS, hmono, _, hsum⟩ := hv
    rw [← hsum]
    exact hchains k xs hS hmono
  exact le_csSup hb hp

lemma sample_endpoint
    (hchains : ∀ (k : Nat) (xs : Fin (k+1) → X n),
      (∀ i, xs i ∈ S) → (∀ i : Fin k, xs i.castSucc ⊆ xs i.succ) →
      (Finset.univ : Finset (Fin k)).sum
        (fun i => drop lo hi (xs i.castSucc) (xs i.succ)) ≤ T*(2^b-1))
    (hvalid : ∀ x ∈ S, ∀ j, lo x j ≤ hi x j ∧ hi x j ≤ T)
    (x : X n) (hx : x ∈ S) (j : Fin m) :
    rank S lo hi x + lo x j ≤ lowerEnd S lo (rank S lo hi) x j ∧
    lowerEnd S lo (rank S lo hi) x j ≤ rank S lo hi x + hi x j ∧
    lowerEnd S lo (rank S lo hi) x j ≤ rank S lo hi x + T := by
  exact lowerEnd_bounds S lo hi (rank S lo hi)
    (rank_step S lo hi hchains) hvalid x hx j


def rankEnd (R : X n → Nat) (x : X n) : Nat :=
  (S.filter (fun y => y ⊆ x)).sup R

lemma rankEnd_sample
    (hchains : ∀ (k : Nat) (xs : Fin (k+1) → X n),
      (∀ i, xs i ∈ S) → (∀ i : Fin k, xs i.castSucc ⊆ xs i.succ) →
      (Finset.univ : Finset (Fin k)).sum
        (fun i => drop lo hi (xs i.castSucc) (xs i.succ)) ≤ T*(2^b-1))
    (x : X n) (hx : x ∈ S) :
    rankEnd S (rank S lo hi) x = rank S lo hi x := by
  have hmem : x ∈ S.filter (fun y => y ⊆ x) :=
    Finset.mem_filter.mpr ⟨hx, Finset.Subset.rfl⟩
  apply Nat.le_antisymm
  · unfold rankEnd
    apply Finset.sup_le
    intro y hy
    obtain ⟨hyS, hyx⟩ := Finset.mem_filter.mp hy
    have h := rank_step S lo hi hchains y hyS x hx hyx
    omega
  · exact Finset.le_sup (f := rank S lo hi) hmem

lemma endpoints_global
    (hchains : ∀ (k : Nat) (xs : Fin (k+1) → X n),
      (∀ i, xs i ∈ S) → (∀ i : Fin k, xs i.castSucc ⊆ xs i.succ) →
      (Finset.univ : Finset (Fin k)).sum
        (fun i => drop lo hi (xs i.castSucc) (xs i.succ)) ≤ T*(2^b-1))
    (hvalid : ∀ x ∈ S, ∀ j, lo x j ≤ hi x j ∧ hi x j ≤ T)
    (x : X n) (j : Fin m) :
    rankEnd S (rank S lo hi) x ≤ T*(2^b-1) ∧
    rankEnd S (rank S lo hi) x ≤ lowerEnd S lo (rank S lo hi) x j ∧
    lowerEnd S lo (rank S lo hi) x j ≤ rankEnd S (rank S lo hi) x + T := by
  have hcap : rankEnd S (rank S lo hi) x ≤ T*(2^b-1) := by
    unfold rankEnd
    apply Finset.sup_le
    intro y hy
    exact rank_le_of_chains S lo hi hchains y (Finset.mem_filter.mp hy).1
  have hlow : rankEnd S (rank S lo hi) x ≤
      lowerEnd S lo (rank S lo hi) x j := by
    unfold rankEnd lowerEnd
    apply Finset.sup_le
    intro y hy
    exact (Nat.le_add_right _ _).trans
      (Finset.le_sup (f := fun y => rank S lo hi y + lo y j) hy)
  have hhigh : lowerEnd S lo (rank S lo hi) x j ≤
      rankEnd S (rank S lo hi) x + T := by
    unfold lowerEnd
    apply Finset.sup_le
    intro y hy
    have hr : rank S lo hi y ≤ rankEnd S (rank S lo hi) x := by
      unfold rankEnd
      exact Finset.le_sup (f := rank S lo hi) hy
    have hlo : lo y j ≤ T :=
      ((hvalid y (Finset.mem_filter.mp hy).1 j).1).trans
        ((hvalid y (Finset.mem_filter.mp hy).1 j).2)
    omega
  exact ⟨hcap, hlow, hhigh⟩

lemma endpoints_sample
    (hchains : ∀ (k : Nat) (xs : Fin (k+1) → X n),
      (∀ i, xs i ∈ S) → (∀ i : Fin k, xs i.castSucc ⊆ xs i.succ) →
      (Finset.univ : Finset (Fin k)).sum
        (fun i => drop lo hi (xs i.castSucc) (xs i.succ)) ≤ T*(2^b-1))
    (hvalid : ∀ x ∈ S, ∀ j, lo x j ≤ hi x j ∧ hi x j ≤ T)
    (x : X n) (hx : x ∈ S) (j : Fin m) :
    rankEnd S (rank S lo hi) x + lo x j ≤ lowerEnd S lo (rank S lo hi) x j ∧
    lowerEnd S lo (rank S lo hi) x j ≤ rankEnd S (rank S lo hi) x + hi x j := by
  rw [rankEnd_sample S lo hi hchains x hx]
  exact ⟨(sample_endpoint S lo hi hchains hvalid x hx j).1,
    (sample_endpoint S lo hi hchains hvalid x hx j).2.1⟩


end Endpoint53156


namespace Endpoint53156Residue

noncomputable def slots (T R B : Nat) (hT : 0 < T) : Finset (Fin T) :=
  (Finset.Ico R B).image (fun q : Nat => (⟨q % T, Nat.mod_lt q hT⟩ : Fin T))

lemma slots_card (T R B : Nat) (hT : 0 < T) (hwidth : B ≤ R + T) :
    (slots T R B hT).card = B - R := by
  classical
  unfold slots
  rw [Finset.card_image_iff.mpr ?_, Nat.card_Ico]
  intro a ha c hc heq
  have ha' : R ≤ a ∧ a < B := Finset.mem_Ico.mp ha
  have hc' : R ≤ c ∧ c < B := Finset.mem_Ico.mp hc
  have hm : a % T = c % T := congrArg Fin.val heq
  rcases le_total a c with hac | hca
  · by_contra hneq
    have hp : 0 < c - a := by omega
    have hlt : c - a < T := by omega
    have hdvd : T ∣ c - a := Nat.ModEq.dvd' hm
    have := Nat.le_of_dvd hp hdvd
    omega
  · by_contra hneq
    have hp : 0 < a - c := by omega
    have hlt : a - c < T := by omega
    have hdvd : T ∣ a - c := Nat.ModEq.dvd' hm.symm
    have := Nat.le_of_dvd hp hdvd
    omega

lemma slots_mem (T R B : Nat) (hT : 0 < T) (t : Fin T) :
    t ∈ slots T R B hT ↔ ∃ q : Nat, R ≤ q ∧ q < B ∧ q % T = t.val := by
  classical
  unfold slots
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, ht⟩
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hq
    exact ⟨q, hlo, hhi, congrArg Fin.val ht⟩
  · rintro ⟨q,hlo,hhi,hmod⟩
    exact ⟨q, Finset.mem_Ico.mpr ⟨hlo,hhi⟩, Fin.ext hmod⟩

end Endpoint53156Residue


namespace Endpoint53156Card

variable {n m T : Nat}
abbrev X (n : Nat) := Finset (Fin n)
variable (S : Finset (X n)) (lo hi : X n → Fin m → Nat)

def drop (x y : X n) : Nat := (Finset.univ : Finset (Fin m)).sup (fun j => lo x j - hi y j)

lemma edge_card (hvalid : ∀ x ∈ S, ∀ j, lo x j ≤ hi x j ∧ hi x j ≤ T)
    (x y : X n) (hx : x ∈ S) (hxy : x ⊆ y) :
    drop lo hi x y ≤ T * (y.card - x.card) := by
  have hdT : drop lo hi x y ≤ T := by
    unfold drop
    apply Finset.sup_le
    intro j _
    have hj := hvalid x hx j
    omega
  by_cases heq : x = y
  · subst y
    have hzero : drop lo hi x x = 0 := by
      apply Nat.eq_zero_of_le_zero
      unfold drop
      apply Finset.sup_le
      intro j _
      exact Nat.le_zero.mpr (Nat.sub_eq_zero_of_le (hvalid x hx j).1)
    simp [hzero]
  · have hstrict : x ⊂ y := Finset.ssubset_iff_subset_ne.mpr ⟨hxy, heq⟩
    have hcard := Finset.card_lt_card hstrict
    have hdiff : 1 ≤ y.card - x.card := by omega
    nlinarith

lemma chain_card_bound (hvalid : ∀ x ∈ S, ∀ j, lo x j ≤ hi x j ∧ hi x j ≤ T)
    (k : Nat) (xs : Fin (k+1) → X n) (hs : ∀ i, xs i ∈ S)
    (hm : ∀ i : Fin k, xs i.castSucc ⊆ xs i.succ) :
    (Finset.univ : Finset (Fin k)).sum
      (fun i => drop lo hi (xs i.castSucc) (xs i.succ)) ≤
      T * (xs (Fin.last k)).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    let ys : Fin (k+1) → X n := fun i => xs i.castSucc
    have hys : ∀ i, ys i ∈ S := by
      intro i; exact hs i.castSucc
    have hym : ∀ i : Fin k, ys i.castSucc ⊆ ys i.succ := by
      intro i
      simpa only [ys, Fin.succ_castSucc] using hm i.castSucc
    have hprefix := ih ys hys hym
    have hedge := edge_card S lo hi hvalid
      (xs (Fin.last k).castSucc) (xs (Fin.last k).succ)
      (hs (Fin.last k).castSucc) (hm (Fin.last k))
    have hcard := Finset.card_le_card (hm (Fin.last k))
    rw [Fin.sum_univ_castSucc]
    have hlast : (Fin.last k).succ = Fin.last (k+1) := rfl
    change (∑ i : Fin k, drop lo hi (ys i.castSucc) (ys i.succ)) +
      drop lo hi (xs (Fin.last k).castSucc) (xs (Fin.last k).succ) ≤
      T * (xs (Fin.last (k+1))).card
    rw [← hlast]
    calc
      _ ≤ T * (xs (Fin.last k).castSucc).card +
          T * ((xs (Fin.last k).succ).card - (xs (Fin.last k).castSucc).card) :=
        Nat.add_le_add hprefix hedge
      _ = T * (xs (Fin.last k).succ).card := by
        rw [← mul_add]
        congr 1
        omega

lemma chain_le_Tn (hvalid : ∀ x ∈ S, ∀ j, lo x j ≤ hi x j ∧ hi x j ≤ T)
    (k : Nat) (xs : Fin (k+1) → X n) (hs : ∀ i, xs i ∈ S)
    (hm : ∀ i : Fin k, xs i.castSucc ⊆ xs i.succ) :
    (Finset.univ : Finset (Fin k)).sum
      (fun i => drop lo hi (xs i.castSucc) (xs i.succ)) ≤ T * n := by
  have hcard : (xs (Fin.last k)).card ≤ n := by
    simpa using (Finset.card_le_card (Finset.subset_univ (xs (Fin.last k))))
  exact (chain_card_bound S lo hi hvalid k xs hs hm).trans (Nat.mul_le_mul_left T hcard)

end Endpoint53156Card


namespace Endpoint53156Monotone

variable {n m : Nat}
abbrev X (n : Nat) := Finset (Fin n)
variable (S : Finset (X n)) (R : X n → Nat) (lo : X n → Fin m → Nat)

def rankEnd (x : X n) : Nat :=
  (S.filter (fun z => z ⊆ x)).sup R

def lowerEnd (x : X n) (j : Fin m) : Nat :=
  (S.filter (fun z => z ⊆ x)).sup (fun z => R z + lo z j)

lemma rankEnd_mono {x y : X n} (hxy : x ⊆ y) :
    rankEnd S R x ≤ rankEnd S R y := by
  unfold rankEnd
  apply Finset.sup_le
  intro z hz
  obtain ⟨hzS,hzx⟩ := Finset.mem_filter.mp hz
  exact Finset.le_sup (f := R) (Finset.mem_filter.mpr ⟨hzS,hzx.trans hxy⟩)

lemma lowerEnd_mono {x y : X n} (hxy : x ⊆ y) (j : Fin m) :
    lowerEnd S R lo x j ≤ lowerEnd S R lo y j := by
  unfold lowerEnd
  apply Finset.sup_le
  intro z hz
  obtain ⟨hzS,hzx⟩ := Finset.mem_filter.mp hz
  exact Finset.le_sup (f := fun z => R z + lo z j)
    (Finset.mem_filter.mpr ⟨hzS,hzx.trans hxy⟩)

end Endpoint53156Monotone

namespace DervishEnsemble53156
open PEqualNP PEqualNP.CircuitLowerBounds
open Endpoint53156Prefix Endpoint53156Residue DervishRepresentatives53156
open DervishCompileSlot53156
variable {n m T b : ℕ}
abbrev X (n : ℕ) := Finset (Fin n)
abbrev Tap (n m : ℕ) (C : Circuit) := Fin m → Fin (n+2+C.size)
def valid (n b : ℕ) (C : Circuit) : Prop := MetaComplexity.FanInTwo C ∧
  MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
  NotBracket.notCount C ≤ b

theorem build (S : Finset (X n)) (lo hi : X n → Fin m → ℕ)
    (R : X n → ℕ) (B : X n → Fin m → ℕ)
    (hRN : ∀ x ∈ S, R x ≤ T*n) (hRb : ∀ x ∈ S, R x ≤ T*(2^b-1))
    (hRm : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → R x ≤ R y)
    (hBm : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → ∀ j, B x j ≤ B y j)
    (hlo : ∀ x ∈ S, ∀ j, lo x j ≤ hi x j ∧ hi x j ≤ T)
    (he : ∀ x ∈ S, ∀ j, R x+lo x j ≤ B x j ∧ B x j ≤ R x+hi x j) :
    ∃ (cs : Fin T → Circuit) (a : ∀ t, Tap n m (cs t)),
      (∀ t, valid n b (cs t) ∧ (cs t).size ≤ 32*(n+1)*(m+1)*(S.card+1)) ∧
      (∀ x ∈ S, ∀ j, let cnt := (Finset.univ.filter (fun t =>
        ((cs t).wires (Dervish53156Donor.Wiring1270.input x)).getD (a t j).val false = true)).card
        lo x j ≤ cnt ∧ cnt ≤ hi x j) ∧
      ∃ K : Finset (Fin T), K.card ≤ 1+(m+1)*S.card ∧ ∀ t, ∃ r ∈ K,
        cs t = cs r ∧ ∀ j, (a t j).val = (a r j).val := by
  classical
  by_cases h0 : T = 0
  · subst T
    refine ⟨fun t => t.elim0, fun t => t.elim0, fun t => t.elim0, ?_,
      ∅, by simp, fun t => t.elim0⟩
    intro x hx j
    have h := hlo x hx j
    have hz (p : Fin 0 → Prop) [DecidablePred p] : (Finset.univ.filter p).card = 0 := by
      simp
    dsimp
    rw [hz]
    omega
  have hT := Nat.pos_of_ne_zero h0
  let L := min n (2^b-1)
  have hpow : L < 2^b := by
    have hp : 0 < (2 : ℕ)^b := pow_pos (by norm_num) _
    exact (min_le_right _ _).trans_lt (by omega)
  let rank (t : Fin T) (x : X n) := prefixCount T t (R x)
  let v (t : Fin T) (x : X n) (j : Fin m) := decide (rank t x < prefixCount T t (B x j))
  have hw (t : Fin T) := compile_slot S (rank t) (v t) L b (min_le_left _ _) hpow
    (fun x hx => le_min (prefixCount_le_cap _ _ _ hT (hRN x hx) t)
      (prefixCount_le_cap _ _ _ hT (hRb x hx) t))
    (fun x hx y hy hxy => prefixCount_mono T t (hRm x hx y hy hxy))
    (by
      intro x hx y hy hxy hxyR j hv
      exact decide_eq_true (high_mono_of_equal_prefixCount T t (hRm x hx y hy hxy)
        (hBm x hx y hy hxy j) hxyR (of_decide_eq_true hv)))
  choose cs a hc using hw
  let K := breaks T hT S R B
  let Same (r t : Fin T) : Prop := (∀ x ∈ S, rank r x = rank t x) ∧
    (∀ x ∈ S, ∀ j : Fin m, prefixCount T r (B x j) = prefixCount T t (B x j))
  have hex (t : Fin T) : ∃ r ∈ K, Same r t := shares_breaks T hT S R B t
  let rep (t : Fin T) : Fin T := if t ∈ K then t else Classical.choose (hex t)
  have hfix (t : Fin T) (ht : t ∈ K) : rep t = t := if_pos ht
  have hrep (t : Fin T) : rep t ∈ K ∧ Same (rep t) t := by
    by_cases h : t ∈ K
    · rw [hfix t h]
      exact ⟨h,fun _ _ => rfl,fun _ _ _ => rfl⟩
    · simpa only [rep,if_neg h] using Classical.choose_spec (hex t)
  let C (t : Fin T) := cs (rep t)
  let A (t : Fin T) : Tap n m (C t) := a (rep t)
  have hit (t : Fin T) (x : X n) (hx : x ∈ S) (j : Fin m) :
      ((C t).wires (Dervish53156Donor.Wiring1270.input x)).getD (A t j).val false = v t x j := by
    calc
      _ = v (rep t) x j := (hc (rep t)).2.2.2.2.2 x hx j
      _ = v t x j := by simp only [v,(hrep t).2.1 x hx,(hrep t).2.2 x hx j]
  refine ⟨C,A,?_,?_,K,?_,?_⟩
  · intro t
    have h := hc (rep t)
    exact ⟨⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩,h.2.2.2.2.1⟩
  · intro x hx j
    have h₁ := he x hx j
    have hr : R x ≤ B x j := (Nat.le_add_right _ _).trans h₁.1
    have hwid : B x j ≤ R x+T := h₁.2.trans (Nat.add_le_add_left (hlo x hx j).2 _)
    have heq : Finset.univ.filter (fun t =>
        ((C t).wires (Dervish53156Donor.Wiring1270.input x)).getD (A t j).val false = true) =
        slots T (R x) (B x j) hT := by
      ext t
      rw [Finset.mem_filter,hit t x hx j,slots_mem]
      simp only [Finset.mem_univ,true_and,v,rank,decide_eq_true_eq]
      exact prefixCount_high_iff T t _ _ hr
    dsimp
    rw [heq,slots_card _ _ _ _ hwid]
    omega
  · simpa using breaks_card T hT S R B
  · intro t
    have h := (hrep t).1
    have hh := (hfix (rep t) h).symm
    exact ⟨rep t,h,congrArg cs hh,fun j => congrArg (fun q => (a q j).val) hh⟩

end DervishEnsemble53156
open PEqualNP.CircuitLowerBounds
local instance : DecidableEq PEqualNP.CircuitLowerBounds.GateOp :=
  PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
namespace Lower53156
namespace AltChain1196

def below (x y : List Bool) : Prop := ∀ i, x.getD i false ≤ y.getD i false

private theorem below_append (a b : List Bool) (u v : Bool)
    (h : below a b) (hu : u ≤ v) (hl : a.length = b.length) :
    below (a ++ [u]) (b ++ [v]) := by
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi)]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_lt hi),
        List.getD_append_right _ _ _ _ (by omega : b.length ≤ i)]
    by_cases hiz : i - a.length = 0
    · have hbz : i - b.length = 0 := by omega
      simp only [hiz, hbz]
      exact hu
    · have hg : 1 ≤ i - a.length := by omega
      have hg2 : 1 ≤ i - b.length := by omega
      rw [List.getD_eq_default _ _ hg, List.getD_eq_default _ _ hg2]
private theorem all_mono (a b : List Bool) (h : below a b) (is : List ℕ) :
    (is.map fun i => a.getD i false).all id ≤
    (is.map fun i => b.getD i false).all id := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.all_cons, id_eq]
    have hi := h i
    cases ha : a.getD i false <;> cases hb : b.getD i false
    · simp
    · simp
    · have hcontra : False := (by decide : ¬ (true : Bool) ≤ false) (by simpa only [ha, hb] using hi)
      exact hcontra.elim
    · simpa [ha, hb] using ih

private theorem any_mono (a b : List Bool) (h : below a b) (is : List ℕ) :
    (is.map fun i => a.getD i false).any id ≤
    (is.map fun i => b.getD i false).any id := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    have hi := h i
    cases ha : a.getD i false <;> cases hb : b.getD i false
    · simpa [ha, hb] using ih
    · simp
    · have hcontra : False := (by decide : ¬ (true : Bool) ≤ false) (by simpa only [ha, hb] using hi)
      exact hcontra.elim
    · simpa [ha, hb] using ih

private theorem gate_mono (a b : List Bool) (h : below a b) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hn : g.op = GateOp.not →
      g.op.eval (g.inputs.map fun i => a.getD i false) =
      g.op.eval (g.inputs.map fun i => b.getD i false)) :
    g.op.eval (g.inputs.map fun i => a.getD i false) ≤
    g.op.eval (g.inputs.map fun i => b.getD i false) := by
  rcases hop with ha | ho | hnop
  · simpa [ha, GateOp.eval] using all_mono a b h g.inputs
  · simpa [ho, GateOp.eval] using any_mono a b h g.inputs
  · exact le_of_eq (hn hnop)

private def physicalNot (C : Circuit) := {j : Fin C.size // (C.gates[j.val]).op = GateOp.not}

private noncomputable instance (C : Circuit) : Fintype (physicalNot C) := by
  classical
  unfold physicalNot
  infer_instance

private theorem physical_not_count (C : Circuit) :
    Fintype.card (physicalNot C) = PEqualNP.NotBracket.notCount C := by
  classical
  simp only [physicalNot, Fintype.card_subtype, PEqualNP.NotBracket.notCount]
  change (Finset.univ.filter (fun j : Fin C.gates.length => C.gates[j.val].op = GateOp.not)).card =
    (C.gates.filter fun g => decide (g.op = GateOp.not)).length
  rw [← List.countP_eq_length_filter]
  conv_rhs => rw [← List.ofFn_get C.gates]
  rw [List.countP_ofFn]
  simp

def value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def step (w : List Bool) (g : Gate) := w ++ [value g w]
def resultFrom (gs : List Gate) (w : List Bool) := gs.foldl step w

def signatureFrom : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w =>
      (if g.op = GateOp.not then [value g w] else []) ++ signatureFrom gs (step w g)

private theorem signatureFrom_length (gs : List Gate) (w : List Bool) :
    (signatureFrom gs w).length =
      (gs.filter fun g => decide (g.op = GateOp.not)).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : g.op = GateOp.not <;> simp [signatureFrom, ih, h]

private theorem resultFrom_length (gs : List Gate) (w : List Bool) :
    (resultFrom gs w).length = w.length + gs.length := by
  simp only [resultFrom]
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

private theorem not_between (a b c : List Bool) (hab : below a b) (hbc : below b c)
    (is : List ℕ)
    (hac : GateOp.not.eval (is.map fun i => a.getD i false) =
      GateOp.not.eval (is.map fun i => c.getD i false)) :
    GateOp.not.eval (is.map fun i => a.getD i false) =
      GateOp.not.eval (is.map fun i => b.getD i false) ∧
    GateOp.not.eval (is.map fun i => b.getD i false) =
      GateOp.not.eval (is.map fun i => c.getD i false) := by
  cases is with
  | nil => simp [GateOp.eval]
  | cons i is =>
    have hi := hab i
    have hi' := hbc i
    simp only [List.map_cons, GateOp.eval, List.headD_cons] at hac ⊢
    cases ha : a.getD i false <;> cases hb : b.getD i false <;>
      cases hc : c.getD i false <;> simp_all
    all_goals exact False.elim ((by decide : ¬ (true : Bool) ≤ false) (by assumption))

private theorem signature_convex (gs : List Gate) (a b c : List Bool)
    (hab : below a b) (hbc : below b c)
    (hablen : a.length = b.length) (hbclen : b.length = c.length)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hends : signatureFrom gs a = signatureFrom gs c) :
    signatureFrom gs a = signatureFrom gs b ∧
    below (resultFrom gs a) (resultFrom gs b) ∧
    below (resultFrom gs b) (resultFrom gs c) := by
  induction gs generalizing a b c with
  | nil => exact ⟨rfl, hab, hbc⟩
  | cons g gs ih =>
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
      hops g (by simp)
    have htOps : ∀ q ∈ gs, q.op = GateOp.and ∨ q.op = GateOp.or ∨ q.op = GateOp.not := by
      intro q hq
      exact hops q (by simp [hq])
    by_cases hn : g.op = GateOp.not
    · have hv : value g a = value g c := by
        have h := hends
        simp only [signatureFrom, if_pos hn, List.singleton_append, List.cons.injEq] at h
        exact h.1
      have htail : signatureFrom gs (step a g) = signatureFrom gs (step c g) := by
        have h := hends
        simp only [signatureFrom, if_pos hn, List.singleton_append, List.cons.injEq] at h
        exact h.2
      have hvals : value g a = value g b ∧ value g b = value g c := by
        simpa only [value, hn] using
          (not_between a b c hab hbc g.inputs (by simpa only [value, hn] using hv))
      have hab' : below (step a g) (step b g) :=
        below_append a b (value g a) (value g b) hab hvals.1.le hablen
      have hbc' : below (step b g) (step c g) :=
        below_append b c (value g b) (value g c) hbc hvals.2.le hbclen
      have hres := ih (step a g) (step b g) (step c g) hab' hbc'
        (by simp [step, hablen]) (by simp [step, hbclen]) htOps htail
      refine ⟨?_, hres.2.1, hres.2.2⟩
      simp [signatureFrom, hn, hvals.1, hres.1]
    · have htail : signatureFrom gs (step a g) = signatureFrom gs (step c g) := by
        simpa only [signatureFrom, if_neg hn, List.nil_append] using hends
      have hab' : below (step a g) (step b g) :=
        below_append a b (value g a) (value g b) hab
          (gate_mono a b hab g hop (by intro h; exact (hn h).elim)) hablen
      have hbc' : below (step b g) (step c g) :=
        below_append b c (value g b) (value g c) hbc
          (gate_mono b c hbc g hop (by intro h; exact (hn h).elim)) hbclen
      have hres := ih (step a g) (step b g) (step c g) hab' hbc'
        (by simp [step, hablen]) (by simp [step, hbclen]) htOps htail
      refine ⟨?_, hres.2.1, hres.2.2⟩
      simpa [signatureFrom, hn] using hres.1

def circuitSignature (C : Circuit) (x : List Bool) :
    Fin (PEqualNP.NotBracket.notCount C) → Bool :=
  fun j => (signatureFrom C.gates x).getD j.val false

private theorem sig_injective (C : Circuit) (x y : List Bool)
    (h : circuitSignature C x = circuitSignature C y) :
    signatureFrom C.gates x = signatureFrom C.gates y := by
  have hlen (w : List Bool) :
      (signatureFrom C.gates w).length = PEqualNP.NotBracket.notCount C := by
    exact signatureFrom_length C.gates w
  apply List.ext_getElem
  · exact (hlen x).trans (hlen y).symm
  · intro i hix hiy
    let j : Fin (PEqualNP.NotBracket.notCount C) := ⟨i, by simpa only [hlen] using hix⟩
    have hj := congrFun h j
    change (signatureFrom C.gates x).getD i false =
      (signatureFrom C.gates y).getD i false at hj
    rwa [List.getD_eq_getElem _ _ hix, List.getD_eq_getElem _ _ hiy] at hj

theorem circuit_signature_convex (C : Circuit) (a b c : List Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hab : below a b) (hbc : below b c)
    (hlenAB : a.length = b.length) (hlenBC : b.length = c.length)
    (heq : circuitSignature C a = circuitSignature C c) :
    circuitSignature C a = circuitSignature C b ∧
      below (C.wires a) (C.wires b) ∧ below (C.wires b) (C.wires c) := by
  have hops : ∀ g ∈ C.gates,
      g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    have h := (hfan g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have h := signature_convex C.gates a b c hab hbc hlenAB hlenBC hops
    (sig_injective C a c heq)
  refine ⟨?_, ?_, ?_⟩
  · funext j
    exact congrArg (fun w : List Bool => w.getD j.val false) h.1
  · exact h.2.1
  · exact h.2.2

theorem signature_bound (k r : ℕ) (σ : Fin (k+1) → Fin r → Bool)
    (hconvex : ∀ a b c : Fin (k+1), a ≤ b → b ≤ c → σ a = σ c → σ a = σ b)
    (hfall : ∀ i : Fin k, σ (Fin.castSucc i) ≠ σ (Fin.succ i)) : k < 2^r := by
  have hinj : Function.Injective σ := by
    intro a c heq
    rcases le_total a c with hac | hca
    · by_contra hne
      have hlt : a.val < c.val := Nat.lt_of_le_of_ne hac (by
        intro h; exact hne (Fin.ext h))
      have hsmall : a.val < k := by omega
      let i : Fin k := ⟨a.val, hsmall⟩
      have hboundary := hfall i
      have hstep := hconvex a (Fin.succ i) c (by change a.val ≤ i.val + 1; dsimp [i]; omega) (by change i.val + 1 ≤ c.val; dsimp [i]; omega) heq
      have ha : Fin.castSucc i = a := by ext; rfl
      exact hboundary (by simpa [ha] using hstep)
    · by_contra hne
      have hlt : c.val < a.val := Nat.lt_of_le_of_ne hca (by
        intro h; exact hne (Fin.ext h.symm))
      have hsmall : c.val < k := by omega
      let i : Fin k := ⟨c.val, hsmall⟩
      have hboundary := hfall i
      have hstep := hconvex c (Fin.succ i) a (by change c.val ≤ i.val + 1; dsimp [i]; omega) (by change i.val + 1 ≤ a.val; dsimp [i]; omega) heq.symm
      have hc : Fin.castSucc i = c := by ext; rfl
      exact hboundary (by simpa [hc] using hstep)
  have hcard : Fintype.card (Fin (k+1)) ≤ Fintype.card (Fin r → Bool) :=
    Fintype.card_le_of_injective σ hinj
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool] at hcard
  omega
theorem odd_fall_bound (k r : ℕ) (σ : Fin (2*k+1) → Fin r → Bool)
    (hconvex : ∀ a b c : Fin (2*k+1), a ≤ b → b ≤ c → σ a = σ c → σ a = σ b)
    (hfall : ∀ i : Fin k,
      σ ⟨2*i.val+1, by omega⟩ ≠ σ ⟨2*i.val+2, by omega⟩) : k < 2^r := by
  let τ : Fin (k+1) → Fin r → Bool := fun i => σ ⟨2*i.val, by omega⟩
  apply signature_bound k r τ
  · intro a b c hab hbc heq
    exact hconvex ⟨2*a.val, by omega⟩ ⟨2*b.val, by omega⟩
      ⟨2*c.val, by omega⟩ (by change 2*a.val ≤ 2*b.val; omega)
      (by change 2*b.val ≤ 2*c.val; omega) heq
  · intro i heq
    have hbase := hfall i
    have hend : σ ⟨2*i.val, by omega⟩ = σ ⟨2*i.val+2, by omega⟩ := by
      simpa [τ, Fin.succ, Fin.castSucc, mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using heq
    have hfirst : σ ⟨2*i.val, by omega⟩ = σ ⟨2*i.val+1, by omega⟩ :=
      hconvex ⟨2*i.val, by omega⟩ ⟨2*i.val+1, by omega⟩
        ⟨2*i.val+2, by omega⟩
        (by change 2*i.val ≤ 2*i.val+1; omega)
        (by change 2*i.val+1 ≤ 2*i.val+2; omega) hend
    exact hbase (hfirst.symm.trans hend)


theorem circuit_multioutput_markov (k n : Nat) (C : Circuit)
    (x : Fin (2*k+1) → List Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hlen : ∀ t, (x t).length = n)
    (hmono : ∀ a b, a ≤ b → below (x a) (x b))
    (hfall : ∀ i : Fin k, ∃ w : ℕ,
      (C.wires (x ⟨2*i.val+1, by omega⟩)).getD w false = true ∧
      (C.wires (x ⟨2*i.val+2, by omega⟩)).getD w false = false) :
    k < 2 ^ PEqualNP.NotBracket.notCount C := by
  apply odd_fall_bound k (PEqualNP.NotBracket.notCount C)
    (fun t => circuitSignature C (x t))
  · intro a b c hab hbc heq
    exact (circuit_signature_convex C (x a) (x b) (x c) hfan
      (hmono a b hab) (hmono b c hbc)
      (by rw [hlen a, hlen b]) (by rw [hlen b, hlen c]) heq).1
  · intro i heq
    rcases hfall i with ⟨w, hw1, hw0⟩
    let a : Fin (2*k+1) := ⟨2*i.val+1, by omega⟩
    let b : Fin (2*k+1) := ⟨2*i.val+2, by omega⟩
    have hab : a ≤ b := by change 2*i.val+1 ≤ 2*i.val+2; omega
    have hbelow := (circuit_signature_convex C (x a) (x b) (x b) hfan
      (hmono a b hab) (by intro j; exact le_refl _)
      (by rw [hlen a, hlen b]) rfl heq).2.1
    have hf := hbelow w
    rw [show x a = x ⟨2*i.val+1, by omega⟩ from rfl,
      show x b = x ⟨2*i.val+2, by omega⟩ from rfl, hw1, hw0] at hf
    exact (by decide : ¬ (true : Bool) ≤ false) hf

end AltChain1196

open PEqualNP.CircuitLowerBounds
open Lower53156.AltChain1196

namespace Lower53156

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

private theorem fall_bound {k : Nat} (C : Circuit) (x : Fin (k+1) → List Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hlen : ∀ i j, (x i).length = (x j).length)
    (hmono : ∀ i j, i ≤ j → below (x i) (x j)) :
    ((Finset.univ : Finset (Fin k)).filter (fun i : Fin k => ∃ w : Nat,
      (C.wires (x i.castSucc)).getD w false = true ∧
      (C.wires (x i.succ)).getD w false = false)).card <
      2 ^ PEqualNP.NotBracket.notCount C := by
  classical
  let E : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => ∃ w : Nat,
      (C.wires (x i.castSucc)).getD w false = true ∧
      (C.wires (x i.succ)).getD w false = false)
  let σ : Fin (k+1) → (Fin (PEqualNP.NotBracket.notCount C) → Bool) :=
    fun i => circuitSignature C (x i)
  have hsep : ∀ i : Fin k, i ∈ E → ∀ j : Fin (k+1), i.val < j.val →
      σ i.castSucc ≠ σ j := by
    intro i hi j hij heq
    obtain ⟨w, hw1, hw0⟩ := (Finset.mem_filter.mp hi).2
    have hij' : i.succ ≤ j := by exact hij
    have hc := circuit_signature_convex C (x i.castSucc) (x i.succ) (x j)
      hfan (hmono _ _ (Fin.castSucc_le_succ i)) (hmono _ _ hij')
      (hlen _ _) (hlen _ _) heq
    have hn := hc.2.1 w
    rw [hw1, hw0] at hn
    exact (by decide : ¬ (true : Bool) ≤ false) hn
  have hinj : Set.InjOn (fun i : Fin k => σ i.castSucc) E := by
    intro i hi j hj heq
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · exact False.elim ((hsep i hi j.castSucc hij) heq)
    · exact Fin.ext hij
    · exact False.elim ((hsep j hj i.castSucc hij) heq.symm)
  have hsub : E.image (fun i => σ i.castSucc) ⊆
      Finset.univ.erase (σ (Fin.last k)) := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_erase.mpr ⟨hsep i hi (Fin.last k) i.isLt, Finset.mem_univ _⟩
  have hc : E.card ≤ (Finset.univ.erase (σ (Fin.last k)) :
      Finset (Fin (PEqualNP.NotBracket.notCount C) → Bool)).card := by
    calc
      E.card = (E.image (fun i => σ i.castSucc)).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hcard : (Finset.univ : Finset (Fin (PEqualNP.NotBracket.notCount C) → Bool)).card =
      2 ^ PEqualNP.NotBracket.notCount C := by simp
  have hh := Finset.card_erase_of_mem (Finset.mem_univ (σ (Fin.last k)))
  rw [hcard] at hh
  change E.card < 2 ^ PEqualNP.NotBracket.notCount C
  have hpositive : 0 < 2 ^ PEqualNP.NotBracket.notCount C := pow_pos (by norm_num) _
  omega


private def input {n : Nat} (s : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ s)) ++ [false,true]

private theorem input_length {n : Nat} (s : Finset (Fin n)) :
    (input s).length = n+2 := by simp [input]

private theorem input_below {n : Nat} {s t : Finset (Fin n)} (hst : s ⊆ t) :
    below (input s) (input t) := by
  intro i
  by_cases hi : i < n
  · have h : i < (List.ofFn (fun u : Fin n => decide (u ∈ s))).length := by simpa using hi
    have h' : i < (List.ofFn (fun u : Fin n => decide (u ∈ t))).length := by simpa using hi
    rw [input, input, List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h']
    rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h']
    simp only [List.getElem_ofFn]
    by_cases hs : ⟨i,hi⟩ ∈ s
    · simp [hs, hst hs]
    · simp [hs]
  · rw [input, input, List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simpa only [List.length_ofFn] using (le_refl ([false,true].getD (i-n) false))

private theorem chain_mono {n k : Nat} (x : Fin (k+1) → Finset (Fin n))
    (h : ∀ i : Fin k, x i.castSucc ⊆ x i.succ) :
    ∀ i j : Fin (k+1), i ≤ j → x i ⊆ x j := by
  have step : ∀ d : Nat, ∀ i j : Fin (k+1), j.val = i.val+d → x i ⊆ x j := by
    intro d
    induction d with
    | zero =>
      intro i j hj
      have heq : i = j := Fin.ext (by omega)
      rw [heq]
    | succ d ih =>
      intro i j hj
      have hpred : j.val-1 < k := by omega
      let p : Fin k := ⟨j.val-1, hpred⟩
      have hpj : p.succ = j := Fin.ext (by dsimp [p]; omega)
      have hip : p.castSucc.val = i.val+d := by dsimp [p]; omega
      exact (ih i p.castSucc hip).trans (by simpa only [hpj] using h p)
  intro i j hij
  exact step (j.val-i.val) i j (by omega)

private theorem count_edge_bound {T m : Nat} (u v : Fin T → Fin m → Bool)
    (lo hi : Fin m → Nat)
    (hfit : ∀ j, lo j ≤ (Finset.univ.filter (fun t => u t j = true)).card ∧
      (Finset.univ.filter (fun t => v t j = true)).card ≤ hi j) :
    (Finset.univ : Finset (Fin m)).sup (fun j => lo j - hi j) ≤
      ((Finset.univ : Finset (Fin T)).filter (fun t => ∃ j, u t j = true ∧ v t j = false)).card := by
  classical
  apply Finset.sup_le
  intro j _
  let A : Finset (Fin T) := Finset.univ.filter (fun t => u t j = true)
  let B : Finset (Fin T) := Finset.univ.filter (fun t => v t j = true)
  let F : Finset (Fin T) := Finset.univ.filter (fun t => ∃ j, u t j = true ∧ v t j = false)
  have hsub : A ⊆ B ∪ F := by
    intro t ht
    by_cases hv : v t j = true
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
    · have hfalse : v t j = false := Bool.eq_false_iff.mpr hv
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨j, (Finset.mem_filter.mp ht).2, hfalse⟩⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le B F)
  have hh := hfit j
  change lo j ≤ A.card ∧ B.card ≤ hi j at hh
  change lo j - hi j ≤ F.card
  omega

private theorem count_chain_bound {T m k b : Nat}
    (u : Fin T → Fin m → Fin (k+1) → Bool)
    (lo hi : Fin (k+1) → Fin m → Nat)
    (hfit : ∀ i j, lo i j ≤ ((Finset.univ : Finset (Fin T)).filter
      (fun t => u t j i = true)).card ∧
      ((Finset.univ : Finset (Fin T)).filter (fun t => u t j i = true)).card ≤ hi i j)
    (hfall : ∀ t, ((Finset.univ : Finset (Fin k)).filter (fun i =>
      ∃ j, u t j i.castSucc = true ∧ u t j i.succ = false)).card < 2^b) :
    (Finset.univ : Finset (Fin k)).sum (fun i =>
      (Finset.univ : Finset (Fin m)).sup (fun j => lo i.castSucc j - hi i.succ j)) ≤
      T*(2^b-1) := by
  classical
  have hedge (i : Fin k) :
      (Finset.univ : Finset (Fin m)).sup (fun j => lo i.castSucc j - hi i.succ j) ≤
      ((Finset.univ : Finset (Fin T)).filter (fun t =>
        ∃ j, u t j i.castSucc = true ∧ u t j i.succ = false)).card := by
    exact count_edge_bound (fun t j => u t j i.castSucc)
      (fun t j => u t j i.succ) (lo i.castSucc) (hi i.succ)
      (fun j => ⟨(hfit i.castSucc j).1, (hfit i.succ j).2⟩)
  have hcomm :
      (Finset.univ : Finset (Fin k)).sum (fun i =>
        ((Finset.univ : Finset (Fin T)).filter (fun t =>
          ∃ j, u t j i.castSucc = true ∧ u t j i.succ = false)).card) =
      (Finset.univ : Finset (Fin T)).sum (fun t =>
        ((Finset.univ : Finset (Fin k)).filter (fun i =>
          ∃ j, u t j i.castSucc = true ∧ u t j i.succ = false)).card) := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  calc
    _ ≤ (Finset.univ : Finset (Fin k)).sum (fun i =>
        ((Finset.univ : Finset (Fin T)).filter (fun t =>
          ∃ j, u t j i.castSucc = true ∧ u t j i.succ = false)).card) :=
      Finset.sum_le_sum (fun i _ => hedge i)
    _ = (Finset.univ : Finset (Fin T)).sum (fun t =>
        ((Finset.univ : Finset (Fin k)).filter (fun i =>
          ∃ j, u t j i.castSucc = true ∧ u t j i.succ = false)).card) := hcomm
    _ ≤ (Finset.univ : Finset (Fin T)).sum (fun _ => 2^b-1) := by
      apply Finset.sum_le_sum
      intro t _
      have hp : 0 < 2^b := pow_pos (by norm_num) _
      have ht := hfall t
      omega
    _ = T*(2^b-1) := by simp

private theorem necessary_chain {n m T b k : Nat}
    (cs : Fin T → Circuit)
    (a : ∀ t, Fin m → Fin (n+2+(cs t).size))
    (lo hi : Finset (Fin n) → Fin m → Nat)
    (x : Fin (k+1) → Finset (Fin n))
    (hmono : ∀ i : Fin k, x i.castSucc ⊆ x i.succ)
    (hfan : ∀ t, PEqualNP.MetaComplexity.FanInTwo (cs t))
    (hbudget : ∀ t, PEqualNP.NotBracket.notCount (cs t) ≤ b)
    (hfit : ∀ i j, lo (x i) j ≤ ((Finset.univ : Finset (Fin T)).filter
      (fun t => ((cs t).wires (input (x i))).getD (a t j).val false = true)).card ∧
      ((Finset.univ : Finset (Fin T)).filter
      (fun t => ((cs t).wires (input (x i))).getD (a t j).val false = true)).card ≤ hi (x i) j) :
    (Finset.univ : Finset (Fin k)).sum (fun i =>
      (Finset.univ : Finset (Fin m)).sup (fun j => lo (x i.castSucc) j - hi (x i.succ) j)) ≤
      T*(2^b-1) := by
  classical
  let u : Fin T → Fin m → Fin (k+1) → Bool := fun t j i =>
    ((cs t).wires (input (x i))).getD (a t j).val false
  have hglobal := chain_mono x hmono
  have hper (t : Fin T) :
      ((Finset.univ : Finset (Fin k)).filter (fun i =>
        ∃ j, u t j i.castSucc = true ∧ u t j i.succ = false)).card < 2^b := by
    have hsub :
        ((Finset.univ : Finset (Fin k)).filter (fun i =>
          ∃ j, u t j i.castSucc = true ∧ u t j i.succ = false)) ⊆
        ((Finset.univ : Finset (Fin k)).filter (fun i => ∃ w : Nat,
          ((cs t).wires (input (x i.castSucc))).getD w false = true ∧
          ((cs t).wires (input (x i.succ))).getD w false = false)) := by
      intro i hi
      obtain ⟨j, hj1, hj0⟩ := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨(a t j).val, hj1, hj0⟩⟩
    have hc := Finset.card_le_card hsub
    have hm := fall_bound (cs t) (fun i => input (x i)) (hfan t)
      (fun i j => by rw [input_length, input_length])
      (fun i j hij => input_below (hglobal i j hij))
    have hb : 2 ^ PEqualNP.NotBracket.notCount (cs t) ≤ 2^b := by
      exact Nat.pow_le_pow_right (by omega : 0 < 2) (hbudget t)
    exact lt_of_le_of_lt hc (lt_of_lt_of_le hm hb)
  exact count_chain_bound u (fun i j => lo (x i) j) (fun i j => hi (x i) j)
    (fun i j => hfit i j) hper
end

theorem necessary_exact : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m T b : Nat) (S : Finset (Finset (Fin n))) (lo hi : Finset (Fin n) → Fin m → Nat),
  let X := Finset (Fin n)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let taps := fun (C : Circ) => Fin m → Fin (n+2+C.size)
  let input := fun (x : X) => List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
  let val := fun (C : Circ) (a : taps C) (x : X) (j : Fin m) =>
    (C.wires (input x)).getD (a j).val false
  let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b
  let drop := fun (x y : X) => (Finset.univ : Finset (Fin m)).sup (fun j => lo x j - hi y j)
  let chains := ∀ (k : Nat) (x : Fin (k+1) → X), (∀ i, x i ∈ S) →
    (∀ i : Fin k, x i.castSucc ⊆ x i.succ) →
    (Finset.univ : Finset (Fin k)).sum (fun i => drop (x i.castSucc) (x i.succ)) ≤ T*(2^b-1)
  let fits := fun (cs : Fin T → Circ) (a : ∀ t, taps (cs t)) =>
    ∀ x ∈ S, ∀ j : Fin m, let count := ((Finset.univ : Finset (Fin T)).filter
      (fun t => val (cs t) (a t) x j = true)).card
    lo x j ≤ count ∧ count ≤ hi x j
  (∀ x ∈ S, ∀ j, lo x j ≤ hi x j ∧ hi x j ≤ T) →
  (∃ (cs : Fin T → Circ) (a : ∀ t, taps (cs t)), (∀ t, valid (cs t)) ∧ fits cs a) → chains) := by
  classical
  intro n m T b S lo hi
  dsimp
  intro _
  rintro ⟨cs, a, hvalid, hfits⟩
  intro k x hxS hxmono
  apply necessary_chain cs a lo hi x hxmono
    (fun t => (hvalid t).1) (fun t => (hvalid t).2.2.2)
  intro i j
  have hin : input (x i) =
      List.ofFn (fun z : Fin n => @decide (z ∈ x i) (Classical.propDecidable _)) ++ [false,true] := by
    unfold input
    have hfun : (fun z : Fin n => decide (z ∈ x i)) =
        (fun z : Fin n => @decide (z ∈ x i) (Classical.propDecidable _)) := by
      funext z
      by_cases hz : z ∈ x i <;> simp [hz]
    exact congrArg (fun f : Fin n → Bool => List.ofFn f ++ [false,true]) hfun
  constructor
  · convert (hfits (x i) (hxS i) j).1 using 2
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hin]
  · convert (hfits (x i) (hxS i) j).2 using 2
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hin]

end Lower53156

end Lower53156

end PEqualNP.Outside.L_meta_53156_aux

open PEqualNP.Outside.L_meta_53156_aux in
theorem PEqualNP.Outside.L_meta_53156 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m T b : Nat) (S : Finset (Finset (Fin n))) (lo hi : Finset (Fin n) → Fin m → Nat),
  let X := Finset (Fin n)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let taps := fun (C : Circ) => Fin m → Fin (n+2+C.size)
  let input := fun (x : X) => List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
  let val := fun (C : Circ) (a : taps C) (x : X) (j : Fin m) =>
    (C.wires (input x)).getD (a j).val false
  let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b
  let drop := fun (x y : X) => (Finset.univ : Finset (Fin m)).sup (fun j => lo x j - hi y j)
  let chains := ∀ (k : Nat) (x : Fin (k+1) → X), (∀ i, x i ∈ S) →
    (∀ i : Fin k, x i.castSucc ⊆ x i.succ) →
    (Finset.univ : Finset (Fin k)).sum (fun i => drop (x i.castSucc) (x i.succ)) ≤ T*(2^b-1)
  let fits := fun (cs : Fin T → Circ) (a : ∀ t, taps (cs t)) =>
    ∀ x ∈ S, ∀ j : Fin m, let count := ((Finset.univ : Finset (Fin T)).filter
      (fun t => val (cs t) (a t) x j = true)).card
    lo x j ≤ count ∧ count ≤ hi x j
  (∀ x ∈ S, ∀ j, lo x j ≤ hi x j ∧ hi x j ≤ T) →
  ((∃ (cs : Fin T → Circ) (a : ∀ t, taps (cs t)), (∀ t, valid (cs t)) ∧ fits cs a) ↔ chains) ∧
  (chains → ∃ (cs : Fin T → Circ) (a : ∀ t, taps (cs t)),
    (∀ t, valid (cs t) ∧ (cs t).size ≤ 32*(n+1)*(m+1)*(S.card+1)) ∧ fits cs a ∧
    ∃ reps : Finset (Fin T), reps.card ≤ 1+(m+1)*S.card ∧ ∀ t, ∃ r ∈ reps,
      cs t = cs r ∧ ∀ j : Fin m, (a t j).val = (a r j).val)) := by
  classical
  intro n m T b S lo hi
  dsimp
  intro hvalid
  have upper (hchain : ∀ (k : Nat) (xs : Fin (k+1) → Finset (Fin n)),
      (∀ i, xs i ∈ S) → (∀ i : Fin k, xs i.castSucc ⊆ xs i.succ) →
      (Finset.univ : Finset (Fin k)).sum
        (fun i => Endpoint53156.drop lo hi (xs i.castSucc) (xs i.succ)) ≤ T*(2^b-1)) := by
    let R := Endpoint53156.rank S lo hi
    let B := Endpoint53156.lowerEnd S lo R
    have hRn (x : Finset (Fin n)) (hx : x ∈ S) : R x ≤ T*n := by
      obtain ⟨k,xs,hs,hm,_,hv⟩ := Endpoint53156.rank_path S lo hi hchain x hx
      change _ = R x at hv
      rw [← hv]
      exact Endpoint53156Card.chain_le_Tn S lo hi hvalid k xs hs hm
    have hRb (x : Finset (Fin n)) (hx : x ∈ S) : R x ≤ T*(2^b-1) :=
      Endpoint53156.rank_le_of_chains S lo hi hchain x hx
    have hRm (x : Finset (Fin n)) (hx : x ∈ S) (y : Finset (Fin n)) (hy : y ∈ S)
        (hxy : x ⊆ y) : R x ≤ R y := by
      have hh := Endpoint53156.rank_step S lo hi hchain x hx y hy hxy
      exact (Nat.le_add_right _ _).trans hh
    have hBm (x : Finset (Fin n)) (_hx : x ∈ S) (y : Finset (Fin n)) (_hy : y ∈ S)
        (hxy : x ⊆ y) (j : Fin m) : B x j ≤ B y j :=
      Endpoint53156Monotone.lowerEnd_mono S R lo hxy j
    have he (x : Finset (Fin n)) (hx : x ∈ S) (j : Fin m) :
        R x+lo x j ≤ B x j ∧ B x j ≤ R x+hi x j :=
      ⟨(Endpoint53156.sample_endpoint S lo hi hchain hvalid x hx j).1,
        (Endpoint53156.sample_endpoint S lo hi hchain hvalid x hx j).2.1⟩
    exact DervishEnsemble53156.build S lo hi R B (b:=b) hRn hRb hRm hBm hvalid he
  have hin (x : Finset (Fin n)) : Dervish53156Donor.Wiring1270.input x =
      List.ofFn (fun z : Fin n => @decide (z ∈ x) (Classical.propDecidable _)) ++ [false,true] := by
    unfold Dervish53156Donor.Wiring1270.input
    have hfun : (fun z : Fin n => decide (z ∈ x)) =
        (fun z : Fin n => @decide (z ∈ x) (Classical.propDecidable _)) := by
      funext z
      by_cases hz : z ∈ x <;> simp [hz]
    exact congrArg (fun f : Fin n → Bool => List.ofFn f ++ [false,true]) hfun
  constructor
  · constructor
    · exact Lower53156.Lower53156.necessary_exact n m T b S lo hi hvalid
    · intro hc
      obtain ⟨cs,a,hv,hf,r,hr,hs⟩ := upper hc
      refine ⟨cs,a,fun t => (hv t).1,?_⟩
      intro x hx j
      constructor
      · convert (hf x hx j).1 using 2
        ext t
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        rw [hin]
      · convert (hf x hx j).2 using 2
        ext t
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        rw [hin]
  · intro hc
    obtain ⟨cs,a,hv,hf,r,hr,hs⟩ := upper hc
    refine ⟨cs,a,hv,?_,r,hr,hs⟩
    intro x hx j
    constructor
    · convert (hf x hx j).1 using 2
      ext t
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rw [hin]
    · convert (hf x hx j).2 using 2
      ext t
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rw [hin]


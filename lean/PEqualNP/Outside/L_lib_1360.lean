import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1360

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
    (v : Finset (Fin n) → Fin m → Bool) (L b : ℕ) (hPow : L < 2^b)
    (hBound : ∀ y ∈ S, h y ≤ L)
    (hh : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x ≤ h y)
    (hv : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x = h y → ∀ j, v x j = true → v y j = true) :
    ∃ (C : Circuit) (tap : Fin m → Fin (n+2+C.size)),
      MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ NotBracket.notCount C ≤ b ∧
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
  have hNots : e.nots ≤ b := by omega
  choose addr hadd using V₅
  let C : Circuit := ⟨e.gates,0⟩
  let tap : Fin m → Fin (n+2+C.size) := fun j =>
    ⟨addr j, by
      have h := (hadd j).1
      simpa only [C,Circuit.size,Build.size,Build.cost] using h⟩
  refine ⟨C,tap,e.fan,e.back,by simp [C],hNots,?_⟩
  intro x hx j
  exact ((hadd j).2 x).trans (report_exact S h v hh hv x hx j)

end DervishCompileSlot53156
end PEqualNP.Outside.L_lib_1360

namespace PEqualNP.Outside.L_lib_1360.Mark

open PEqualNP.CircuitLowerBounds

section CircuitDSL

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepW x

lemma W_eq_wires (gs : List Gate) (out : ℕ) (x : List Bool) :
    (⟨gs, out⟩ : Circuit).wires x = W gs x := rfl

lemma W_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = stepW (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_length (gs : List Gate) (x : List Bool) :
    (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_append_singleton]
    simp [stepW, ih]
    omega

lemma W_getD_lt (gs : List Gate) (g : Gate) (x : List Bool) (k : ℕ)
    (hk : k < (W gs x).length) :
    (W (gs ++ [g]) x).getD k false = (W gs x).getD k false := by
  rw [W_append_singleton, stepW]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma W_getD_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (W (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (W gs x).getD i false) := by
  rw [W_append_singleton, stepW]
  have hlen := W_length gs x
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [hlen]

lemma W_getD_of_le (gs : List Gate) (x : List Bool) (k : ℕ)
    (hk : x.length + gs.length ≤ k) :
    (W gs x).getD k false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [W_length]; omega)]
  rfl

lemma W_extend (as bs : List Gate) (x : List Bool) (k : ℕ)
    (hk : k < x.length + as.length) :
    (W (as ++ bs) x).getD k false = (W as x).getD k false := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs g ih =>
    rw [← List.append_assoc, W_getD_lt _ _ _ _ (by rw [W_length]; simp; omega), ih]

def OKg (g : Gate) (b : ℕ) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
  g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < b

def Good (N : ℕ) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), OKg gs[j] (N + j)

lemma Good_nil (N : ℕ) : Good N [] := by
  intro j hj; simp at hj

lemma Good_snoc {N : ℕ} {gs : List Gate} {g : Gate}
    (h : Good N gs) (hg : OKg g (N + gs.length)) :
    Good N (gs ++ [g]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hj' : j < gs.length
  · rw [List.getElem_append_left hj']; exact h j hj'
  · have heq : j = gs.length := by omega
    subst heq
    simpa using hg

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

def nc (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNot g.op).length

lemma nc_nil : nc [] = 0 := rfl

lemma nc_append (a b : List Gate) : nc (a ++ b) = nc a + nc b := by
  simp [nc, List.filter_append]

lemma nc_and (l : List ℕ) : nc [⟨GateOp.and, l⟩] = 0 := by simp [nc, isNot]

lemma nc_or (l : List ℕ) : nc [⟨GateOp.or, l⟩] = 0 := by simp [nc, isNot]

lemma nc_not (l : List ℕ) : nc [⟨GateOp.not, l⟩] = 1 := by simp [nc, isNot]

lemma notCount_eq_nc (gs : List Gate) (out : ℕ) :
    PEqualNP.NotBracket.notCount ⟨gs, out⟩ = nc gs := by
  unfold PEqualNP.NotBracket.notCount nc
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> simp [isNot]

lemma good_fanInTwo {N : ℕ} {gs : List Gate} (hG : Good N gs) (out : ℕ) :
    PEqualNP.MetaComplexity.FanInTwo ⟨gs, out⟩ := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
  obtain ⟨h1, h2, _⟩ := hG k hk
  refine ⟨?_, h2⟩
  rcases h1 with h | h | h <;> simp [h]

lemma good_readsBack {N : ℕ} {gs : List Gate} (hG : Good N gs) (out : ℕ) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, out⟩ := by
  intro k hk i hi
  simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hk] at hi
  exact (hG k hk).2.2 i hi

end CircuitDSL

section LowerBound

lemma gateOp_eval_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {l₁ l₂ : List Bool} (hlen : l₁.length = l₂.length)
    (hle : ∀ i (hi : i < l₁.length), l₁[i] = true → l₂[i]'(hlen ▸ hi) = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h1 b hb
    rcases List.mem_iff_getElem.mp hb with ⟨i, hi, rfl⟩
    have hi1 : i < l₁.length := hlen ▸ hi
    exact hle i hi1 (h1 l₁[i] (List.getElem_mem hi1))
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    rcases List.mem_iff_getElem.mp hb with ⟨i, hi, heq⟩
    exact ⟨l₂[i]'(hlen ▸ hi), List.getElem_mem _, hle i hi heq⟩

lemma exists_drop_between {L : ℕ} (u : Fin (L + 1) → Bool)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ L)
    (ha1 : u ⟨a, by omega⟩ = true) (hb0 : u ⟨b, by omega⟩ = false) :
    ∃ d : Fin L, a ≤ d.val ∧ d.val < b ∧ u d.castSucc = true ∧ u d.succ = false := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    rw [ha1] at hb0
    exact Bool.noConfusion hb0
  | succ b' ih =>
    by_cases heq : a = b' + 1
    · subst heq
      rw [ha1] at hb0
      exact Bool.noConfusion hb0
    · have hab' : a ≤ b' := by omega
      cases hub' : u ⟨b', by omega⟩
      · rcases ih hab' (by omega) ha1 hub' with ⟨d, hd1, hd2, hd3, hd4⟩
        exact ⟨d, hd1, by omega, hd3, hd4⟩
      · exact ⟨⟨b', by omega⟩, hab', by dsimp; omega, hub', hb0⟩

lemma card_le_of_between {L : ℕ} (A D : Finset (Fin L))
    (hbet : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁.val < a₂.val →
      ∃ d ∈ D, a₁.val < d.val ∧ d.val < a₂.val) :
    A.card ≤ D.card + 1 := by
  by_cases hA : A.Nonempty
  · set m := A.max' hA
    have hm : m ∈ A := Finset.max'_mem A hA
    set A' := A.erase m
    have hcardA : A'.card + 1 = A.card := Finset.card_erase_add_one hm
    have hex : ∀ a : Fin L, a ∈ A' → ∃ d ∈ D, a.val < d.val ∧ d.val < m.val := by
      intro a ha
      have hne : a ≠ m := (Finset.mem_erase.mp ha).1
      have haA : a ∈ A := Finset.mem_of_mem_erase ha
      have hle : a ≤ m := Finset.le_max' A a haA
      have hlt : a.val < m.val := by
        have : a < m := lt_of_le_of_ne hle hne
        exact this
      exact hbet a haA m hm hlt
    have hnext_ne : ∀ a, a ∈ A' → (A.filter (fun b => a.val < b.val)).Nonempty := by
      intro a ha
      refine ⟨m, Finset.mem_filter.mpr ⟨hm, ?_⟩⟩
      have hne : a ≠ m := (Finset.mem_erase.mp ha).1
      have hle : a ≤ m := Finset.le_max' A a (Finset.mem_of_mem_erase ha)
      exact (lt_of_le_of_ne hle hne : a < m)
    let nextA : Fin L → Fin L := fun a =>
      if ha : a ∈ A' then
        (A.filter (fun b => a.val < b.val)).min' (hnext_ne a ha)
      else a
    have hnext_mem : ∀ a (ha : a ∈ A'), nextA a ∈ A ∧ a.val < (nextA a).val := by
      intro a ha
      dsimp only [nextA]
      simp only [ha, ↓reduceDIte]
      have hmem := Finset.min'_mem (A.filter (fun b => a.val < b.val)) (hnext_ne a ha)
      exact Finset.mem_filter.mp hmem
    have hnext_le : ∀ a (ha : a ∈ A'), ∀ b ∈ A, a.val < b.val → (nextA a).val ≤ b.val := by
      intro a ha b hb hlt
      dsimp only [nextA]
      simp only [ha, ↓reduceDIte]
      exact Finset.min'_le _ b (Finset.mem_filter.mpr ⟨hb, hlt⟩)
    have hstep : ∀ a ∈ A', ∃ d ∈ D, a.val < d.val ∧ d.val < (nextA a).val := by
      intro a ha
      have hnm := hnext_mem a ha
      exact hbet a (Finset.mem_of_mem_erase ha) (nextA a) hnm.1 hnm.2
    let f : Fin L → Fin L := fun a =>
      if h : a ∈ A' then Classical.choose (hstep a h) else a
    have hf_mem : ∀ a ∈ A', f a ∈ D := by
      intro a ha
      dsimp only [f]
      simp only [ha, ↓reduceDIte]
      exact (Classical.choose_spec (hstep a ha)).1
    have hf_bounds : ∀ a ∈ A', a.val < (f a).val ∧ (f a).val < (nextA a).val := by
      intro a ha
      dsimp only [f]
      simp only [ha, ↓reduceDIte]
      exact (Classical.choose_spec (hstep a ha)).2
    have hf_inj : Set.InjOn f A' := by
      intro a₁ ha₁ a₂ ha₂ hfeq
      by_contra hne
      have hne_val : a₁.val ≠ a₂.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne_val with hlt | hlt
      · have h1 := (hf_bounds a₁ ha₁).2
        have h2 := hnext_le a₁ ha₁ a₂ (Finset.mem_of_mem_erase ha₂) hlt
        have h3 := (hf_bounds a₂ ha₂).1
        rw [hfeq] at h1
        omega
      · have h1 := (hf_bounds a₂ ha₂).2
        have h2 := hnext_le a₂ ha₂ a₁ (Finset.mem_of_mem_erase ha₁) hlt
        have h3 := (hf_bounds a₁ ha₁).1
        rw [← hfeq] at h1
        omega
    have hle : A'.card ≤ D.card := by
      calc A'.card = (A'.image f).card := (Finset.card_image_of_injOn hf_inj).symm
        _ ≤ D.card := Finset.card_le_card (Finset.image_subset_iff.mpr hf_mem)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

def drops {I L : ℕ} (xs : Fin (L + 1) → List Bool) (gs : List Gate) :
    Finset (Fin L) :=
  Finset.univ.filter (fun t : Fin L =>
    ∃ w < I + gs.length,
      (W gs (xs t.castSucc)).getD w false = true ∧
      (W gs (xs t.succ)).getD w false = false)

lemma markov_drops_bound {I L : ℕ} (xs : Fin (L + 1) → List Bool)
    (hlen : ∀ t : Fin (L + 1), (xs t).length = I)
    (hmono : ∀ t : Fin L, ∀ w < I,
      (xs t.castSucc).getD w false = true → (xs t.succ).getD w false = true) :
    ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      (drops (I := I) xs gs).card + 1 ≤ 2 ^ nc gs := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    have hemp : drops (I := I) xs [] = ∅ := by
      ext t
      simp only [drops, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_exists, List.length_nil, Nat.add_zero]
      rintro w ⟨hw, h1, h2⟩
      exact Bool.noConfusion ((hmono t w hw h1).symm.trans h2)
    rw [hemp]
    simp [nc]
  | append_singleton gs g ih =>
    intro hfan
    have hfan_pre : ∀ g' ∈ gs,
        (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_append_left _ hg')
    have hg_fan := hfan g (List.mem_append_right _ (List.mem_singleton_self g))
    have hih := ih hfan_pre
    set D := drops (I := I) xs gs
    set v : Fin (L + 1) → Bool := fun t => (W (gs ++ [g]) (xs t)).getD (I + gs.length) false
    set newD : Finset (Fin L) :=
      Finset.univ.filter (fun t : Fin L => v t.castSucc = true ∧ v t.succ = false)
    have hsplit : drops (I := I) xs (gs ++ [g]) = D ∪ newD := by
      ext t
      simp only [drops, D, newD, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        List.length_append, List.length_singleton]
      constructor
      · rintro ⟨w, hw, h1, h2⟩
        by_cases hlt : w < I + gs.length
        · left
          refine ⟨w, hlt, ?_, ?_⟩
          · rwa [W_getD_lt gs g (xs t.castSucc) w (by rw [W_length, hlen]; exact hlt)] at h1
          · rwa [W_getD_lt gs g (xs t.succ) w (by rw [W_length, hlen]; exact hlt)] at h2
        · have heq : w = I + gs.length := by omega
          subst heq
          exact Or.inr ⟨h1, h2⟩
      · rintro (⟨w, hw, h1, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨w, by omega, ?_, ?_⟩
          · rw [W_getD_lt gs g (xs t.castSucc) w (by rw [W_length, hlen]; exact hw)]; exact h1
          · rw [W_getD_lt gs g (xs t.succ) w (by rw [W_length, hlen]; exact hw)]; exact h2
        · exact ⟨I + gs.length, by omega, h1, h2⟩
    have hv_eq : ∀ t : Fin (L + 1),
        v t = g.op.eval (g.inputs.map fun i => (W gs (xs t)).getD i false) := by
      intro t
      dsimp only [v]
      rw [← hlen t]
      exact W_getD_last gs g (xs t)
    rcases hg_fan.1 with hop | hop | hop
    · have hnc : nc (gs ++ [g]) = nc gs := by
        rw [nc_append]; simp [nc, isNot, hop]
      have hsub : newD ⊆ D := by
        intro t ht
        simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        by_contra hnd
        have hnondec : ∀ i : ℕ, (W gs (xs t.castSucc)).getD i false = true →
            (W gs (xs t.succ)).getD i false = true := by
          intro i hi
          by_cases hilt : i < I + gs.length
          · cases h2 : (W gs (xs t.succ)).getD i false
            · exfalso
              apply hnd
              simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨i, hilt, hi, h2⟩
            · rfl
          · rw [W_getD_of_le gs (xs t.castSucc) i (by rw [hlen]; omega)] at hi
            exact Bool.noConfusion hi
        have htrue : v t.succ = true := by
          have h1 := ht.1
          rw [hv_eq] at h1 ⊢
          refine gateOp_eval_mono (Or.inl hop) (by simp) (fun idx hidx hval => ?_) h1
          simp only [List.length_map] at hidx
          simp only [List.getElem_map] at hval ⊢
          exact hnondec g.inputs[idx] hval
        rw [ht.2] at htrue
        exact Bool.noConfusion htrue
      rw [hsplit, Finset.union_eq_left.mpr hsub, hnc]
      exact hih
    · have hnc : nc (gs ++ [g]) = nc gs := by
        rw [nc_append]; simp [nc, isNot, hop]
      have hsub : newD ⊆ D := by
        intro t ht
        simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        by_contra hnd
        have hnondec : ∀ i : ℕ, (W gs (xs t.castSucc)).getD i false = true →
            (W gs (xs t.succ)).getD i false = true := by
          intro i hi
          by_cases hilt : i < I + gs.length
          · cases h2 : (W gs (xs t.succ)).getD i false
            · exfalso
              apply hnd
              simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨i, hilt, hi, h2⟩
            · rfl
          · rw [W_getD_of_le gs (xs t.castSucc) i (by rw [hlen]; omega)] at hi
            exact Bool.noConfusion hi
        have htrue : v t.succ = true := by
          have h1 := ht.1
          rw [hv_eq] at h1 ⊢
          refine gateOp_eval_mono (Or.inr hop) (by simp) (fun idx hidx hval => ?_) h1
          simp only [List.length_map] at hidx
          simp only [List.getElem_map] at hval ⊢
          exact hnondec g.inputs[idx] hval
        rw [ht.2] at htrue
        exact Bool.noConfusion htrue
      rw [hsplit, Finset.union_eq_left.mpr hsub, hnc]
      exact hih
    · have hnc : nc (gs ++ [g]) = nc gs + 1 := by
        rw [nc_append]; simp [nc, isNot, hop]
      have hnew_le : newD.card ≤ D.card + 1 := by
        cases hgin : g.inputs with
        | nil =>
          have hemp : newD = ∅ := by
            ext t
            simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, not_and]
            intro _
            rw [hv_eq, hop, hgin]
            simp [GateOp.eval]
          rw [hemp]; simp
        | cons a tl =>
          set u : Fin (L + 1) → Bool := fun t => (W gs (xs t)).getD a false
          have hvu : ∀ t, v t = !(u t) := by
            intro t
            rw [hv_eq, hop, hgin]
            simp [GateOp.eval, u]
          apply card_le_of_between newD D
          intro t₁ ht₁ t₂ ht₂ hlt
          simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and, hvu] at ht₁ ht₂
          have hu1 : u t₁.succ = true := by
            cases h : u t₁.succ <;> simp [h] at ht₁
            rfl
          have hu2 : u t₂.castSucc = false := by
            cases h : u t₂.castSucc <;> simp [h] at ht₂
            rfl
          obtain ⟨d, hd1, hd2, hd3, hd4⟩ :=
            exists_drop_between u (a := t₁.val + 1) (b := t₂.val) (by omega) (by omega) hu1 hu2
          refine ⟨d, ?_, by omega, hd2⟩
          simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
          have halt : a < I + gs.length := by
            by_contra hge
            have hfalse := W_getD_of_le gs (xs d.castSucc) a (by rw [hlen]; omega)
            dsimp only [u] at hd3
            rw [hfalse] at hd3
            exact Bool.noConfusion hd3
          exact ⟨a, halt, hd3, hd4⟩
      have hunion : (D ∪ newD).card ≤ D.card + newD.card := Finset.card_union_le D newD
      rw [hsplit, hnc, Nat.pow_succ]
      omega

lemma card_filter_lt (n m : ℕ) (hm : m ≤ n) :
    (Finset.univ.filter (fun u : Fin n => u.val < m)).card = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : Finset.univ.filter (fun u : Fin n => u.val < m + 1) =
        insert ⟨m, hm⟩ (Finset.univ.filter (fun u : Fin n => u.val < m)) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    rw [hsplit, Finset.card_insert_of_notMem (by simp), ih (by omega)]

end LowerBound
end PEqualNP.Outside.L_lib_1360.Mark

namespace PEqualNP.Outside.L_lib_1360
abbrev Word (a : ℕ) := Fin a → Bool
abbrev Row (a : ℕ) := Word a → ℕ
structure St (a : ℕ) where
  lev : ℤ
  word : Word a

def Below {a} (x y : St a) : Prop := x.lev < y.lev ∨ x.lev = y.lev ∧ x.word ≤ y.word
lemma brefl {a} (u : St a) : Below u u := Or.inr ⟨rfl,le_rfl⟩
lemma blevel {a} {u v : St a} (h : Below u v) : u.lev ≤ v.lev := by rcases h with h|h <;> omega
lemma btrans {a} {u v z : St a} (h : Below u v) (g : Below v z) : Below u z := by
  rcases h with h|⟨h,h'⟩ <;> rcases g with g|⟨g,g'⟩
  · exact Or.inl (lt_trans h g)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨h.trans g,h'.trans g'⟩

def Run {a} : List (Row a) → St a → St a → ℕ → Prop
  | [],u,v,_ => Below u v
  | c::cs,u,v,e => ∃ z, Below u z ∧ c z.word ≤ e ∧ Run cs z v (e-c z.word)
lemma runBounds {a} (l : List (Row a)) {u v e} (h : Run l u v e) : Below u v := by
  induction l generalizing u e with
  | nil => exact h
  | cons c cs ih => obtain ⟨z,hz,_,H⟩ := h; exact btrans hz (ih H)
lemma runLeft {a} {l : List (Row a)} {u v t e} (h : Below t u) (H : Run l u v e) : Run l t v e := by
  cases l with
  | nil => exact btrans h H
  | cons c cs => obtain ⟨z,hz,hc,hr⟩ := H; exact ⟨z,btrans h hz,hc,hr⟩
lemma runErase {a} (c : Row a) (cs : List (Row a)) {u v e} (h : Run (c::cs) u v e) : Run cs u v e := by
  have mono {l : List (Row a)} {x y : St a} {i j : Nat} (hij : i ≤ j) (H : Run l x y i) : Run l x y j := by
    induction l generalizing x i j with
    | nil => exact H
    | cons c cs ih => obtain ⟨z,hz,hc,hr⟩ := H; exact ⟨z,hz,hc.trans hij,ih (by omega) hr⟩
  obtain ⟨z,hz,_,hr⟩ := h; exact runLeft hz (mono (Nat.sub_le ..) hr)
lemma runZero {a} (l : List (Row a)) (u v : St a) (e : Nat) : Run ((fun _ => 0)::l) u v e ↔ Run l u v e :=
  ⟨runErase _ _,fun h => ⟨u,brefl _,Nat.zero_le _,by simpa using h⟩⟩
def shift {a} (n : ℤ) (x : St a) : St a := ⟨n+x.lev,x.word⟩
lemma shiftBelow {a} {u v : St a} (h : Below u v) (n : ℤ) : Below (shift n u) (shift n v) := by simpa [shift,Below] using h
lemma runShift {a} (l : List (Row a)) {u v e} (h : Run l u v e) (n : ℤ) : Run l (shift n u) (shift n v) e := by
  induction l generalizing u e with
  | nil => exact shiftBelow h n
  | cons c cs ih => obtain ⟨z,hz,hc,H⟩ := h; exact ⟨shift n z,shiftBelow hz n,hc,ih H⟩

abbrev Key (a R : ℕ) := (Fin a → Fin 3) ⊕ (Fin R × Word a × Word a)
def ends {a R} : Key a R → St a × St a
  | .inl t => (⟨0,fun j => decide (t j = 2)⟩,⟨0,fun j => decide (t j ≠ 0)⟩)
  | .inr (d,x,y) => (⟨0,x⟩,⟨(d.val:ℤ)+1,y⟩)
lemma stateEq {a} {x y : St a} (h : x.lev = y.lev) (g : x.word = y.word) : x = y := by cases x; cases y; congr
lemma key_rep {a R : ℕ} (u v : St a) (hb : Below u v) (hR : v.lev-u.lev ≤ (R:ℤ)) :
  ∃ k : Key a R, u = shift u.lev (ends k).1 ∧ v = shift u.lev (ends k).2 := by
  rcases hb with h|⟨h,hw⟩
  · let d : Fin R := ⟨(v.lev-u.lev-1).toNat,by omega⟩
    refine ⟨.inr (d,u.word,v.word),?_,?_⟩
    · refine stateEq ?_ rfl; simp [shift,ends]
    · refine stateEq ?_ rfl; simp [ends,shift,d]; omega
  · let t (j : Fin a) : Fin 3 := if u.word j then 2 else if v.word j then 1 else 0
    refine ⟨.inl t,?_,?_⟩
    · apply stateEq (by simp [ends,shift]); funext j
      cases hu : u.word j <;> cases hv : v.word j <;> simp [ends,shift,t,hu,hv]
    · apply stateEq (by simpa [ends,shift] using h.symm); funext j
      have hwj := hw j; cases hu : u.word j <;> cases hv : v.word j <;> simp_all [ends,shift,t] <;> exact (by decide : ¬(true ≤ false)) hwj
noncomputable def bad {a R E} (cs : List (Row a)) : Finset (Key a R × Fin (E+1)) := by
  classical
  exact Finset.univ.filter (fun t => ¬Run cs (ends t.1).1 (ends t.1).2 t.2.val)
lemma badMono {a R E} (c : Row a) (cs : List (Row a)) : bad (R:=R) (E:=E) cs ⊆ bad (c::cs) := by
  classical
  intro x hx; simp only [bad, Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢; exact fun h => hx (runErase _ _ h)
lemma equalBad {a R E} (c : Row a) (cs : List (Row a)) (same : bad (R:=R) (E:=E) cs = bad (c::cs)) {u v : St a} {e : Nat}
    (hr : v.lev-u.lev ≤ (R:ℤ)) (he : e ≤ E) (H : Run cs u v e) : Run (c::cs) u v e := by
  classical
  obtain ⟨k,hu,hv⟩ := key_rep u v (runBounds _ H) hr
  have existsOld := runShift _ H (-u.lev)
  have cancel (t : ℤ) (x : St a) : shift (-t) (shift t x) = x := stateEq (by simp [shift]) rfl
  have eu : shift (-u.lev) u = (ends k).1 := (congrArg (shift (-u.lev)) hu).trans (cancel ..)
  have ev : shift (-u.lev) v = (ends k).2 := (congrArg (shift (-u.lev)) hv).trans (cancel ..)
  rw [eu,ev] at existsOld
  let t : Key a R × Fin (E+1) := (k,⟨e,by omega⟩)
  have hnot : t ∉ bad cs := by simpa [bad,t] using existsOld
  rw [same] at hnot
  have H' : Run (c::cs) (ends k).1 (ends k).2 e := by simpa [bad,t] using hnot
  have := runShift _ H' u.lev
  rwa [← hu,← hv] at this

lemma compress {a R E : ℕ} {I : Type} [DecidableEq I] (row : I → Row a) (xs : List I) (nd : xs.Nodup) :
  ∃ S : Finset I, (∀ i ∈ S, i ∈ xs) ∧ S.card ≤ (bad (R:=R) (E:=E) (xs.map row)).card ∧
    ∀ (u v : St a) (e : ℕ), v.lev-u.lev ≤ (R:ℤ) → e ≤ E →
      (Run (xs.map row) u v e ↔ Run (xs.map (fun i => if i ∈ S then row i else fun _ => 0)) u v e) := by
  classical
  induction xs with
  | nil => exact ⟨∅,by simp,by simp,by simp⟩
  | cons i xs ih =>
    obtain ⟨S,hsub,hcard,H⟩ := ih nd.tail
    have hi : i ∉ S := fun h => (List.nodup_cons.mp nd).1 (hsub _ h)
    let cs := xs.map row
    by_cases same : bad (R:=R) (E:=E) cs = bad (row i::cs)
    · refine ⟨S,fun j hj => List.mem_cons_of_mem _ (hsub j hj),by simpa [cs] using hcard.trans (Finset.card_le_card (badMono (R:=R) (E:=E) (row i) cs)),?_⟩
      intro u v e hr he; simp only [List.map_cons,hi,ite_false,runZero]
      rw [← H u v e hr he]; exact ⟨runErase _ _,equalBad _ _ same hr he⟩
    · have hlt : (bad (R:=R) (E:=E) cs).card < (bad (row i::cs)).card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨badMono _ _,same⟩)
      refine ⟨insert i S,fun j hj => by rcases Finset.mem_insert.mp hj with rfl|h; exact List.mem_cons_self; exact List.mem_cons_of_mem _ (hsub _ h),?_,?_⟩
      · rw [Finset.card_insert_of_notMem hi]; change S.card+1 ≤ (bad (R:=R) (E:=E) (row i::cs)).card; exact Nat.succ_le_of_lt (lt_of_le_of_lt hcard hlt)
      · intro u v e hr he
        have eq : xs.map (fun j => if j ∈ insert i S then row j else fun _ => 0) = xs.map (fun j => if j ∈ S then row j else fun _ => 0) := by
          apply List.map_congr_left; intro j hj; have hne : j ≠ i := fun h => (List.nodup_cons.mp nd).1 (h ▸ hj); simp [hne]
        simp only [List.map_cons, Finset.mem_insert_self,ite_true,eq,Run]
        constructor <;> rintro ⟨z,hz,hc,hs⟩ <;> refine ⟨z,hz,hc,?_⟩
        · exact (H z v _ (by have := blevel hz; omega) (by omega)).1 hs
        · exact (H z v _ (by have := blevel hz; omega) (by omega)).2 hs
end PEqualNP.Outside.L_lib_1360

namespace PEqualNP.Outside.L_lib_1360
open Finset

def Ordered {a m} (q : Fin m → St a) := ∀ i j, i ≤ j → Below (q i) (q j)
lemma runFn {a m} (row : Fin m → Row a) (u v : St a) (e : ℕ) (uv : Below u v) :
  Run (List.ofFn row) u v e ↔ ∃ q : Fin m → St a, (∀ i, Below u (q i) ∧ Below (q i) v) ∧ Ordered q ∧ (∑ i, row i (q i).word) ≤ e := by
  induction m generalizing u e with
  | zero => simp [List.ofFn_zero,Run,uv,Ordered]
  | succ m ih =>
    rw [List.ofFn_succ]; constructor
    · rintro ⟨z,uz,hcost,tail⟩
      have zv := runBounds _ tail
      obtain ⟨q,hq,hord,hsum⟩ := (ih _ z _ zv).1 tail
      refine ⟨Fin.cases z q,Fin.cases ⟨uz,zv⟩ (fun i => ⟨btrans uz (hq i).1,(hq i).2⟩),?_,?_⟩
      · intro i j; refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases (fun _ => brefl z) (fun j _ => (hq j).1) j
        · refine Fin.cases (fun h => False.elim (by change i.val+1 ≤ 0 at h; omega)) (fun j h => hord i j (Fin.succ_le_succ_iff.mp h)) j
      · rw [Fin.sum_univ_succ]; simp only [Fin.cases_zero,Fin.cases_succ]; omega
    · rintro ⟨q,hq,hord,hsum⟩; rw [Fin.sum_univ_succ] at hsum
      refine ⟨q 0,(hq 0).1,by omega,(ih _ _ _ (hq 0).2).2 ⟨fun i => q i.succ,fun i => ⟨hord 0 i.succ (Fin.zero_le _),(hq _).2⟩,fun i j h => hord _ _ (Fin.succ_le_succ_iff.mpr h),?_⟩⟩
      dsimp only [Function.comp_apply]; omega

lemma runAppend {a} (p s : List (Row a)) (u v : St a) (e : ℕ) :
  Run (p++s) u v e ↔ ∃ t d, d ≤ e ∧ Run p u t d ∧ Run s t v (e-d) := by
  induction p generalizing u e with
  | nil =>
    constructor
    · intro h; exact ⟨u,0,by omega,brefl _,by simpa using h⟩
    · rintro ⟨t,d,hd,ht,hs⟩; apply runLeft ht
      have mono {l : List (Row a)} {x y : St a} {i j : Nat} (hij : i ≤ j) (H : Run l x y i) : Run l x y j := by
        induction l generalizing x i j with
        | nil => exact H
        | cons c cs ih => obtain ⟨z,hz,hc,hr⟩ := H; exact ⟨z,hz,hc.trans hij,ih (by omega) hr⟩
      exact mono (Nat.sub_le ..) hs
  | cons c cs ih =>
    constructor
    · rintro ⟨z,hz,hc,hs⟩; obtain ⟨t,d,hd,hcs,hss⟩ := (ih z _).1 hs
      refine ⟨t,c z.word+d,by omega,⟨z,hz,by omega,by simpa using hcs⟩,?_⟩
      simpa only [Nat.sub_add_eq] using hss
    · rintro ⟨t,d,hd,⟨z,hz,hc,hcs⟩,hss⟩
      refine ⟨z,hz,by omega,(ih z _).2 ⟨t,d-c z.word,by omega,hcs,?_⟩⟩
      convert hss using 1 <;> omega

lemma contextual {a R E} (pre mid alt post : List (Row a))
    (H : ∀ (u v : St a) e, v.lev-u.lev ≤ (R:ℤ) → e ≤ E → (Run mid u v e ↔ Run alt u v e))
    (u v : St a) (e : ℕ) (hr : v.lev-u.lev ≤ (R:ℤ)) (he : e ≤ E) :
    Run (pre++(mid++post)) u v e ↔ Run (pre++(alt++post)) u v e := by
  simp only [runAppend]; constructor
  · rintro ⟨x,d,hd,hp,y,f,hf,hm,hs⟩
    exact ⟨x,d,hd,hp,y,f,hf,(H x y f (by have := blevel (runBounds _ hp); have := blevel (runBounds _ hs); omega) (by omega)).1 hm,hs⟩
  · rintro ⟨x,d,hd,hp,y,f,hf,hm,hs⟩
    exact ⟨x,d,hd,hp,y,f,hf,(H x y f (by have := blevel (runBounds _ hp); have := blevel (runBounds _ hs); omega) (by omega)).2 hm,hs⟩
end PEqualNP.Outside.L_lib_1360

namespace PEqualNP.Outside.L_lib_1360
open Finset PEqualNP.CircuitLowerBounds
open Dervish53156Donor.Wiring1270

def pre {n} (t : Fin (n+1)) : Finset (Fin n) := univ.filter (fun j => j.val < t.val)
def timeOf {n} (s : Finset (Fin n)) : Fin (n+1) := ⟨s.card,Nat.lt_succ_of_le (by simpa using s.card_le_univ)⟩
lemma time_pre {n} (t : Fin (n+1)) : timeOf (pre t) = t := by
  apply Fin.ext; change _ = t.val; exact Mark.card_filter_lt n t.val (by omega)
def inp {n} (t : Fin (n+1)) := List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false,true]
lemma input_pre {n} (t : Fin (n+1)) : input (pre t) = inp t := by simp [input,pre,inp]
def limit (a b : ℕ) := if a=0 then 0 else 2^b-1
def low (a : ℕ) : St a := ⟨0,fun _ => false⟩
def high (a b : ℕ) : St a := ⟨limit a b,fun _ => true⟩
lemma lows {a} (z : St a) (h : 0 ≤ z.lev) : Below (low a) z := by rcases lt_or_eq_of_le h with h|h; exact Or.inl h; exact Or.inr ⟨h,fun _ => Bool.false_le _⟩
lemma highs {a b} (z : St a) (h : z.lev ≤ limit a b) : Below z (high a b) := by rcases lt_or_eq_of_le h with h|h; exact Or.inl h; exact Or.inr ⟨h,fun _ => Bool.le_true _⟩
def OK (n b : ℕ) (C : Circuit) := PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.output < n+2+C.size

def Fits {a n} (b e : Nat) (cs : Fin (n+1) → Row a) := ∃ (C : Circuit) (tap : Fin a → Nat), OK n b C ∧ (∀ j, tap j < n+2+C.size) ∧ (∑ t, cs t (fun j => (C.wires (inp t)).getD (tap j) false)) ≤ e

lemma toRun {a n b e} (cs : Fin (n+1) → Row a) (h : Fits b e cs) : Run (List.ofFn cs) (low a) (high a b) e := by
  classical
  obtain ⟨C,tap,hv,ht,hcost⟩ := h
  let w (t : Fin (n+1)) (j : Fin a) := (C.wires (inp t)).getD (tap j) false
  let M := Mark.drops (L:=n) (I:=n+2) inp C.gates
  have hin (t : Fin (n+1)) : (inp t).length = n+2 := by simp [inp]
  have mono (t : Fin n) (i : ℕ) (hi : i < n+2) : (inp t.castSucc).getD i false = true → (inp t.succ).getD i false = true := by
    by_cases h : i<n
    · rw [← input_pre, ← input_pre, bit _ (⟨i,h⟩ : Fin n), bit _ (⟨i,h⟩ : Fin n)]
      simp [pre]; omega
    · obtain rfl|rfl : i=n ∨ i=n+1 := by omega
      · simp [inp,List.getD_append_right]
      · simp [inp,List.getD_append_right]
  have costD := Mark.markov_drops_bound inp hin mono C.gates hv.1
  have nc : Mark.nc C.gates ≤ b := by rw [← Mark.notCount_eq_nc C.gates C.output]; exact hv.2.2.1
  have small : M.card < 2^b := (Nat.lt_of_succ_le costD).trans_le (Nat.pow_le_pow_right (by decide) nc)
  let ranks (t : Fin (n+1)) := M.filter (fun k => k.val < t.val)
  let q (t : Fin (n+1)) : St a := ⟨if a=0 then 0 else ((ranks t).card:ℤ), w t⟩
  refine (runFn _ _ _ _ (highs _ (by simp [low]))).2 ⟨q,?_,?_,hcost⟩
  · intro t; have leM : (ranks t).card ≤ M.card := card_filter_le ..
    constructor
    · apply lows; simp [q]; split <;> omega
    · apply highs; by_cases ha : a=0
      · simp [q,limit,ha]
      · simp only [q,limit,ha,ite_false]; exact_mod_cast (show (ranks t).card ≤ 2^b-1 by omega)
  · letI : Preorder (St a) := {le := Below, le_refl := brefl, le_trans := fun _ _ _ => btrans}
    change Monotone q; apply Fin.monotone_iff_le_succ.mpr; intro t
    change Below (q t.castSucc) (q t.succ)
    by_cases ha : a=0
    · subst a; exact Or.inr ⟨by simp [q],fun j => Fin.elim0 j⟩
    have hs : ranks t.castSucc ⊆ ranks t.succ := by intro j hj; obtain ⟨hm,hj⟩ := mem_filter.mp hj; exact mem_filter.mpr ⟨hm,by simpa using Nat.lt_succ_of_lt hj⟩
    by_cases h : t ∈ M
    · have hlt : (ranks t.castSucc).card < (ranks t.succ).card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs,by
        intro eq; have hmem : t ∈ ranks t.succ := mem_filter.mpr ⟨h,Nat.lt_succ_self _⟩; rw [← eq] at hmem; exact (Nat.lt_irrefl _) (mem_filter.mp hmem).2⟩)
      exact Or.inl (by simp [q,ha,hlt])
    · have eq : ranks t.castSucc = ranks t.succ := by
        apply Subset.antisymm hs; intro j hj; obtain ⟨hm,hj⟩ := mem_filter.mp hj; apply mem_filter.mpr; refine ⟨hm,?_⟩
        have ne : j.val ≠ t.val := fun e => h (Fin.ext e ▸ hm)
        change j.val < t.val+1 at hj; change j.val<t.val; omega
      refine Or.inr ⟨by simp [q,ha,eq],?_⟩; intro j
      change w t.castSucc j ≤ w t.succ j
      cases h₁ : w t.castSucc j <;> cases h₂ : w t.succ j <;> first | decide | exact (h (mem_filter.mpr ⟨mem_univ _,tap j, ht j,h₁,h₂⟩)).elim

lemma fromRun {a n b e} (cs : Fin (n+1) → Row a) (h : Run (List.ofFn cs) (low a) (high a b) e) : Fits b e cs := by
  classical
  obtain ⟨q,bounds,ordered,hsum⟩ := (runFn _ _ _ _ (highs _ (by simp [low]))).1 h
  let stage (s : Finset (Fin n)) := (q (timeOf s)).lev.toNat
  let word (s : Finset (Fin n)) := (q (timeOf s)).word
  let S := (univ : Finset (Fin (n+1))).image pre
  have loq (i) : 0 ≤ (q i).lev := blevel (bounds i).1
  have hiq (i) : (q i).lev ≤ limit a b := blevel (bounds i).2
  have hm {x y : Finset (Fin n)} (hxy : x ⊆ y) : Below (q (timeOf x)) (q (timeOf y)) := ordered _ _ (Finset.card_le_card hxy : x.card ≤ y.card)
  have hcap : limit a b < 2^b := by
    have hp : 0 < 2^b := by positivity
    unfold limit; split <;> omega
  obtain ⟨C,tap,fan,back,out,notc,ev⟩ := DervishCompileSlot53156.compile_slot S stage word (limit a b) b hcap
    (fun s _ => by have := hiq (timeOf s); dsimp [stage]; omega)
    (fun _ _ _ _ hxy => Int.toNat_le_toNat (blevel (hm hxy))) (by
      intro x _ y _ hxy heq j hj
      have hl := loq (timeOf x); have hr := loq (timeOf y); change (q _).lev.toNat = (q _).lev.toNat at heq
      rcases hm hxy with hh|⟨_,hw⟩
      · omega
      · have hv := hw j; change (q (timeOf x)).word j = true at hj; rw [hj] at hv; exact Bool.eq_true_of_true_le hv)
  refine ⟨C,fun j => (tap j).val,⟨fan,back,notc,out⟩,fun j => (tap j).isLt, le_trans ?_ hsum⟩
  apply Finset.sum_le_sum; intro t _; apply le_of_eq; congr 1; funext j
  simpa [word,time_pre,input_pre] using ev (pre t) (mem_image_of_mem pre (mem_univ t)) j
end PEqualNP.Outside.L_lib_1360

namespace PEqualNP.Outside.L_lib_1360
open Finset

def firstIdx {l n r : Nat} (i : Fin l) : Fin (l+n+r+1) := ⟨i.val,by omega⟩
def midIdx {l n r : Nat} (i : Fin (n+1)) : Fin (l+n+r+1) := ⟨l+i.val,by omega⟩
def lastIdx {l n r : Nat} (i : Fin r) : Fin (l+n+r+1) := ⟨l+n+1+i.val,by omega⟩
lemma splitRows {l n r} {α : Type} (f : Fin (l+n+r+1) → α) :
  List.ofFn f = List.ofFn (fun i : Fin l => f (firstIdx i)) ++ (List.ofFn (fun i : Fin (n+1) => f (midIdx i)) ++ List.ofFn (fun i : Fin r => f (lastIdx i))) := by
  apply List.ext_getElem (by simp; omega); intro i hi hj
  simp only [List.getElem_ofFn,List.getElem_append,List.length_ofFn]
  split <;> (try split) <;> (try simp only [List.getElem_ofFn]) <;> congr 1 <;> apply Fin.ext <;> dsimp [firstIdx,midIdx,lastIdx] <;> omega

def kept {l n r} (S : Finset (Fin (n+1))) : Finset (Fin (l+n+r+1)) := univ.filter (fun t => ¬∃ i : Fin (n+1), i ∉ S ∧ t.val = l+i.val)
def masked {m a} (S : Finset (Fin m)) (f : Fin m → Row a) (t : Fin m) : Row a := if t ∈ S then f t else fun _ => 0
lemma coreResult (n a B E : ℕ) (loc : Fin (n+1) → Row a) :
  ∃ S : Finset (Fin (n+1)), S.card ≤ (E+1)*(if a=0 then 1 else 3^a+(2^B-1)*4^a) ∧
    ∀ (l r : ℕ) (cost : Fin (l+n+r+1) → Row a), (∀ t (i : Fin (n+1)) w, t.val=l+i.val → cost t w=loc i w) →
    ∀ b ≤ B, ∀ e ≤ E, Fits b e cost ↔ Fits b e (masked (kept S) cost) := by
  classical
  obtain ⟨S,_,bound,H⟩ := compress (R:=limit a B) (E:=E) loc (List.finRange (n+1)) (List.nodup_finRange _)
  refine ⟨S,bound.trans ?_,?_⟩
  · apply (Finset.card_le_univ _).trans
    have four : (2:Nat)^a*2^a=4^a := by rw [← mul_pow]; rfl
    by_cases ha : a=0
    · simp [Key,limit,ha]
    · simp [Key,limit,ha,Word,Fintype.card_pi_const,four,Nat.mul_assoc,Nat.mul_comm]
  · intro l r cost hc b hb e he
    let alt := masked (kept S) cost
    have hfirst (i : Fin l) : alt (firstIdx i) = cost (firstIdx i) := by
      have hm : firstIdx (n:=n) (r:=r) i ∈ kept S := by simp [kept,firstIdx]; intros; omega
      simp [alt,masked,hm]
    have hlast (i : Fin r) : alt (lastIdx i) = cost (lastIdx i) := by
      have hm : lastIdx (n:=n) (l:=l) i ∈ kept S := by simp [kept,lastIdx]; intros; omega
      simp [alt,masked,hm]
    have hmid (i : Fin (n+1)) : cost (midIdx i) = loc i := funext (fun w => hc _ i w rfl)
    have hkeep (i : Fin (n+1)) : midIdx (l:=l) (r:=r) i ∈ kept S ↔ i ∈ S := by
      simp only [kept,Finset.mem_filter,Finset.mem_univ,true_and,midIdx,Nat.add_left_cancel_iff,Fin.val_inj]; simp
    have halt (i : Fin (n+1)) : alt (midIdx i) = (if i ∈ S then loc i else fun _ => 0) := by simp only [alt,masked,hkeep,hmid]
    have H' (u v : St a) (z : ℕ) (hr : v.lev-u.lev ≤ (limit a B:ℤ)) (hz : z ≤ E) :
        Run (List.ofFn loc) u v z ↔ Run (List.ofFn (fun i => if i ∈ S then loc i else fun _ => 0)) u v z := by
      have eq (g : Fin (n+1) → Row a) : (List.finRange (n+1)).map g = List.ofFn g := by
        apply List.ext_getElem (by simp); intros; rw [List.getElem_ofFn,List.getElem_map]; simp
      simpa only [eq] using H u v z hr hz
    have hb' : (high a b).lev - (low a).lev ≤ (limit a B : ℤ) := by
      have hp : (2:Nat)^b ≤ 2^B := Nat.pow_le_pow_right (by decide) hb
      change (limit a b : ℤ)-0 ≤ _; rw [sub_zero]; apply Int.ofNat_le.mpr
      unfold limit; split <;> omega
    have runs : Run (List.ofFn cost) (low a) (high a b) e ↔ Run (List.ofFn alt) (low a) (high a b) e := by
      rw [splitRows (l:=l) (n:=n) (r:=r) cost,splitRows (l:=l) (n:=n) (r:=r) alt]
      simp_rw [hfirst,hlast,hmid,halt]; exact contextual _ _ _ _ H' _ _ _ hb' he
    exact ⟨fun h => fromRun _ (runs.1 (toRun _ h)),fun h => fromRun _ (runs.2 (toRun _ h))⟩
end PEqualNP.Outside.L_lib_1360

open PEqualNP.Outside.L_lib_1360 in
theorem PEqualNP.Outside.L_lib_1360 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let fit := fun (a n b e : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat)
    (S : Finset (Fin (n+1))) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧ C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
    S.sum (fun t => cost t (fun i => (C.wires
      (List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false,true])).getD (tap i) false)) ≤ e
∀ (n a B E : Nat) (localCost : Fin (n+1) → (Fin a → Bool) → Nat),
  let types := if a = 0 then 1 else 3^a + (2^B-1)*4^a
  ∃ S : Finset (Fin (n+1)), S.card ≤ (E+1)*types ∧
    ∀ (l r : Nat) (cost : Fin (l+n+r+1) → (Fin a → Bool) → Nat),
      (∀ (t : Fin (l+n+r+1)) (i : Fin (n+1)) w, t.val = l+i.val → cost t w = localCost i w) →
      let keep := (Finset.univ : Finset (Fin (l+n+r+1))).filter
        (fun t => ¬ ∃ i : Fin (n+1), i ∉ S ∧ t.val = l+i.val)
      ∀ b ≤ B, ∀ e ≤ E, fit a (l+n+r) b e cost Finset.univ ↔ fit a (l+n+r) b e cost keep) := by
  intro fit n a B E loc types
  obtain ⟨S,hs,H⟩ := coreResult n a B E loc
  refine ⟨S,?_,?_⟩
  · dsimp only [types]; by_cases h : a = 0 <;> simpa [h] using hs
  · intro l r cost hc keep b hb e he
    have hin (t : Fin (l+n+r+1)) : (List.ofFn (fun j : Fin (l+n+r) => @decide (j.val < t.val) (Classical.propDecidable _)) ++ [false,true]) = inp t := by
      unfold inp; congr 1; apply List.ext_getElem (by simp); intros; simp only [List.getElem_ofFn]; exact congrArg (@decide _) (Subsingleton.elim _ _)
    have cv (T : Finset (Fin (l+n+r+1))) : fit a (l+n+r) b e cost T ↔ Fits b e (masked T cost) := by
      dsimp only [fit,Fits,OK]
      simp only [hin]
      have eq (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat) :
          (∑ t, masked T cost t (fun j => (C.wires (inp t)).getD (tap j) false)) =
          ∑ t ∈ T, cost t (fun j => (C.wires (inp t)).getD (tap j) false) := by
        rw [← Finset.sum_subset (Finset.subset_univ T) (fun i _ h => show masked T cost i _ = 0 by simp [masked,h])]
        exact Finset.sum_congr rfl fun i h => by simp [masked,h]
      simp only [eq]; tauto
    have ku : keep = kept (l:=l) (r:=r) S := by ext t; simp [keep,kept]
    rw [cv,cv,ku]
    have mU : masked Finset.univ cost = cost := by funext t; simp [masked]
    rw [mU]; exact H l r cost hc b hb e he

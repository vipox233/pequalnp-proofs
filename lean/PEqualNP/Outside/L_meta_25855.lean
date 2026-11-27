import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25855_aux
namespace Skeleton25855
open PEqualNP.CircuitLowerBounds
structure Ref where
  idx : Nat
  act : Bool → Bool
def Ref.run (r : Ref) (s : List Bool) := r.act (s.getD r.idx false)
def fallback : Ref := ⟨0,fun _ => false⟩
structure Node where
  a : Nat
  b : Nat
  act : Bool → Bool → Bool
def step (s : List Bool) (g : Node) := s ++ [g.act (s.getD g.a false) (s.getD g.b false)]
def physical (s : List Bool) (g : Gate) := s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]
def ok (n : Nat) (gs : List Node) : Prop := ∀ i (hi : i < gs.length), gs[i].a < n+i ∧ gs[i].b < n+i
theorem compile (gs : List Gate) (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) {m : Nat} (rs : List Ref) (hpos : 0 < m) (hr : ∀ r ∈ rs,r.idx < m) :
    ∃ (ds : List Node) (result : List Ref), ok m ds ∧ ds.length = gs.countP (fun g => g.inputs.length == 2) ∧
      (∀ r ∈ result,r.idx < m +ds.length) ∧ ∀ s : List Bool, s.length=m →
      gs.foldl physical (rs.map (fun r => r.run s)) = result.map (fun r => r.run (ds.foldl step s)) := by
  induction gs generalizing m rs with
  | nil => exact ⟨[],rs,by simp [ok],rfl,by simpa using hr,by simp⟩
  | cons g gs ih =>
    have hg := fan g (by simp)
    have htail : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun x hx => fan x (by simp [hx])
    have get (i : Nat) : (rs.getD i fallback).idx < m := by
      by_cases h : i < rs.length
      · simp [List.getD_eq_getElem?_getD,h,hr _ (List.getElem_mem h)]
      · simp [List.getD_eq_getElem?_getD,h,fallback,hpos]
    have ev (s : List Bool) (i : Nat) : (rs.map (fun r => r.run s)).getD i false = (rs.getD i fallback).run s := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; cases rs[i]? <;> rfl
    cases h : g.inputs with
    | nil =>
      let r : Ref := ⟨0,fun _ => g.op.eval []⟩
      obtain ⟨ds,out,hd,hn,ho,hw⟩ := ih htail (rs++[r]) hpos (by intro z hz; rcases List.mem_append.mp hz with hz|hz; exact hr z hz; obtain rfl := List.mem_singleton.mp hz; exact hpos)
      refine ⟨ds,out,hd,by simpa [List.countP_cons,h] using hn,ho,?_⟩
      intro s hs; simpa [physical,h,r,Ref.run] using hw s hs
    | cons a more => cases hh : more with
      | nil =>
        let t := rs.getD a fallback
        let r : Ref := ⟨t.idx,fun b => g.op.eval [t.act b]⟩
        obtain ⟨ds,out,hd,hn,ho,hw⟩ := ih htail (rs++[r]) hpos (by intro z hz; rcases List.mem_append.mp hz with hz|hz; exact hr z hz; obtain rfl := List.mem_singleton.mp hz; exact get a)
        refine ⟨ds,out,hd,by simpa [List.countP_cons,h,hh] using hn,ho,?_⟩
        intro s hs
        simp only [List.foldl_cons,physical,h,hh,List.map_cons,List.map_nil]
        rw [ev s a]; simpa only [List.map_append,List.map_cons,List.map_nil,r,t,Ref.run] using hw s hs
      | cons b rest => cases hrest : rest with
        | cons z zs => simp [h,hh,hrest] at hg
        | nil =>
          let x := rs.getD a fallback
          let y := rs.getD b fallback
          let nd : Node := ⟨x.idx,y.idx,fun l r => g.op.eval [x.act l,y.act r]⟩
          let r : Ref := ⟨m,id⟩
          obtain ⟨ds,out,hd,hn,ho,hw⟩ := ih htail (rs++[r]) (m:=m+1) (by omega) (by
            intro z hz; simp only [List.mem_append,List.mem_singleton] at hz; rcases hz with hz|rfl
            · exact Nat.lt_trans (hr z hz) (by omega)
            · exact Nat.lt_succ_self _)
          refine ⟨nd::ds,out,?_,by simp [List.countP_cons,h,hh,hrest,hn,Nat.add_comm],?_,?_⟩
          · intro i hi; cases i with
            | zero => exact ⟨get a,get b⟩
            | succ j => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hd j (by simpa using hi)
          · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ho
          · intro s hs
            have eq : (rs++[r]).map (fun z => z.run (step s nd)) = physical (rs.map (fun z => z.run s)) g := by
              simp only [List.map_append,List.map_cons,List.map_nil,physical,h,hh,hrest,ev]
              congr 1
              · apply List.map_congr_left; intro z hz; simp [Ref.run,step,List.getD_eq_getElem?_getD,List.getElem?_append_left (show z.idx<s.length by rw [hs]; exact hr z hz)]
              · simp [r,Ref.run,step,←hs,nd,x,y,List.getD_eq_getElem?_getD]
            simpa only [List.foldl_cons,eq] using hw (step s nd) (by simp [step,hs])
end Skeleton25855

namespace Shape25855
open Skeleton25855 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def gate (x : Node) : Gate := ⟨.or,[x.a,x.b]⟩
def shape (ds : List Node) (o : Nat) : Circuit := ⟨ds.map gate,o⟩
theorem wire {ds : List Node} {j : Nat} (hj : j < ds.length) (o : Nat) : gateAt (shape ds o) j = gate ds[j] := by simp [gateAt,shape,List.getD_eq_getElem?_getD,hj]
theorem earlier {n : Nat} {ds : List Node} (h : ok n ds) (o : Nat) : ReadsBack n (shape ds o) := by
  intro j hj i hi; have lt : j < ds.length := by simpa [shape] using hj
  rw [wire lt] at hi; simp [gate] at hi
  rcases hi with rfl|rfl; exact (h j lt).1; exact (h j lt).2
theorem counted {ds : List Node} {j w o : Nat} (hj : j<ds.length) (rd : ds[j].a=w ∨ ds[j].b=w) :
    0 < readsIn (shape ds o) (Finset.range ds.length) w := by
  have hp : 0 < (gateAt (shape ds o) j).inputs.count w := by
    rw [wire hj]; apply List.count_pos_iff.mpr; simpa [gate,eq_comm] using rd
  exact hp.trans_le (Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt (shape ds o) i).inputs.count w)) (Finset.mem_range.mpr hj))
end Shape25855


namespace Private25855

open Finset
open scoped BigOperators


def errors {ι κ : Type*} [Fintype ι] [Fintype κ] (T H : ι → κ → Bool) : ℕ :=
  (univ.filter fun z : ι × κ => T z.1 z.2 ≠ H z.1 z.2).card

def distance {κ : Type*} [Fintype κ] (x y : κ → Bool) : ℕ :=
  (univ.filter fun c => x c ≠ y c).card

theorem error_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (T H : ι → κ → Bool) :
    errors T H = ∑ i, distance (T i) (H i) := by
  simp only [errors, distance, Finset.card_filter, Fintype.sum_prod_type]

theorem error_transpose {ι κ : Type*} [Fintype ι] [Fintype κ] (T H : ι → κ → Bool) :
    errors (Function.swap T) (Function.swap H) = errors T H := by
  simp only [error_sum, distance, Finset.card_filter, Function.swap]
  rw [Finset.sum_comm]

theorem distance_triangle {κ : Type*} [Fintype κ] (x y z : κ → Bool) :
    distance x z ≤ distance x y + distance y z := by
  classical
  unfold distance
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro c hc
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at *
  by_cases h : x c = y c
  · exact Or.inr fun e => hc (h.trans e)
  · exact Or.inl h

theorem distance_comm {κ : Type*} [Fintype κ] (x y : κ → Bool) : distance x y = distance y x := by
  simp only [distance, ne_comm]

theorem heavy {ι κ : Type*} [Fintype ι] [Fintype κ] (T H : ι → κ → Bool) (v : ℕ) (hv : 0<v) :
    (univ.filter fun i => v ≤ distance (T i) (H i)).card ≤ errors T H / v := by
  classical
  apply (Nat.le_div_iff_mul_le hv).2
  rw [error_sum]
  let s := univ.filter fun i => v ≤ distance (T i) (H i)
  calc
    s.card * v = ∑ _i∈s, v := by simp
    _ ≤ ∑ i∈s, distance (T i) (H i) := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

theorem good_distance {ι κ : Type*} [Fintype κ] (T H : ι → κ → Bool) {v t : ℕ} {i j : ι}
    (sep : t+2*(v-1) ≤ distance (T i) (T j))
    (hi : distance (T i) (H i)<v) (hj : distance (T j) (H j)<v) : t ≤ distance (H i) (H j) := by
  have left := distance_triangle (T i) (H i) (T j)
  have right := distance_triangle (H i) (H j) (T j)
  rw [distance_comm (H j) (T j)] at right
  omega


theorem response_injective {ι κ K : Type*} [Fintype κ] [DecidableEq κ] (H : ι → κ → Bool)
    (S : Finset ι) (exc : Finset κ) (code : ι → K) (t : ℕ) (small : exc.card<t)
    (sep : ∀ i∈S, ∀ j∈S, i≠j → t ≤ distance (H i) (H j))
    (sound : ∀ i∈S, ∀ j∈S, code i=code j → ∀ c∉exc, H i c=H j c) : Set.InjOn code (↑S) := by
  classical
  intro i hi j hj eq
  by_contra ne
  have lo := sep i hi j hj ne
  have sub : (univ.filter fun c => H i c ≠ H j c) ⊆ exc := by
    intro c hc
    by_contra out
    exact (Finset.mem_filter.mp hc).2 (sound i hi j hj eq c out)
  have cap := Finset.card_le_card sub
  unfold distance at lo
  omega


theorem common_private {ι κ K : Type*} [DecidableEq K] (X : Finset ι) (Y : Finset κ)
    (row : ι → K) (col : κ → K) (slots : Finset K)
    (rx : Set.InjOn row (↑X)) (cy : Set.InjOn col (↑Y))
    (insideR : X.image row ⊆ slots) (insideC : Y.image col ⊆ slots) :
    ∃ p : ℕ, ∃ x : Fin p → ι, ∃ y : Fin p → κ,
      Function.Injective x ∧ Function.Injective y ∧
      (∀ j, x j∈X ∧ y j∈Y ∧ row (x j)=col (y j)) ∧ X.card+Y.card ≤ slots.card+p := by
  classical
  let M := X.image row ∩ Y.image col
  let e : Fin M.card ≃ M := (Fintype.equivFinOfCardEq (by simp)).symm
  have hx (j : Fin M.card) : ∃ i∈X, row i=(e j).val := Finset.mem_image.mp (Finset.mem_inter.mp (e j).property).1
  have hy (j : Fin M.card) : ∃ i∈Y, col i=(e j).val := Finset.mem_image.mp (Finset.mem_inter.mp (e j).property).2
  choose x xmem xeq using hx
  choose y ymem yeq using hy
  refine ⟨M.card,x,y,?_,?_,fun j => ⟨xmem j,ymem j,(xeq j).trans (yeq j).symm⟩,?_⟩
  · intro i j h; apply e.injective; apply Subtype.ext; rw [←xeq,←xeq,h]
  · intro i j h; apply e.injective; apply Subtype.ext; rw [←yeq,←yeq,h]
  · have total := Finset.card_union_add_card_inter (X.image row) (Y.image col)
    rw [Finset.card_image_of_injOn rx, Finset.card_image_of_injOn cy] at total
    have cap := Finset.card_le_card (Finset.union_subset insideR insideC)
    change _ ≤ _ + (X.image row ∩ Y.image col).card
    omega


theorem label_ledger {N b H p K P Q S X Y : ℕ}
    (coverage : 2*N ≤ X+Y+S+2*H+4)
    (scarcity : K+2*N ≤ b+3+2*H)
    (shared : S ≤ K+12*H) (pure : P ≤ 2*K+1) (chain : Q ≤ 4*K)
    (slots : X+Y ≤ P+3*Q+p) : 32*N ≤ p+15*b+50+44*H := by omega


theorem conflicts {p : ℕ} {κ : Type*} [DecidableEq κ] (piece : Fin p → κ)
    (M : Fin p → Fin p → Bool)
    (capacity : ∀ i, (univ.filter fun j => piece j=piece i).card ≤ 3)
    (swap : ∀ i j, piece i≠piece j → M i j=M j i) :
    (univ.filter fun z : Fin p × Fin p => z.1 < z.2 ∧ M z.1 z.2 ≠ M z.2 z.1).card ≤ p := by
  classical
  let E := univ.filter fun z : Fin p × Fin p => z.1 < z.2 ∧ M z.1 z.2 ≠ M z.2 z.1
  let F := univ.filter fun z : Fin p × Fin p => z.2 < z.1 ∧ M z.1 z.2 ≠ M z.2 z.1
  have mirror : E.card=F.card := by
    apply Finset.card_bij' (fun z _ => z.swap) (fun z _ => z.swap)
    · simp
    · simp
    · rintro ⟨i,j⟩ h
      exact Finset.mem_filter.mpr ⟨by simp,(Finset.mem_filter.mp h).2.1,Ne.symm (Finset.mem_filter.mp h).2.2⟩
    · rintro ⟨i,j⟩ h
      exact Finset.mem_filter.mpr ⟨by simp,(Finset.mem_filter.mp h).2.1,Ne.symm (Finset.mem_filter.mp h).2.2⟩
  have dis : Disjoint E F := by
    apply Finset.disjoint_left.mpr
    intro z he hf
    have h := (Finset.mem_filter.mp he).2.1
    have h' := (Finset.mem_filter.mp hf).2.1
    omega
  let U := univ.filter fun z : Fin p × Fin p => M z.1 z.2 ≠ M z.2 z.1
  have uf : E ∪ F ⊆ U := by
    intro z h
    rcases Finset.mem_union.mp h with h|h <;> exact Finset.mem_filter.mpr ⟨by simp,(Finset.mem_filter.mp h).2.2⟩
  have cap (i : Fin p) : (univ.filter fun j => M i j ≠ M j i).card ≤ 2 := by
    let A := univ.filter fun j => piece j=piece i
    have hi : i∈A := by simp [A]
    have sub : (univ.filter fun j => M i j ≠ M j i) ⊆ A.erase i := by
      intro j h
      have bad := (Finset.mem_filter.mp h).2
      refine Finset.mem_erase.mpr ⟨?_,Finset.mem_filter.mpr ⟨by simp,?_⟩⟩
      · rintro rfl; exact bad rfl
      · by_contra ne; exact bad (swap i j (Ne.symm ne))
    have c := Finset.card_erase_of_mem hi
    have c' := capacity i
    have := Finset.card_le_card sub
    change A.card≤3 at c'
    have := Finset.card_pos.mpr ⟨i,hi⟩
    omega
  have ub : U.card ≤ 2*p := by
    change errors M (Function.swap M) ≤ _
    rw [error_sum]
    calc
      _ ≤ ∑ _i : Fin p, 2 := Finset.sum_le_sum fun i _ => cap i
      _ = _ := by simp [Nat.mul_comm]
  have h := Finset.card_le_card uf
  rw [Finset.card_union_of_disjoint dis] at h
  change E.card ≤ p
  omega

end Private25855

namespace Private25855
open Finset PEqualNP.CircuitLowerBounds PEqualNP.Represents

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def bin (g : Gate) := g.inputs.length == 2

theorem snoc (w : List Bool) (v : Bool) (i : ℕ) : (w++[v]).getD i false =
    if i<w.length then w.getD i false else if i=w.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h e
  · rw [List.getElem?_append_left h]
  · subst e; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp


theorem cone (n : ℕ) (gs : List Gate) (hg : ∀ g∈gs, g.inputs.length≤2) (R : Finset ℕ) :
    ∃ S : Finset ℕ, S.card≤R.card+gs.countP bin ∧
      ∀ x y : List Bool, x.length=n → y.length=n → (∀ i∈S, x.getD i false=y.getD i false) →
        ∀ i∈R, (gs.foldl step x).getD i false=(gs.foldl step y).getD i false := by
  induction gs generalizing n with
  | nil => exact ⟨R,by simp,fun _ _ _ _ h => h⟩
  | cons g gs ih =>
    obtain ⟨S,cap,det⟩ := ih (n+1) (fun k hk => hg k (by simp [hk]))
    let U := if n∈S then S.erase n ∪ g.inputs.toFinset else S
    refine ⟨U,?_,?_⟩
    · have len := hg g (by simp)
      simp only [List.countP_cons]
      by_cases h : n∈S
      · rw [show U=S.erase n ∪ g.inputs.toFinset from if_pos h]
        have er := Finset.card_erase_of_mem h
        have pos := Finset.card_pos.mpr ⟨n,h⟩
        have reads := List.toFinset_card_le g.inputs
        have united := Finset.card_union_le (S.erase n) g.inputs.toFinset
        simp only [bin,beq_iff_eq]
        split <;> omega
      · rw [show U=S from if_neg h]; omega
    · intro x y hx hy eq
      apply det (step x g) (step y g) (by simp [step,hx]) (by simp [step,hy])
      intro i hi
      simp only [step,snoc,hx,hy]
      split_ifs with small top
      · apply eq i; by_cases hn : n∈S <;> simp_all [U]; omega
      · subst i
        congr 1
        exact List.map_congr_left fun j hj => eq j (by simp [U, hi, hj])
      · rfl

theorem hotPin {n m : ℕ} (i : Fin n) (j : Fin m) (w : ℕ) :
    (oneEach i j).getD w false=true ↔ w=i.val ∨ w=n+j.val := by
  simp only [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega


theorem circuit_budget {N v : ℕ} (T : Fin N → Fin N → Bool) (C : Circuit)
    (fan : ∀ g∈C.gates, g.inputs.length≤2) (hv : 0<v)
    (sep : ∀ i j : Fin N, i≠j → 17+2*(v-1) ≤ distance (T i) (T j) ∧
      17+2*(v-1) ≤ distance (Function.swap T i) (Function.swap T j)) :
    let M := fun i j : Fin N => C.eval (oneEach i j)
    2*N ≤ C.gates.countP bin + 3 + 2*(errors T M/v) := by
  classical
  intro M
  obtain ⟨S,cap,det⟩ := cone (N+N) C.gates fan {C.output}
  simp only [Finset.card_singleton] at cap
  let seenR := univ.filter fun i : Fin N => i.val∈S
  let seenC := univ.filter fun i : Fin N => N+i.val∈S
  have budget : seenR.card+seenC.card≤S.card := by
    let A := seenR.image Fin.val
    let B := seenC.image (fun i => N+i.val)
    have ar : A.card=seenR.card := Finset.card_image_of_injective _ Fin.val_injective
    have bc : B.card=seenC.card := Finset.card_image_of_injective _ (fun i j h => Fin.ext (Nat.add_left_cancel h))
    have dis : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      rintro w ha hb
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j,_,h⟩ := Finset.mem_image.mp hb
      have := i.isLt
      omega
    rw [←ar,←bc,←Finset.card_union_of_disjoint dis]
    apply Finset.card_le_card
    intro w hw
    rcases Finset.mem_union.mp hw with hm|hm <;>
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hm <;> exact (Finset.mem_filter.mp hi).2
  have zeroes (H D : Fin N → Fin N → Bool) (seen : Finset (Fin N))
      (good : ∀ i j, i≠j → 17+2*(v-1)≤distance (H i) (H j))
      (outside : ∀ i∉seen, ∀ j∉seen, D i=D j) :
      N ≤ seen.card + errors H D/v + 1 := by
    let X := univ.filter fun i => i∉seen ∧ distance (H i) (D i)<v
    have atMost : X.card≤1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      obtain ⟨oi,li⟩ := (Finset.mem_filter.mp hi).2
      obtain ⟨oj,lj⟩ := (Finset.mem_filter.mp hj).2
      by_contra ne
      have d := good_distance H D (good i j ne) li lj
      rw [outside i oi j oj] at d
      simp [distance] at d
    let B := univ.filter fun i => v≤distance (H i) (D i)
    have sub : univ ⊆ seen ∪ B ∪ X := by
      intro i hi
      by_cases s : i∈seen <;> by_cases h : v≤distance (H i) (D i) <;> simp_all [B,X]
    have cb := Finset.card_le_card sub
    simp only [Finset.card_univ,Fintype.card_fin] at cb
    have := Finset.card_union_le (seen ∪ B) X
    have := Finset.card_union_le seen B
    have heavyB : B.card ≤ errors H D/v := heavy H D v hv
    omega
  have same (i j x y : Fin N) (pins : ∀ w∈S, (w=i.val ∨ w=N+x.val) ↔ (w=j.val ∨ w=N+y.val)) : M i x=M j y := by
    apply det _ _ (by simp [oneEach]) (by simp [oneEach]) _ _ (Finset.mem_singleton_self _)
    intro w hw
    exact Bool.eq_iff_iff.mpr (by simpa only [hotPin] using pins w hw)
  have rr := zeroes T M seenR (fun i j ne => (sep i j ne).1) (by
    intro i oi j oj; funext x
    apply same
    simp only [seenR,Finset.mem_filter,Finset.mem_univ,true_and] at oi oj
    intro w hw; have hi : w≠i.val := fun h => oi (h ▸ hw); have hj : w≠j.val := fun h => oj (h ▸ hw)
    simp [hi,hj])
  have cc := zeroes (Function.swap T) (Function.swap M) seenC (fun i j ne => (sep i j ne).2) (by
    intro i oi j oj; funext x
    apply same
    simp only [seenC,Finset.mem_filter,Finset.mem_univ,true_and] at oi oj
    intro w hw; have hi : w≠N+i.val := fun h => oi (h ▸ hw); have hj : w≠N+j.val := fun h => oj (h ▸ hw)
    simp [hi,hj])
  rw [error_transpose] at cc
  omega

end Private25855

namespace Private25855
open Finset
variable {N : ℕ}
abbrev Idx (N : ℕ) := Fin N
abbrev Table (N : ℕ) := Finset (Idx N) → Finset (Idx N) → Bool

inductive Piece (N : ℕ)
  | row (i : Fin N)
  | col (j : Fin N)
  | port
  | const (b : Bool)
  | gate (op : Bool → Bool → Bool) (l r : Piece N)

namespace Piece
def rows : Piece N → Finset (Fin N)
  | .row i => {i}
  | .gate _ l r => rows l ∪ rows r
  | _ => ∅
def cols : Piece N → Finset (Fin N)
  | .col j => {j}
  | .gate _ l r => cols l ∪ cols r
  | _ => ∅
def eval (X Y : Finset (Fin N)) (b : Bool) : Piece N → Bool
  | .row i => decide (i∈X)
  | .col j => decide (j∈Y)
  | .port => b
  | .const c => c
  | .gate op l r => op (eval X Y b l) (eval X Y b r)

def Factor (F : Table N) (t : Piece N) := ∀ X Y U V : Finset (Fin N),
    X \ t.rows = U \ t.rows → Y \ t.cols = V \ t.cols →
    (∀ b, eval X Y b t=eval U V b t) → F X Y=F U V

def Regular (F : Table N) : Piece N → Prop
  | t@(.gate _ l r) => Factor F t ∧ Regular F l ∧ Regular F r
  | t => Factor F t

theorem rootFactor {F : Table N} {t : Piece N} (h : Regular F t) : Factor F t := by
  cases t <;> first | exact h | exact h.1

theorem congr_eval {X Y U V : Finset (Fin N)} (t : Piece N)
    (hx : ∀ i∈t.rows, i∈X ↔ i∈U) (hy : ∀ i∈t.cols, i∈Y ↔ i∈V) (b : Bool) :
    eval X Y b t=eval U V b t := by
  induction t with
  | row i => simp only [eval,decide_eq_decide]; exact hx i (by simp [rows])
  | col i => simp only [eval,decide_eq_decide]; exact hy i (by simp [cols])
  | port | const => rfl
  | gate o l r il ir =>
    simp only [eval]
    rw [il (fun _ h => hx _ (Finset.mem_union_left _ h)) (fun _ h => hy _ (Finset.mem_union_left _ h)),
      ir (fun _ h => hx _ (Finset.mem_union_right _ h)) (fun _ h => hy _ (Finset.mem_union_right _ h))]

def respR (t : Piece N) (i : Fin N) := fun b => eval {i} ∅ b t
def respC (t : Piece N) (j : Fin N) := fun b => eval ∅ {j} b t
def base (t : Piece N) := fun b => eval ∅ ∅ b t

theorem rowOutside (t : Piece N) {i j : Fin N} (out : j∉t.cols) (b : Bool) :
    eval {i} {j} b t=respR t i b :=
  congr_eval t (by simp) (by intro w hw; simp; exact fun e => out (e ▸ hw)) b

theorem colOutside (t : Piece N) {i j : Fin N} (out : i∉t.rows) (b : Bool) :
    eval {i} {j} b t=respC t j b :=
  congr_eval t (by intro w hw; simp; exact fun e => out (e ▸ hw)) (by simp) b

def One (F : Table N) := fun (i j : Fin N) => F {i} {j}

theorem injectR (F : Table N) (t : Piece N) (factor : Factor F t)
    (sc : t.cols.card<17) (sep : ∀ i∈t.rows, ∀ j∈t.rows, i≠j → 17≤distance (One F i) (One F j)) :
    Set.InjOn (respR t) (↑t.rows) := by
  apply response_injective (One F) t.rows t.cols (respR t) 17 sc sep
  intro i hi j hj h c hc
  apply factor {i} {c} {j} {c} (by ext w; simp; grind) rfl
  intro b; rw [rowOutside _ hc, rowOutside _ hc, h]

theorem injectC (F : Table N) (t : Piece N) (factor : Factor F t)
    (sc : t.rows.card<17) (sep : ∀ i∈t.cols, ∀ j∈t.cols, i≠j →
      17≤distance (Function.swap (One F) i) (Function.swap (One F) j)) :
    Set.InjOn (respC t) (↑t.cols) := by
  apply response_injective (Function.swap (One F)) t.cols t.rows (respC t) 17 sc sep
  intro i hi j hj h c hc
  apply factor {c} {i} {c} {j} rfl (by ext w; simp; grind)
  intro b; rw [colOutside _ hc, colOutside _ hc, h]


theorem width (F : Table N) (t : Piece N) (reg : Regular F t)
    (sr : ∀ i∈t.rows, ∀ j∈t.rows, i≠j → 17≤distance (One F i) (One F j))
    (sc : ∀ i∈t.cols, ∀ j∈t.cols, i≠j → 17≤distance (Function.swap (One F) i) (Function.swap (One F) j)) :
    t.rows.card≤4 ∧ t.cols.card≤4 := by
  induction t with
  | row | col | port | const => simp [rows,cols]
  | gate op l r il ir =>
    let t := Piece.gate op l r
    obtain ⟨lr,lc⟩ := il reg.2.1
      (fun i hi j hj => sr i (Finset.mem_union_left _ hi) j (Finset.mem_union_left _ hj))
      (fun i hi j hj => sc i (Finset.mem_union_left _ hi) j (Finset.mem_union_left _ hj))
    obtain ⟨rr,rc⟩ := ir reg.2.2
      (fun i hi j hj => sr i (Finset.mem_union_right _ hi) j (Finset.mem_union_right _ hj))
      (fun i hi j hj => sc i (Finset.mem_union_right _ hi) j (Finset.mem_union_right _ hj))
    have rowBound : t.rows.card<17 := by
      change (l.rows ∪ r.rows).card < 17
      have := Finset.card_union_le l.rows r.rows
      omega
    have colBound : t.cols.card<17 := by
      change (l.cols ∪ r.cols).card < 17
      have := Finset.card_union_le l.cols r.cols
      omega
    have injR := injectR F t reg.1 colBound sr
    have injC := injectC F t reg.1 rowBound sc
    change t.rows.card ≤ 4 ∧ t.cols.card ≤ 4
    rw [←Finset.card_image_of_injOn injR, ←Finset.card_image_of_injOn injC]
    exact ⟨(Finset.card_le_univ _).trans (by decide),(Finset.card_le_univ _).trans (by decide)⟩

end Piece
end Private25855

namespace Private25855.Piece
open Finset
variable {N m : ℕ}

theorem rowInvisible {F : Table N} {t : Piece N} (fac : Factor F t) {i : Fin N}
    (hi : i∈t.rows) (invisible : respR t i=base t) :
    distance (One F i) (fun j => F ∅ {j}) ≤ t.cols.card := by
  apply Finset.card_le_card
  intro j hj
  by_contra away
  apply (Finset.mem_filter.mp hj).2
  refine fac {i} {j} ∅ {j} (by ext w; simp; grind) rfl fun b => ?_
  rw [rowOutside t away,invisible]
  exact congr_eval t (by simp) (by intro w hw; simp; exact fun e => away (e ▸ hw)) b

theorem colInvisible {F : Table N} {t : Piece N} (fac : Factor F t) {i : Fin N}
    (hi : i∈t.cols) (invisible : respC t i=base t) :
    distance (Function.swap (One F) i) (fun j => F {j} ∅) ≤ t.rows.card := by
  apply Finset.card_le_card
  intro j hj
  by_contra away
  apply (Finset.mem_filter.mp hj).2
  refine fac {j} {i} {j} ∅ rfl (by ext w; simp; grind) fun b => ?_
  rw [colOutside t away,invisible]
  exact congr_eval t (by intro w hw; simp; exact fun e => away (e ▸ hw)) (by simp) b

theorem cross {F : Table N} {a b : Piece N} (fa : Factor F a) (fb : Factor F b)
    {i j k l : Fin N} (ia : i∈a.rows) (ja : j∈a.cols)
    (kb : k∈b.rows) (lb : l∈b.cols)
    (dr : Disjoint a.rows b.rows) (dc : Disjoint a.cols b.cols)
    (ha : respR a i=respC a j) (hb : respR b k=respC b l) : One F i l=One F k j := by
  have il : i∉b.rows := fun h => Finset.disjoint_left.mp dr ia h
  have kl : k∉a.rows := fun h => Finset.disjoint_left.mp dr h kb
  have jl : j∉b.cols := fun h => Finset.disjoint_left.mp dc ja h
  have ll : l∉a.cols := fun h => Finset.disjoint_left.mp dc h lb
  have ne : j≠l := fun e => jl (e ▸ lb)
  have first : F {i} {l}=F ∅ {j,l} := by
    apply fa
    · ext w; simp; grind
    · ext w; simp; grind
    · intro bit
      rw [rowOutside a ll,ha]
      apply congr_eval a (by simp)
      intro w hw; simp; grind
  apply first.trans
  apply fb
  · ext w; simp; grind
  · ext w; simp; grind
  · intro bit
    rw [rowOutside b jl, hb]
    apply congr_eval b (by simp)
    intro w hw; simp; grind

def members (sets : Fin m → Finset (Fin N)) :=
    univ.filter fun z : Fin m × Fin N => z.2 ∈ sets z.1

theorem member_snd {sets : Fin m → Finset (Fin N)}
    (sep : ∀ i j, i≠j → Disjoint (sets i) (sets j)) : Set.InjOn (Prod.snd : Fin m × Fin N → Fin N) (↑(members sets)) := by
  intro a ha b hb h
  apply Prod.ext _ h
  by_contra ne
  have := (Finset.mem_filter.mp ha).2
  have := (Finset.mem_filter.mp hb).2
  exact (Finset.disjoint_left.mp (sep _ _ ne)) ‹a.2∈sets a.1› (h ▸ ‹b.2∈sets b.1›)

theorem member_cover (sets : Fin m → Finset (Fin N)) :
    (univ.biUnion sets).card ≤ (members sets).card := by
  have eq : (members sets).image Prod.snd = univ.biUnion sets := by
    ext i; simp [members]
  rw [←eq]
  exact Finset.card_image_le

theorem remove_invisible {A : Finset (Fin m × Fin N)} (code : Fin m × Fin N → Bool → Bool)
    (baseline : Fin m → Bool → Bool) (sndI : Set.InjOn (Prod.snd : Fin m × Fin N → Fin N) (↑A))
    (M : Fin N → Fin N → Bool) (null : Fin N → Bool)
    (bound : ∀ z∈A, code z=baseline z.1 → distance (M z.2) null ≤ 4)
    (sep : ∀ z∈A, ∀ w∈A, z.2≠w.2 → 17≤distance (M z.2) (M w.2)) :
    A.card ≤ (A.filter fun z => code z≠baseline z.1).card+1 := by
  classical
  have small : (A.filter fun z => code z=baseline z.1).card≤1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hx,vx⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy,vy⟩ := Finset.mem_filter.mp hy
    apply sndI hx hy
    by_contra ne
    have d := distance_triangle (M x.2) null (M y.2)
    rw [distance_comm null (M y.2)] at d
    have := bound x hx vx
    have := bound y hy vy
    have := sep x hx y hy ne
    omega
  have h := Finset.card_filter_add_card_filter_not (s:=A) (fun z => code z=baseline z.1)
  change (A.filter fun z => code z=baseline z.1).card+(A.filter fun z => code z≠baseline z.1).card=A.card at h
  omega

end Private25855.Piece

namespace Private25855.Piece
open Finset
variable {N m : ℕ}

def slots (pure : Fin m → Bool) (baseline : Fin m → Bool → Bool) :=
  univ.filter fun z : Fin m × (Bool → Bool) => z.2≠baseline z.1 ∧
    (pure z.1=true → z.2 false=z.2 true)

theorem slot_count (pure : Fin m → Bool) (baseline : Fin m → Bool → Bool)
    (baseFlat : ∀ i, pure i=true → baseline i false=baseline i true) :
    (slots pure baseline).card ≤ (univ.filter fun i => pure i=true).card +
      3*(univ.filter fun i => pure i=false).card := by
  classical
  have count : ∀ (p : Bool) (a : Bool → Bool), (p=true → a false=a true) →
      (univ.filter fun h : Bool→Bool => h≠a ∧ (p=true → h false=h true)).card ≤
      (if p=true then 1 else 0) + 3*(if p=false then 1 else 0) := by decide
  simp only [slots,Finset.card_filter,Fintype.sum_prod_type,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [Finset.card_filter] using count (pure i) (baseline i) (baseFlat i)

theorem matching {b H K : ℕ} (F : Table N) (t : Fin m → Piece N) (pure : Fin m → Bool)
    (reg : ∀ z, Regular F (t z))
    (dr : ∀ z w, z≠w → Disjoint (t z).rows (t w).rows)
    (dc : ∀ z w, z≠w → Disjoint (t z).cols (t w).cols)
    (flat : ∀ z, pure z=true → ∀ X Y, eval X Y false (t z)=eval X Y true (t z))
    (sr : ∀ z w i, i∈(t z).rows → ∀ j∈(t w).rows, i≠j → 17≤distance (One F i) (One F j))
    (sc : ∀ z w i, i∈(t z).cols → ∀ j∈(t w).cols, i≠j → 17≤distance (Function.swap (One F) i) (Function.swap (One F) j))
    (scarcity : K+2*N≤b+3+2*H)
    (coverage : 2*N ≤ (univ.biUnion fun z => (t z).rows).card + (univ.biUnion fun z => (t z).cols).card+K+2*H+2)
    (cost : (univ.filter fun i => pure i=true).card+3*(univ.filter fun i => pure i=false).card≤14*K+1+12*H) :
    ∃ p, ∃ x y : Fin p → Fin N, Function.Injective x ∧ Function.Injective y ∧
      32*N≤p+15*b+50+44*H ∧
      ∃ owner : Fin p → Fin m, (∀ i, (univ.filter fun j => owner j=owner i).card≤3) ∧
      (∀ i j, owner i≠owner j → One F (x i) (y j) = One F (x j) (y i)) := by
  classical
  let R := members fun i => (t i).rows
  let C := members fun i => (t i).cols
  let baseF := fun i => base (t i)
  let r := fun z : Fin m × Fin N => respR (t z.1) z.2
  let c := fun z : Fin m × Fin N => respC (t z.1) z.2
  let X := R.filter fun z => r z≠baseF z.1
  let Y := C.filter fun z => c z≠baseF z.1
  let kr := fun z : Fin m × Fin N => (z.1,r z)
  let kc := fun z : Fin m × Fin N => (z.1,c z)
  have wr (i) := width F (t i) (reg i) (sr i i) (sc i i)
  have xr {z} (h : z∈X) : z.2∈(t z.1).rows := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
  have yc {z} (h : z∈Y) : z.2∈(t z.1).cols := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
  have ri (z) := injectR F (t z) (rootFactor (reg z)) (by have := (wr z).2; omega) (sr z z)
  have ci (z) := injectC F (t z) (rootFactor (reg z)) (by have := (wr z).1; omega) (sc z z)
  have krInj : Set.InjOn kr (↑X) := by
    rintro ⟨i,a⟩ ha ⟨j,b⟩ hb eq
    have e : i=j := congrArg Prod.fst eq; subst j
    exact Prod.ext rfl (ri i (xr ha) (xr hb) (congrArg Prod.snd eq))
  have kcInj : Set.InjOn kc (↑Y) := by
    rintro ⟨i,a⟩ ha ⟨j,b⟩ hb eq
    have e : i=j := congrArg Prod.fst eq; subst j
    exact Prod.ext rfl (ci i (yc ha) (yc hb) (congrArg Prod.snd eq))
  have insideR : X.image kr ⊆ slots pure baseF := by
    rintro _ h; obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_filter.mpr ⟨by simp,(Finset.mem_filter.mp hz).2,fun hp => flat z.1 hp _ _⟩
  have insideC : Y.image kc ⊆ slots pure baseF := by
    rintro _ h; obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_filter.mpr ⟨by simp,(Finset.mem_filter.mp hz).2,fun hp => flat z.1 hp _ _⟩
  obtain ⟨p,x,y,hx,hy,mem,codes⟩ := common_private X Y kr kc _ krInj kcInj insideR insideC
  have sndR := member_snd dr
  have sndC := member_snd dc
  have rx (i) := (mem i).1
  have cy (i) := (mem i).2.1
  have eq (i) := (mem i).2.2
  have align (i) : (x i).1=(y i).1 := congrArg (Prod.fst : Fin m × (Bool→Bool) → Fin m) (eq i)
  have yown (i) : (y i).2∈(t (x i).1).cols := align i ▸ yc (cy i)
  have same (i) : respR (t (x i).1) (x i).2=respC (t (x i).1) (y i).2 := by
    have ee := congrArg (Prod.snd : Fin m × (Bool→Bool) → (Bool→Bool)) (eq i)
    change respR (t (x i).1) (x i).2=respC (t (y i).1) (y i).2 at ee
    rwa [←align i] at ee
  refine ⟨p,fun i => (x i).2,fun i => (y i).2,?_,?_,?_,?_⟩
  · intro i j h; exact hx (sndR (Finset.mem_filter.mp (rx i)).1 (Finset.mem_filter.mp (rx j)).1 h)
  · intro i j h; exact hy (sndC (Finset.mem_filter.mp (cy i)).1 (Finset.mem_filter.mp (cy j)).1 h)
  · have capR := remove_invisible (A:=R) r baseF sndR (One F) (fun j => F ∅ {j})
      (fun z hz e => (rowInvisible (rootFactor (reg z.1)) (Finset.mem_filter.mp hz).2 e).trans (wr z.1).2)
      (fun z hz w hw => sr z.1 w.1 z.2 (Finset.mem_filter.mp hz).2 w.2 (Finset.mem_filter.mp hw).2)
    have capC := remove_invisible (A:=C) c baseF sndC (Function.swap (One F)) (fun j => F {j} ∅)
      (fun z hz e => (colInvisible (rootFactor (reg z.1)) (Finset.mem_filter.mp hz).2 e).trans (wr z.1).1)
      (fun z hz w hw => sc z.1 w.1 z.2 (Finset.mem_filter.mp hz).2 w.2 (Finset.mem_filter.mp hw).2)
    change R.card≤X.card+1 at capR
    change C.card≤Y.card+1 at capC
    have rcover : _ ≤ R.card := member_cover fun i => (t i).rows
    have ccover : _ ≤ C.card := member_cover fun i => (t i).cols
    have capSlots := slot_count pure baseF (fun i hi => flat i hi ∅ ∅)
    omega
  · refine ⟨fun i => (x i).1,?_,?_⟩
    · intro i
      let S := univ.filter fun j => (x j).1=(x i).1
      let B := (univ : Finset (Bool→Bool)).erase (baseF (x i).1)
      have image : (S.image fun j => r (x j)) ⊆ B := by
        rintro h hh; obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hh
        exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2 ▸ (Finset.mem_filter.mp (rx j)).2,by simp⟩
      have inj : Set.InjOn (fun j => r (x j)) (↑S) := by
        intro j hj k hk e
        exact hx (krInj (rx j) (rx k) (Prod.ext ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hk).2.symm) e))
      have capB : B.card=3 := by
        rw [show B=univ.erase (baseF (x i).1) from rfl,Finset.card_erase_of_mem (Finset.mem_univ _)]
        decide
      change S.card ≤ 3
      rw [←Finset.card_image_of_injOn inj,←capB]
      exact Finset.card_le_card image
    · intro i j ne
      exact cross (rootFactor (reg _)) (rootFactor (reg _)) (xr (rx i)) (yown i)
        (xr (rx j)) (yown j) (dr _ _ ne) (dc _ _ ne) (same i) (same j)

end Private25855.Piece

namespace Private25855.Piece
open Finset
variable {N : ℕ}


def Linear : Piece N → Prop
  | .gate _ l r => Disjoint l.rows r.rows ∧ Disjoint l.cols r.cols ∧ Linear l ∧ Linear r
  | _ => True

theorem hereditary {F : Table N} {t : Piece N} (h : Factor F t) (lin : Linear t) : Regular F t := by
  induction t with
  | row | col | port | const => exact h
  | gate op l r il ir =>
    obtain ⟨dr,dc,lok,rok⟩ := lin
    have eqAway {X U A B : Finset (Fin N)} (eq : X\A=U\A) :
        X\(A∪B)=U\(A∪B) := by
      ext w
      have point : w∈X\A ↔ w∈U\A := eq ▸ Iff.rfl
      simp at point ⊢
      tauto
    have others {X U A B : Finset (Fin N)} (eq : X\A=U\A) (dis : Disjoint A B) :
        ∀ w∈B, w∈X ↔ w∈U := by
      intro w hw
      have out : w∉A := fun ha => Finset.disjoint_left.mp dis ha hw
      have point : w∈X\A ↔ w∈U\A := eq ▸ Iff.rfl
      simpa [out] using point
    refine ⟨h,il (fun X Y U V hr hc valEq => ?_) lok,ir (fun X Y U V hr hc valEq => ?_) rok⟩
    · apply h _ _ _ _ (eqAway hr) (eqAway hc)
      intro b
      simp only [eval,valEq b,congr_eval r (others hr dr) (others hc dc) b]
    · apply h _ _ _ _ (by simpa only [rows,Finset.union_comm] using eqAway (B:=l.rows) hr)
          (by simpa only [cols,Finset.union_comm] using eqAway (B:=l.cols) hc)
      intro b
      simp only [eval,valEq b,congr_eval l (others hr dr.symm) (others hc dc.symm) b]

end Private25855.Piece


namespace CutLib25855.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_init (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_init [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_init gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_init gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false
theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_init _ _ _ _ (h t rfl)

theorem gv (N : ℕ) (C : Circuit) (hb : ReadsBack N C) (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) :
    (run C.gates x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  have hw := run_gate C.gates x j hj
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [hx, ← he] at hw
  rw [hw]
  congr 1
  exact List.map_congr_left fun i hi => if_pos (hb j hj i hi)

theorem past (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (run gs x).getD i false = false :=
  List.getD_eq_default _ _ (by rw [run_length]; exact hi)

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn]
    simp [h, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp [h2, Fin.ext_iff]
      have hu : ¬ i = u.val := by omega
      by_cases hv : i = n + v.val
      · simp [hv]
      · have hv' : ¬ i - n = v.val := by omega
        simp [hu, hv, hv']
    · simp [h2]
      omega

theorem sa_val {n : ℕ} (u : Fin (n + 1)) (a : Fin n) :
    ((u.succAbove a : Fin (n + 1)) : ℕ) = if (a : ℕ) < u then (a : ℕ) else a + 1 := by
  by_cases h : (a : ℕ) < u
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]; simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; simp [h]

def reads (g : Gate) (w : ℕ) : Prop :=
  (g.op = .not ∧ g.inputs.head? = some w) ∨ (g.op ≠ .not ∧ w ∈ g.inputs)

def Good (P : Prop) (g : Gate) : Prop :=
  ((g.op = .not ∧ ∃ a, g.inputs = [a]) ∨
    ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a ≠ b ∧ g.inputs = [a,b])) ∧
    (P → g.op = .and ∨ g.op = .or)

theorem good_shape {P : Prop} {g : Gate} (h : Good P g) :
    (g.op = .not → g.inputs.length = 1) ∧
    (g.op ≠ .not → g.inputs.length = 2 ∧ g.inputs.Nodup) := by
  rcases h.1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,hn,ha⟩
  · simp [ho,ha]
  · rcases ho with ho|ho <;> simp [ho,ha,hn]

theorem good_fan {P : Prop} {C : Circuit} (h : ∀ g ∈ C.gates, Good P g) : FanInTwo C := by
  intro g hg
  rcases (h g hg).1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,_,ha⟩
  · simp [ho,ha]
  · rcases ho with ho|ho <;> simp [ho,ha]

theorem good_mono {P : Prop} {C : Circuit} (h : ∀ g ∈ C.gates, Good P g) :
    P → Monotone2 C := by
  intro p g hg
  exact ⟨by simpa using (h g hg).2 p,(good_fan h g hg).2⟩

theorem good_read {P : Prop} {g : Gate} (h : Good P g) (w : ℕ) : reads g w ↔ w ∈ g.inputs := by
  rcases h.1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,_,ha⟩
  · simp [reads,ho,ha,eq_comm]
  · rcases ho with ho|ho <;> simp [reads,ho]

end CutLib25855.Normalize

namespace CutLib25855.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem emit (P : Prop) (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hmon : P → op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
      (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, Good P g → (∀ t ∈ g.inputs, t < N + hs.length) →
      (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h1' h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, by simpa using h1', ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  by_cases hn : op = GateOp.not
  · subst op
    rcases rs with _ | ⟨r, rs⟩
    · exact keep (.inl true) (by simp) (by intro y hy; rfl)
    · have hr := hv r (by simp)
      rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y hy; rfl)
      · exact add ⟨.not,[t]⟩ ⟨Or.inl ⟨rfl,t,rfl⟩,hmon⟩ (by simpa using hr t rfl)
          (by intro y hy; rfl)
  have hop' : op = GateOp.and ∨ op = GateOp.or := by tauto
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop' with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop' with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop' with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.and,[t,q]⟩ ⟨Or.inr ⟨Or.inl rfl,t,q,same,rfl⟩,fun _ => Or.inl rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.or,[t,q]⟩ ⟨Or.inr ⟨Or.inr rfl,t,q,same,rfl⟩,fun _ => Or.inr rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
  · simp at hl

theorem engine {X : Type} (P : Prop) (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : FanInTwo C) (hmon : P → Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size + F.card ≤ C.size ∧
      ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h5, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, Good P g) → (∀ g ∈ e, ∀ t ∈ g.inputs, t < M + hs.length) →
          (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he he' hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · intro i hi t ht
          rw [List.getElem_append] at ht
          split_ifs at ht with hih
          · exact h5 i hih t ht
          · have hmem : e[i - hs.length]'(by simp at hi; omega) ∈ e := List.mem_iff_getElem.mpr ⟨_, _, rfl⟩
            have := he' _ hmem t ht
            omega
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e2', e3, e4⟩ := emit P M hs C.gates[k].op hop (fun p => by simpa using (hmon p _ (List.getElem_mem hk')).1) (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e2' e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h5, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, ?_, h2, fun x => ?_⟩
    · exact h1
    · intro j hj i hi
      have hj' : j < hs.length := hj
      have he : gateAt ⟨hs, t⟩ j = hs[j] := List.getD_eq_getElem _ _ hj'
      rw [he] at hi
      exact h5 j hj' i hi
    · have := hev x
      rw [hm] at this
      exact this.symm

end CutLib25855.Normalize

namespace CutLib25855.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def collapses {X : Type} (W : X → ℕ → Bool) (top : ℕ) (out : X → Bool) : Prop :=
  (∃ b, ∀ x, out x = b) ∨ ∃ w < top, ∀ x, out x = W x w

theorem read_pair (l : List ℕ) (w : ℕ) (hlen : l.length ≤ 2) (hw : w ∈ l) :
    l = [w] ∨ ∃ v, l = [w,v] ∨ l = [v,w] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d,tail⟩⟩⟩
  · simp at hw
  · have e : w=a := by simpa using hw
    exact Or.inl (by rw [e])
  · rcases List.mem_cons.mp hw with e | h
    · exact Or.inr ⟨b,Or.inl (by rw [e])⟩
    · have e : w=b := by simpa using h
      exact Or.inr ⟨a,Or.inr (by rw [e])⟩
  · simp at hlen

theorem not_value {X : Type} (W : X → ℕ → Bool) (g : Gate) {w : ℕ} {b : Bool}
    (op : g.op = .not) (r : reads g w) (fixed : ∀ x, W x w = b) (x : X) :
    g.op.eval (g.inputs.map (W x)) = !b := by
  have he : g.inputs.head? = some w := by simpa [reads,op] using r
  cases h : g.inputs with
  | nil => simp [h] at he
  | cons a tail =>
    have e : a=w := by simpa [h] using he
    simp [op,h,GateOp.eval,e,fixed]

theorem dominant {X : Type} (W : X → ℕ → Bool) (g : Gate) (w : ℕ)
    (hlen : g.inputs.length ≤ 2) (r : reads g w) (op : g.op = .and ∨ g.op = .not)
    (fixed : ∀ x, W x w = false) :
    ∃ b, ∀ x, g.op.eval (g.inputs.map (W x)) = b := by
  rcases op with h|h
  · have mem : w ∈ g.inputs := by simpa [reads,h] using r
    refine ⟨false,fun x => ?_⟩
    rcases read_pair _ w hlen mem with e | ⟨v,e|e⟩ <;> simp [h,e,GateOp.eval,fixed]
  · exact ⟨true,not_value W g h r fixed⟩

theorem when_read {X : Type} (W : X → ℕ → Bool) (g : Gate) (top w : ℕ) (b : Bool)
    (ok : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (before : ∀ t ∈ g.inputs, t < top) (r : reads g w) (fixed : ∀ x, W x w = b) :
    collapses W top (fun x => g.op.eval (g.inputs.map (W x))) := by
  by_cases hn : g.op = .not
  · exact Or.inl ⟨!b,not_value W g hn r fixed⟩
  have hop : g.op = .and ∨ g.op = .or := by tauto
  have mem : w ∈ g.inputs := by simpa [reads,hn] using r
  rcases read_pair _ w hlen mem with e | ⟨v,e⟩
  · refine Or.inl ⟨b,fun x => ?_⟩
    rcases hop with ho|ho <;> simp [ho,e,GateOp.eval,fixed]
  · have hv : v < top := before v (by rcases e with h|h <;> simp [h])
    rcases hop with h|h
    · cases b
      · refine Or.inl ⟨false,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
    · cases b
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inl ⟨true,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]

def toNat {s : ℕ} (K : Finset (Fin s)) : Finset ℕ := K.map ⟨Fin.val,Fin.val_injective⟩

theorem marked {X : Type} (N : ℕ) (C : Circuit) (src : X → List Bool)
    (hs : ∀ x, (src x).length=N) (u : ℕ) (hu : u<N) (hu0 : ∀ x, (src x).getD u false=false)
    (fan : FanInTwo C) (back : ReadsBack N C) (K : Finset (Fin C.gates.length))
    (mark : ∀ j ∈ K, reads (C.gates.get j) u ∨ ∃ i : Fin C.gates.length, i<j ∧
      reads (C.gates.get i) u ∧ ((C.gates.get i).op=.and ∨ (C.gates.get i).op=.not) ∧
      reads (C.gates.get j) (N+i.val)) :
    ∀ k ∈ toNat K, k < C.gates.length ∧
      collapses (fun x w => (run C.gates (src x)).getD w false) (N+k)
        (fun x => (run C.gates (src x)).getD (N+k) false) := by
  let W := fun (x : X) (w : ℕ) => (run C.gates (src x)).getD w false
  have raw (x : X) : W x u = false :=
    (run_input _ _ _ (by rw [hs]; exact hu)).trans (hu0 x)
  have atGate (j : Fin C.gates.length) : gateAt C j.val=C.gates.get j :=
    List.getD_eq_getElem _ _ j.isLt
  have ev (j : Fin C.gates.length) (x : X) :
      W x (N+j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (W x)) := by
    simpa only [W,atGate j] using gv N C back (src x) (hs x) j.val j.isLt
  intro k hk
  obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hk
  refine ⟨j.isLt,?_⟩
  change collapses W (N+j.val) (fun x => W x (N+j.val))
  have same := funext (ev j)
  rw [same]
  have ok := fan (C.gates.get j) (List.get_mem _ _)
  have before (t : ℕ) (ht : t∈(C.gates.get j).inputs) : t<N+j.val :=
    back j.val j.isLt t (by rwa [atGate])
  have folded (w : ℕ) (b : Bool) (r : reads (C.gates.get j) w) (h : ∀ x, W x w=b) :=
    when_read W _ (N+j.val) w b (by simpa using ok.1) ok.2 before r h
  rcases mark j hj with direct | ⟨i,_,ri,oi,rj⟩
  · exact folded u false direct raw
  · have fi := fan (C.gates.get i) (List.get_mem _ _)
    obtain ⟨b,hb⟩ := dominant W _ u fi.2 ri oi raw
    exact folded (N+i.val) b rj (fun x => (ev i x).trans (hb x))

end CutLib25855.Normalize

namespace CutLib25855.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def oldFace {n m : ℕ} (u : Fin (n+1)) (x : List Bool) : Option (Fin n × Fin m) → List Bool
  | none => x
  | some p => oneEach (u.succAbove p.1) p.2

def newFace {n m : ℕ} (u : Fin (n+1)) (x : List Bool) : Option (Fin n × Fin m) → List Bool
  | none => List.ofFn (fun j : Fin (n+m) => x.getD (if j.val<u.val then j.val else j.val+1) false)
  | some p => oneEach p.1 p.2

theorem old_len {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.length=n+1+m)
    (p : Option (Fin n × Fin m)) : (oldFace u x p).length=n+1+m := by
  cases p <;> simp [oldFace,oneEach_length,hx]

theorem new_len {n m : ℕ} (u : Fin (n+1)) (x : List Bool)
    (p : Option (Fin n × Fin m)) : (newFace u x p).length=n+m := by
  cases p <;> simp [newFace,oneEach_length]

theorem off_face {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.getD u.val false=false)
    (p : Option (Fin n × Fin m)) : (oldFace u x p).getD u.val false=false := by
  cases p with
  | none => exact hx
  | some p =>
    simp only [oldFace,oneEach_getD,decide_eq_false_iff_not,sa_val]
    have := u.isLt
    split_ifs <;> omega

theorem face_inputs {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.getD u.val false=false)
    (w : ℕ) (hw : w<n+1+m) :
    (∃ b, ∀ p : Option (Fin n × Fin m), (oldFace u x p).getD w false = b) ∨
    ∃ t, t<n+m ∧ ∀ p : Option (Fin n × Fin m), (oldFace u x p).getD w false =
      (newFace u x p).getD t false := by
  have hu := u.isLt
  rcases lt_trichotomy w u.val with h | h | h
  · have ht : w<n+m := by omega
    refine Or.inr ⟨w,ht,?_⟩
    intro p
    cases p with
    | none => simp [oldFace,newFace,ht,h]
    | some p =>
      have := p.1.isLt
      have := p.2.isLt
      simp only [oldFace,newFace,oneEach_getD,decide_eq_decide,sa_val]
      split_ifs <;> omega
  · subst w
    exact Or.inl ⟨false,off_face u x hx⟩
  · have ht : w-1<n+m := by omega
    have hn : ¬ w-1<u.val := by omega
    have eq : w-1+1=w := by omega
    refine Or.inr ⟨w-1,ht,?_⟩
    intro p
    cases p with
    | none => simp [oldFace,newFace,ht,hn,eq]
    | some p =>
      have := p.1.isLt
      have := p.2.isLt
      simp only [oldFace,newFace,oneEach_getD,decide_eq_decide,sa_val]
      split_ifs <;> omega

end CutLib25855.Normalize

namespace CutLib25855.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem blank_dead_signed (P : Prop) (N : ℕ) (C : Circuit)
    (hc : FanInTwo C) (hm : P → Monotone2 C) (hb : ReadsBack N C)
    (j : ℕ) (hj : j < C.gates.length)
    (hdead : ∀ k < C.gates.length, N + j ∉ (gateAt C k).inputs) (ho : C.output ≠ N + j) :
    let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
    FanInTwo E ∧ (P → Monotone2 E) ∧ ReadsBack N E ∧ E.size = C.size ∧
      (∀ x : List Bool, x.length = N → E.eval x = C.eval x) ∧
      (∀ x : List Bool, x.length = N → (run E.gates x).getD (N + j) false = false) := by
  let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
  have hlen : E.gates.length = C.gates.length := by simp [E]
  have hg : ∀ k, gateAt E k = if k = j then ⟨GateOp.or, []⟩ else gateAt C k := by
    intro k
    simp only [gateAt, E, List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hk : k = j
    · subst hk; simp [hj]
    · simp [hk, Ne.symm hk]
  have hc' : FanInTwo E := by
    intro g h
    rcases List.mem_or_eq_of_mem_set h with h | h
    · exact hc g h
    · subst h; simp
  have hm' : P → Monotone2 E := by
    intro hP g h
    rcases List.mem_or_eq_of_mem_set h with h | h
    · exact hm hP g h
    · subst h; simp
  have hb' : ReadsBack N E := by
    intro k hk i hi
    rw [hg] at hi
    split_ifs at hi with h
    · simp at hi
    · exact hb k (by rw [hlen] at hk; exact hk) i hi
  have agree : ∀ x : List Bool, x.length = N → ∀ i, i ≠ N + j →
      (run E.gates x).getD i false = (run C.gates x).getD i false := by
    intro x hx i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hlo : i < N
      · rw [run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
      by_cases hhi : N + C.gates.length ≤ i
      · rw [past _ _ _ (by rw [hlen]; omega), past _ _ _ (by omega)]
      have hk : i - N < C.gates.length := by omega
      have hik : i = N + (i - N) := by omega
      rw [hik, gv N E hb' x hx _ (by rw [hlen]; exact hk), gv N C hb x hx _ hk, hg,
        if_neg (by omega)]
      congr 1
      refine List.map_congr_left fun i' hi' => ih i' ?_ ?_
      · have := hb _ hk i' hi'; omega
      · rintro rfl; exact hdead _ hk hi'
  refine ⟨hc', hm', hb', hlen, fun x hx => agree x hx _ ho, fun x hx => ?_⟩
  change (run E.gates x).getD (N + j) false = false
  rw [gv N E hb' x hx j (by rw [hlen]; exact hj), hg, if_pos rfl]
  simp [GateOp.eval]

theorem finish_live {X : Type} (P : Prop) (M : ℕ) (y : X → List Bool)
    (hy : ∀ x, (y x).length = M) (f : X → Bool)
    (hnc : ¬ ∃ b : Bool, ∀ x, f x = b) (C : Circuit)
    (hg : ∀ g ∈ C.gates, Good P g) (hb : ReadsBack M C) (hf : ∀ x, C.eval (y x) = f x) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size ≤ C.size ∧
      (∀ x, D.eval (y x) = f x) ∧
      ∀ i : Fin D.gates.length, M + i.val ≠ D.output →
        ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (M + i.val) := by
  classical
  have hex : ∃ k, ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧
      D.size ≤ k ∧ ∀ x, D.eval (y x) = f x := ⟨C.size, C, hg, hb, le_rfl, hf⟩
  obtain ⟨D, hgood, hback, hsize, hval⟩ := Nat.find_spec hex
  have hmin0 : Nat.find hex ≤ C.size := Nat.find_min' hex ⟨C, hg, hb, le_rfl, hf⟩
  refine ⟨D, hgood, hback, hsize.trans hmin0, hval, ?_⟩
  intro i hout
  by_contra hn
  have dead : ∀ k < D.gates.length, M + i.val ∉ (gateAt D k).inputs := by
    intro k hk hpin
    have hh := hback k hk _ hpin
    have later : i < (⟨k, hk⟩ : Fin D.gates.length) := by
      change i.val < k
      omega
    have eqg : D.gates.get ⟨k, hk⟩ = gateAt D k := (List.getD_eq_getElem _ _ hk).symm
    have hgk : Good P (D.gates.get ⟨k, hk⟩) := hgood _ (List.getElem_mem hk)
    have hread : reads (D.gates.get ⟨k, hk⟩) (M + i.val) ↔
        M + i.val ∈ (D.gates.get ⟨k, hk⟩).inputs := by
      apply good_read
      exact hgk
    exact hn ⟨⟨k, hk⟩, later, hread.2 (by rwa [eqg])⟩
  let E : Circuit := ⟨D.gates.set i.val ⟨GateOp.or, []⟩, D.output⟩
  have hdf : FanInTwo D := by apply good_fan; exact hgood
  have hdm : P → Monotone2 D := by
    intro hP
    apply good_mono <;> assumption
  obtain ⟨hef, hem, _, hes, heq, hzero⟩ :=
    blank_dead_signed P M D hdf hdm hback i.val i.isLt dead hout.symm
  have heval (x : X) : E.eval (y x) = f x := (heq _ (hy x)).trans (hval x)
  have hmarked : ∀ j ∈ ({i.val} : Finset ℕ), j < E.gates.length ∧
      ((∃ b, ∀ x, (run E.gates (y x)).getD (M + j) false = b) ∨
       ∃ w < M + j, ∀ x, (run E.gates (y x)).getD (M + j) false =
         (run E.gates (y x)).getD w false) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst j
    exact ⟨by simpa [E] using i.isLt, Or.inl ⟨false, fun x => hzero _ (hy x)⟩⟩
  obtain ⟨J, hJg, hJb, hJs, hJv⟩ := engine P M M E y y hy hy {i.val} hef hem
    (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩)
    (fun ⟨b, h⟩ => hnc ⟨b, fun x => (heval x).symm.trans (h x)⟩) hmarked
  have lower : Nat.find hex ≤ J.size :=
    Nat.find_min' hex ⟨J, hJg, hJb, le_rfl, fun x => (hJv x).trans (heval x)⟩
  rw [Finset.card_singleton] at hJs
  change E.size = D.size at hes
  omega

end CutLib25855.Normalize

namespace CutLib25855.Pins
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem sum_count (l : List ℕ) (N : ℕ) (h : ∀ i ∈ l, i < N) :
    ∑ w ∈ Finset.range N, l.count w = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a < N := h a (by simp)
    rw [List.length_cons, ← ih (fun i hi => h i (by simp [hi]))]
    simp [List.count_cons, Finset.sum_add_distrib, ha]

theorem key (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) :
    (∑ w ∈ Finset.range m, readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size, readsIn C (Finset.range C.size) (m + j)) =
    ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length := by
  rw [← Finset.sum_range_add]
  unfold readsIn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => sum_count _ _ fun i hi => ?_
  have h1 : j < C.size := Finset.mem_range.mp hj
  have := hrb j h1 i hi
  omega

theorem slots (C : Circuit)
    (hg : ∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    (∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length) +
      (@Finset.filter ℕ (fun k => (gateAt C k).op = GateOp.not) (fun d1 => Classical.propDecidable _)
        (Finset.range C.size)).card = C.size + C.size := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.sum_congr rfl (g := fun _ => 2) ?_]
  · simp [Circuit.size]
    omega
  · intro j hj
    have hj' : j < C.gates.length := Finset.mem_range.mp hj
    have hmem : gateAt C j ∈ C.gates := by
      simp only [gateAt, List.getD_eq_getElem _ _ hj']
      exact List.getElem_mem hj'
    rcases hg _ hmem with ⟨h1 | h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem tail (s : ℕ) (f : ℕ → ℕ) (hs : 0 < s) (h : ∀ j < s, (f j = 0 ↔ j + 1 = s)) :
    (∑ j ∈ Finset.range (s - 1), (f j - 1)) + (s - 1) = ∑ j ∈ Finset.range s, f j := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hk : f k = 0 := (h k (by omega)).2 rfl
  simp only [Nat.add_sub_cancel, Finset.sum_range_succ, hk, Nat.add_zero]
  have : ∀ j ∈ Finset.range k, f j - 1 + 1 = f j := fun j hj => by
    have hj' : j < k := Finset.mem_range.mp hj
    have : f j ≠ 0 := fun h0 => by have := (h j (by omega)).1 h0; omega
    omega
  rw [← Finset.sum_congr rfl this, Finset.sum_add_distrib]
  simp

end CutLib25855.Pins

namespace CutLib25855.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def gates69 (C : Circuit) := Finset.range C.size
def reads69 (C : Circuit) (w : Nat) := readsIn C (gates69 C) w
noncomputable def neg69 (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>(gateAt C k).op=.not)
noncomputable def special (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact ((Finset.range (N+C.size)).filter (fun w=>2≤reads69 C w)) ∪
    (neg69 C).image (fun k=>N+k)
noncomputable def ordinary (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>N+k∉special N C)
noncomputable def exits69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈gates69 C \ ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∉special N C))
noncomputable def entries69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∈special N C))
def once69 (N : Nat) (C : Circuit) := (Finset.range N).filter (fun w=>reads69 C w=1)
def shapes69 (C : Circuit) : Prop := ∀g∈C.gates,
  ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1)

def tree69 (N : Nat) (C : Circuit) (S E : Finset Nat) : Prop := ∃ region : Finset Nat, ∃ root : Nat,
  let wires := S ∪ region.image (fun k=>N+k)
  let localReads := readsIn C region
  region ⊆ ordinary N C ∧ root∈wires ∧ localReads root=0 ∧
  (∀b∈E,b∉wires ∧ b<root ∧ localReads b=1) ∧
  (∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀w∈(gateAt C j).inputs, w∈wires ∨ w∈E) ∧
  (∀w∈wires,w≠root → localReads w=1 ∧ reads69 C w=1 ∧ C.output≠w)

theorem ordinary_reads69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    reads69 C (N+k)≤1 := by
  classical
  obtain ⟨hk,hn⟩:=Finset.mem_filter.mp h
  have lt : k<C.size := Finset.mem_range.mp hk
  by_contra! many
  exact hn (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩))

theorem ordinary_index69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    k<C.size := Finset.mem_range.mp (Finset.mem_filter.mp h).1

end CutLib25855.Partition

namespace CutLib25855.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

noncomputable def color69 (N : Nat) (C : Circuit) (w : Nat) : Bool :=
  if w∈special N C then true else if w<N then false else
    (gateAt C (w-N)).inputs.any (fun v => if hv : v<w then color69 N C v else false)
termination_by w

noncomputable def split69 (N : Nat) (C : Circuit) :=
  (ordinary N C).filter (fun j=>2≤((gateAt C j).inputs.filter (color69 N C)).length)

noncomputable def keep69 (N : Nat) (C : Circuit) := ordinary N C \ split69 N C

theorem color_special {N w : Nat} {C : Circuit} (h : w∈special N C) : color69 N C w=true := by
  rw [color69,ite_eq_left h]

theorem color_raw {N w : Nat} {C : Circuit} (hw : w<N) (h : w∉special N C) :
    color69 N C w=false := by rw [color69,ite_eq_right h,ite_eq_left hw]

theorem color_ordinary_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈ordinary N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true := by
  have ns := (Finset.mem_filter.mp hj).2
  rw [color69,ite_eq_right ns,ite_eq_right (by omega : ¬N+j<N),Nat.add_sub_cancel_left,List.any_eq_true]
  apply exists_congr
  intro w
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩

theorem color_keep_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈keep69 N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true :=
  color_ordinary_iff back (Finset.mem_sdiff.mp hj).1

theorem marked_keep_slots {N j : Nat} {C : Circuit} (hj : j∈keep69 N C) :
    ((gateAt C j).inputs.filter (color69 N C)).length≤1 := by
  obtain ⟨ord,no⟩ := Finset.mem_sdiff.mp hj
  by_contra! two
  exact no (Finset.mem_filter.mpr ⟨ord,two⟩)

theorem color_split_all {N j : Nat} {C : Circuit} (sh : shapes69 C) (hj : j∈split69 N C) :
    ∀ w∈(gateAt C j).inputs,color69 N C w=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  have jlt : j<C.gates.length := ordinary_index69 ord
  have mem : gateAt C j∈C.gates := by simp [gateAt,jlt]
  have len : (gateAt C j).inputs.length≤2 := by rcases sh _ mem with h|h <;> omega
  apply List.length_filter_eq_length_iff.mp
  have hl := List.length_filter_le (p:=color69 N C) (l:=(gateAt C j).inputs)
  omega

theorem color_split_self {N j : Nat} {C : Circuit} (back : ReadsBack N C) (hj : j∈split69 N C) :
    color69 N C (N+j)=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  apply (color_ordinary_iff back ord).2
  rw [←List.countP_pos_iff,List.countP_eq_length_filter]
  omega

private lemma maskedCount69 (l : List Nat) (A : Finset Nat) :
    l.countP (fun w=>decide (w∈A)) = ∑w∈A,l.count w := by
  classical
  let f := l.filter (fun w=>decide (w∈A))
  have sub : f.toFinset ⊆ A := by
    intro w hw
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change f.length=_
  calc
    _ = ∑w∈f.toFinset,f.count w := (List.sum_toFinset_count_eq_length f).symm
    _ = ∑w∈A,f.count w := Finset.sum_subset sub (fun _ _ h =>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))
    _ = _ := Finset.sum_congr rfl (fun w hw=>List.count_filter (by simpa using hw))

private lemma countCover69 (l : List Nat) (p s a : Nat→Bool)
    (cover : ∀w∈l,p w=true → s w=true ∨ a w=true) : l.countP p≤l.countP s+l.countP a := by
  induction l with
  | nil => simp
  | cons w ws ih =>
    have tail := ih (fun v hv=>cover v (List.mem_cons_of_mem _ hv))
    have head := cover w List.mem_cons_self
    cases hp : p w <;> cases hs : s w <;> cases ha : a w <;> simp_all [List.countP_cons] <;> omega

private theorem countedSlots69 {N : Nat} {C : Circuit} (P A : Finset Nat)
    (p : Nat→Bool) (pg : P⊆ordinary N C) (ag : A⊆ordinary N C)
    (cover : ∀ j∈P, ∀w∈(gateAt C j).inputs,p w=true →
      w∈special N C ∨ w∈A.image (fun t=>N+t)) :
    (∑j∈P,(gateAt C j).inputs.countP p)≤entries69 N C+A.card := by
  classical
  let I := A.image (fun j=>N+j)
  let specialSlot := fun w=>decide (w∈special N C)
  have each (j : Nat) (hj : j∈P) : (gateAt C j).inputs.countP p ≤
      (gateAt C j).inputs.countP specialSlot + ∑w∈I,(gateAt C j).inputs.count w := by
    rw [←maskedCount69]
    apply countCover69
    intro w hw hp
    exact (cover j hj w hw hp).imp (fun h=>by simpa [specialSlot] using h) (fun h=>by simpa [I] using h)
  have sl : (∑ j∈P,(gateAt C j).inputs.countP specialSlot) ≤ entries69 N C :=
    Finset.sum_le_sum_of_subset_of_nonneg pg (fun _ _ _ => Nat.zero_le _)
  have rest (w : Nat) (hw : w∈I) : (∑ j∈P,(gateAt C j).inputs.count w) ≤ 1 := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    apply le_trans (b:=reads69 C (N+j)) _ (ordinary_reads69 (ag hj))
    unfold reads69 readsIn
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
    exact fun q hq=>(Finset.mem_filter.mp (pg hq)).1
  have total := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,Finset.sum_comm (s:=P) (t:=I)] at total
  have pool := Finset.sum_le_sum rest
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at pool
  have cap : I.card≤A.card := Finset.card_image_le
  omega

theorem splitCard69 {N : Nat} {C : Circuit} (_sh : shapes69 C) (back : ReadsBack N C) :
    (split69 N C).card≤entries69 N C := by
  classical
  let A := (ordinary N C).filter (fun j=>color69 N C (N+j)=true)
  have cover (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (hl : color69 N C w=true) : w∈special N C ∨ w∈A.image (fun t=>N+t) := by
    by_cases sp : w∈special N C
    · exact Or.inl sp
    right
    have wire : w<N+j := back j (ordinary_index69 hj) w hw
    have mid : N≤w := by by_contra! z;rw [color_raw z sp] at hl;contradiction
    have eq : N+(w-N)=w := by omega
    have idx : w-N<C.size := by have := ordinary_index69 hj;omega
    have good : w-N∈ordinary N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,by simpa only [eq] using sp⟩
    exact Finset.mem_image.mpr ⟨w-N,Finset.mem_filter.mpr ⟨good,by simpa only [eq] using hl⟩,eq⟩
  have account := countedSlots69 (ordinary N C) A (color69 N C) (fun _ h=>h)
    (fun _ h=>(Finset.mem_filter.mp h).1) cover
  have pay (j : Nat) (hj : j∈ordinary N C) :
      (if color69 N C (N+j)=true then 1 else 0) +
      (if 2≤((gateAt C j).inputs.filter (color69 N C)).length then 1 else 0) ≤
      (gateAt C j).inputs.countP (color69 N C) := by
    rw [List.countP_eq_length_filter]
    by_cases many : 2≤((gateAt C j).inputs.filter (color69 N C)).length
    · rw [ite_eq_left many];split <;> omega
    rw [ite_eq_right many]
    split
    · next hc =>
      have has := (color_ordinary_iff back hj).1 hc
      have pos := List.countP_pos_iff.mpr has
      rw [List.countP_eq_length_filter] at pos
      omega
    · omega
  have total := Finset.sum_le_sum pay
  rw [Finset.sum_add_distrib,←Finset.card_filter,←Finset.card_filter] at total
  change A.card+(split69 N C).card≤_ at total
  omega

theorem entrySlotsBound69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) :
    (∑j∈keep69 N C,(gateAt C j).inputs.countP
      (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))) ≤ 2*entries69 N C := by
  classical
  have cap := countedSlots69 (keep69 N C) (split69 N C)
    (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
    (fun _ h=>(Finset.mem_sdiff.mp h).1) (fun _ h=>(Finset.mem_filter.mp h).1) (by
      intro j hj w hw h
      rcases of_decide_eq_true h with s|⟨low,idx⟩
      · exact Or.inl s
      · exact Or.inr (Finset.mem_image.mpr ⟨w-N,idx,by omega⟩))
  have splitBound := splitCard69 sh back
  omega

end CutLib25855.Partition

namespace CutLib25855.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def pool69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  once69 N C ∪ P.image (fun k=>N+k)

def branch69 (N : Nat) (C : Circuit) (P : Finset Nat) (x y : Nat) : Prop :=
  x∈pool69 N C P ∧ ∃k∈P, y=N+k ∧ x∈(gateAt C k).inputs

abbrev walk69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  Relation.ReflTransGen (branch69 N C P)

def sink69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Prop :=
  ∀ y, ¬ branch69 N C P x y

noncomputable def owner69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Nat := by
  classical exact if h : ∃y,walk69 N C P x y ∧ sink69 N C P y then h.choose else x

noncomputable def roots69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  (once69 N C).image (owner69 N C P)

noncomputable def src69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (once69 N C).filter (fun w=>owner69 N C P w=z)

noncomputable def reg69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact P.filter (fun k=>owner69 N C P (N+k)=z)

noncomputable def outside69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (reg69 N C P z).biUnion fun k =>
    (gateAt C k).inputs.toFinset.filter (fun w=>w∉pool69 N C P)

noncomputable def slots69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Nat := by
  classical exact ∑ k∈reg69 N C P z,(gateAt C k).inputs.countP (fun w=>decide (w∉pool69 N C P))

variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem reads_le_one69 (hp : P⊆ordinary N C) {w : Nat} (hw : w∈pool69 N C P) : reads69 C w≤1 := by
  rcases Finset.mem_union.mp hw with h | h
  · exact (Finset.mem_filter.mp h).2.le
  · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp h;exact ordinary_reads69 (hp hk)

theorem reader69 {w i j : Nat} (one : reads69 C w≤1) (hi : i<C.size) (hj : j<C.size)
    (a : w∈(gateAt C i).inputs) (b : w∈(gateAt C j).inputs) : i=j := by
  by_contra ne
  have h:=Finset.add_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _)
    (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) ne
  have ai:=List.count_pos_iff.mpr a
  have bj:=List.count_pos_iff.mpr b
  change _ ≤ reads69 C w at h
  omega

theorem next_unique69 (hp : P⊆ordinary N C) : Relator.RightUnique (branch69 N C P) := by
  rintro w x y ⟨hw,i,hi,rfl,a⟩ ⟨_,j,hj,rfl,b⟩
  rw [reader69 (reads_le_one69 hp hw) (ordinary_index69 (hp hi)) (ordinary_index69 (hp hj)) a b]

theorem next_lt69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (h : branch69 N C P x y) : x<y ∧ y<N+C.size := by
  obtain ⟨_,k,hk,rfl,inp⟩:=h
  have lt:=ordinary_index69 (hp hk)
  exact ⟨back k lt x inp,by omega⟩

theorem walk_in69 {x y : Nat} (h : walk69 N C P x y) (hx : x∈pool69 N C P) :
    y∈pool69 N C P := by
  induction h with
  | refl => exact hx
  | tail _ e _ =>
    obtain ⟨_,k,hk,rfl,_⟩ := e
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)

theorem owner_spec69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (w : Nat) :
    walk69 N C P w (owner69 N C P w) ∧ sink69 N C P (owner69 N C P w) := by
  classical
  have exists' (i : Nat) : ∀x,N+C.size-x=i → ∃y,walk69 N C P x y ∧ sink69 N C P y := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro x eq
      by_cases e : ∃y,branch69 N C P x y
      · obtain ⟨y,hy⟩:=e
        obtain ⟨lt,bound⟩:=next_lt69 hp back hy
        obtain ⟨v,path,sink⟩:=ih (N+C.size-y) (by omega) y rfl
        exact ⟨v,path.head hy,sink⟩
      · exact ⟨x,.refl,fun y h=> e ⟨y,h⟩⟩
  have h:=exists' _ w rfl
  simpa only [owner69,dif_pos h] using h.choose_spec

theorem owner_same69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (e : branch69 N C P x y) : owner69 N C P x = owner69 N C P y := by
  have a := owner_spec69 hp back x
  have b := owner_spec69 hp back y
  have term {u v : Nat} (s : sink69 N C P u) (path : walk69 N C P u v) : u=v := by
    rcases path.cases_head with eq|⟨z,e,_⟩
    · exact eq
    · exact (s z e).elim
  rcases Relation.ReflTransGen.total_of_right_unique (next_unique69 hp)
    a.1 (b.1.head e) with h|h
  · exact term a.2 h
  · exact (term b.2 h).symm

theorem fiber69 (z w : Nat) :
    w∈src69 N C P z ∪ (reg69 N C P z).image (fun k=>N+k) ↔
      w∈pool69 N C P ∧ owner69 N C P w=z := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.mp h with a|b
    · obtain ⟨h,e⟩:=Finset.mem_filter.mp a;exact ⟨Finset.mem_union_left _ h,e⟩
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      obtain ⟨h,e⟩:=Finset.mem_filter.mp hk;exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ h),e⟩
  · rintro ⟨pool,e⟩
    rcases Finset.mem_union.mp pool with a|b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨a,e⟩)
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hk,e⟩))

theorem root_info69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    z∈pool69 N C P ∧ sink69 N C P z ∧ owner69 N C P z=z ∧ (src69 N C P z).Nonempty := by
  obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
  have sp:=owner_spec69 hp back u
  refine ⟨walk_in69 sp.1 (Finset.mem_union_left _ hu),sp.2,?_,⟨u,Finset.mem_filter.mpr ⟨hu,rfl⟩⟩⟩
  have p:=(owner_spec69 hp back (owner69 N C P u)).1
  rcases p.cases_head with eq|⟨x,step,_⟩
  · exact eq.symm
  · exact (sp.2 x step).elim

end CutLib25855.Partition

namespace CutLib25855.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem root_zero69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    readsIn C (reg69 N C P z) z=0 := by
  obtain ⟨pool,sink,_,_⟩:=root_info69 hp back hz
  apply Finset.sum_eq_zero
  intro j hj;apply List.count_eq_zero.mpr
  intro h;exact sink (N+j) ⟨pool,j,(Finset.mem_filter.mp hj).1,rfl,h⟩

theorem local_read69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z w : Nat}
    (pool : w∈pool69 N C P) (ow : owner69 N C P w=z) (other : w≠z) :
    readsIn C (reg69 N C P z) w=1 ∧ reads69 C w=1 := by
  obtain ⟨way,_⟩:=owner_spec69 hp back w
  rw [ow] at way
  obtain ⟨_,⟨_,k,hk,rfl,hit⟩,_⟩:=way.cases_head.resolve_left other
  have eq := owner_same69 hp back (show branch69 N C P w (N+k) from ⟨pool,k,hk,rfl,hit⟩)
  have mem : k∈reg69 N C P z := Finset.mem_filter.mpr ⟨hk,eq.symm.trans ow⟩
  have le : (gateAt C k).inputs.count w ≤ readsIn C (reg69 N C P z) w :=
    Finset.single_le_sum (fun l _=>Nat.zero_le ((gateAt C l).inputs.count w)) mem
  have bound : readsIn C (reg69 N C P z) w ≤ reads69 C w :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun j hj =>
      Finset.mem_range.mpr (ordinary_index69 (hp (Finset.mem_filter.mp hj).1))) (fun _ _ _=>Nat.zero_le _)
  have counted:=List.count_pos_iff.mpr hit;have all:=reads_le_one69 hp pool
  omega

theorem pool_bound69 (hp : P⊆ordinary N C) {w : Nat} (pool : w∈pool69 N C P) : w<N+C.size := by
  rcases Finset.mem_union.mp pool with h|h
  · have lt:=Finset.mem_range.mp (Finset.mem_filter.mp h).1;omega
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h;have:=ordinary_index69 (hp hj);omega

theorem walk_le69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat} (path : walk69 N C P x y) :
    x≤y := by
  induction path with
  | refl => exact le_rfl
  | tail _ e ih => exact ih.trans (next_lt69 hp back e).1.le

theorem outside_mem69 {z w : Nat} :
    w∈outside69 N C P z ↔ w∉pool69 N C P ∧ ∃k∈reg69 N C P z,w∈(gateAt C k).inputs := by
  classical
  simp only [outside69,Finset.mem_biUnion,Finset.mem_filter,List.mem_toFinset]
  grind

private theorem read_le_slots69 {z w : Nat} (out : w∉pool69 N C P) :
    readsIn C (reg69 N C P z) w ≤ slots69 N C P z := by
  classical
  apply Finset.sum_le_sum
  intro k _
  induction (gateAt C k).inputs with
  | nil => simp
  | cons a l ih =>
    simp only [decide_not] at ih
    by_cases eq : a=w
    · subst a;simp [List.count_cons,List.countP_cons,out,ih]
    · by_cases pa:a∈pool69 N C P <;> simp [List.count_cons,List.countP_cons,eq,pa,ih] <;> omega

theorem out_pos69 {z w : Nat} (h : w∈outside69 N C P z) :
    0<readsIn C (reg69 N C P z) w ∧ readsIn C (reg69 N C P z) w≤ slots69 N C P z := by
  obtain ⟨no,k,hk,hx⟩:=outside_mem69.mp h
  exact ⟨(List.count_pos_iff.mpr hx).trans_le
    (Finset.single_le_sum (fun j _=>Nat.zero_le ((gateAt C j).inputs.count w)) hk),read_le_slots69 no⟩

theorem outside_card69 {z : Nat} : (outside69 N C P z).card ≤ slots69 N C P z := by
  classical
  unfold outside69 slots69
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
  intro k _
  have h (l : List Nat) : (l.toFinset.filter (fun w=>w∉pool69 N C P)).card ≤
      l.countP (fun w=>decide (w∉pool69 N C P)) := by
    induction l with
    | nil => simp
    | cons w l ih =>
      simp only [decide_not] at ih
      by_cases hw:w∈pool69 N C P
      · simpa [Finset.filter_insert,hw,List.countP_cons] using ih
      · simp [Finset.filter_insert,hw,List.countP_cons]
        exact (Finset.card_insert_le _ _).trans (by omega)
  exact h _

theorem outside_empty69 {z : Nat} : outside69 N C P z=∅ ↔ slots69 N C P z=0 := by
  classical
  constructor
  · intro empty;apply Finset.sum_eq_zero;intro k hk
    apply List.countP_eq_zero.mpr
    intro w hw
    simp only [Bool.not_eq_true,decide_eq_false_iff_not,not_not]
    by_contra out
    have h : w∈outside69 N C P z := outside_mem69.mpr ⟨out,k,hk,hw⟩
    simp [empty] at h
  · intro z0;apply Finset.card_eq_zero.mp;have le:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z);omega

theorem subtree69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (sh : shapes69 C)
    (last : C.output+1=N+C.size) {z : Nat} (hz : z∈roots69 N C P)
    (slot : slots69 N C P z≤1) : tree69 N C (src69 N C P z) (outside69 N C P z) := by
  classical
  obtain ⟨zp,sink,zown,nonempty⟩:=root_info69 hp back hz
  have bound:=pool_bound69 hp zp
  refine ⟨reg69 N C P z,z,fun j hj=>hp (Finset.mem_filter.mp hj).1,
    (fiber69 z z).mpr ⟨zp,zown⟩,root_zero69 hp back hz,?_,?_,?_⟩
  · intro w hw
    obtain ⟨out,k,hk,read⟩:=outside_mem69.mp hw
    have lt:=back k (ordinary_index69 (hp (Finset.mem_filter.mp hk).1)) w read
    have path:=(owner_spec69 hp back (N+k)).1
    rw [(Finset.mem_filter.mp hk).2] at path
    have cmp:=walk_le69 hp back path
    obtain ⟨pos,le⟩:=out_pos69 hw
    exact ⟨fun h=>out ((fiber69 z w).mp h).1,by omega,by omega⟩
  · intro j hj
    obtain ⟨keep,own⟩:=Finset.mem_filter.mp hj
    have ord:=hp keep;have jl:=ordinary_index69 ord
    have mem : gateAt C j∈C.gates := by have h:j<C.gates.length:=jl;simp [gateAt,h]
    rcases sh _ mem with ao | no
    · refine ⟨ao.1,ao.2,?_⟩
      intro w wh
      by_cases pooled:w∈pool69 N C P
      · exact Or.inl ((fiber69 z w).mpr ⟨pooled,(owner_same69 hp back ⟨pooled,j,keep,rfl,wh⟩).trans own⟩)
      · exact Or.inr (outside_mem69.mpr ⟨pooled,j,hj,wh⟩)
    · have ns: N+j∉special N C := (Finset.mem_filter.mp ord).2
      apply (ns (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (show j∈neg69 C from Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jl,no.1⟩)))).elim
  · intro w hw diff
    obtain ⟨pool,own⟩:=(fiber69 z w).mp hw
    obtain ⟨loc,all⟩:=local_read69 hp back pool own diff
    have path:=(owner_spec69 hp back w).1
    rw [own] at path
    have le:=walk_le69 hp back path
    exact ⟨loc,all,by omega⟩

end CutLib25855.Partition

namespace CutLib25855.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C:Circuit}
lemma keepSub69 : keep69 N C ⊆ ordinary N C := Finset.sdiff_subset
lemma colorOnce69 {w:Nat} (h:w∈once69 N C) : color69 N C w=false := by
  obtain ⟨hw,one⟩:=Finset.mem_filter.mp h
  have lo:=Finset.mem_range.mp hw
  apply color_raw lo
  intro hs
  rcases Finset.mem_union.mp hs with rep|notw
  · have high:2≤reads69 C w := (Finset.mem_filter.mp rep).2
    omega
  · obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp notw;omega
lemma colorOuter69 (back:ReadsBack N C) {j w:Nat} (hp:j∈keep69 N C) (hit:w∈(gateAt C j).inputs)
    (out:w∉pool69 N C (keep69 N C)) : color69 N C w=true := by
  classical
  have jj:=ordinary_index69 (keepSub69 hp)
  have wr:=back j jj w hit
  by_cases hs:w∈special N C
  · exact color_special hs
  by_cases low:w<N
  · have used:0<reads69 C w := by
      have h:=Finset.single_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr jj)
      have count:=List.count_pos_iff.mpr hit
      change _≤reads69 C w at h
      omega
    have one:reads69 C w=1 := by
      by_contra! ne
      apply hs
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩)
    exact (out (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr low,one⟩))).elim
  · let k:=w-N
    have eq:N+k=w := by dsimp [k];omega
    have ord:k∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [k];omega),by rwa [eq]⟩
    by_cases sp:k∈split69 N C
    · exact eq ▸ color_split_self back sp
    · have kkeep:k∈keep69 N C:=Finset.mem_sdiff.mpr ⟨ord,sp⟩
      exact (out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,kkeep,eq⟩))).elim

lemma markedInputs69 (back:ReadsBack N C) {j:Nat} (h:j∈keep69 N C) :
    (gateAt C j).inputs.countP (color69 N C) = if color69 N C (N+j) then 1 else 0 := by
  have le:=marked_keep_slots h
  rw [←List.countP_eq_length_filter] at le
  have pos := color_keep_iff back h
  rw [←List.countP_pos_iff] at pos
  cases hx:color69 N C (N+j)
  · change (gateAt C j).inputs.countP (color69 N C)=0
    by_contra! ne
    have eq:=pos.mpr (by omega)
    rw [hx] at eq;contradiction
  · change (gateAt C j).inputs.countP (color69 N C)=1
    have hp:=pos.mp hx
    omega

lemma splitInputCount69 (L:List Nat) (p:Nat→Bool) (pool A:Finset Nat)
    (spec:∀w∈L, (p w=true ↔ w∉pool ∨ w∈A) ∧ (w∈A → w∈pool)) :
    L.countP p = L.countP (fun w=>decide (w∉pool)) + ∑w∈A,L.count w := by
  classical
  induction L with
  | nil => simp
  | cons x xs ih =>
    have t:=ih (fun w hw=>spec w (List.mem_cons_of_mem _ hw))
    simp only [List.countP_cons,List.count_cons,Finset.sum_add_distrib]
    have a:=spec x (by simp)
    by_cases xA:x∈A <;> by_cases xp:x∈pool <;> cases xx:p x <;>
      simp_all <;> omega
end CutLib25855.Partition

namespace CutLib25855.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem conserved69 {N z:Nat} {C:Circuit} (back:ReadsBack N C)
    (hz:z∈roots69 N C (keep69 N C))
    (lr:∀ j∈reg69 N C (keep69 N C) z,
      readsIn C (reg69 N C (keep69 N C) z) (N+j)=if N+j=z then 0 else 1) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  classical
  let P:=keep69 N C
  let pool:=pool69 N C P
  let rg:=reg69 N C P z
  let hot:=rg.filter (fun j=>color69 N C (N+j)=true)
  let A:=hot.image (fun j=>N+j)
  have acard:A.card=hot.card:=Finset.card_image_of_injective _ (fun _ _ e=>Nat.add_left_cancel e)
  have rgKeep (j:Nat) (hj:j∈rg):j∈P:=(Finset.mem_filter.mp hj).1
  have memA {w:Nat} : w∈A ↔ w∈pool ∧ owner69 N C P w=z ∧ color69 N C w=true := by
    constructor
    · intro h;obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h
      obtain ⟨jr,marked⟩:=Finset.mem_filter.mp hj
      exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (rgKeep _ jr)),(Finset.mem_filter.mp jr).2,marked⟩
    · rintro ⟨h,o,t⟩
      rcases Finset.mem_union.mp h with raw|gate
      · exact (by rw [colorOnce69 raw] at t; contradiction : False).elim
      · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp gate
        exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hj,o⟩,t⟩,rfl⟩
  have inEq (j:Nat) (hj:j∈rg) :
      (gateAt C j).inputs.countP (color69 N C) =
        (gateAt C j).inputs.countP (fun w=>decide (w∉pool)) + ∑w∈A,(gateAt C j).inputs.count w := by
    apply splitInputCount69
    intro w hit
    have memPool (h:w∈pool) : owner69 N C P w=z := by
      have p:=owner_same69 (P:=P) keepSub69 back (show branch69 N C P w (N+j) from ⟨h,j,rgKeep _ hj,rfl,hit⟩)
      exact p.trans (Finset.mem_filter.mp hj).2
    refine ⟨⟨fun t=>?_,?_⟩,fun h=>(memA.mp h).1⟩
    · by_cases pw:w∈pool
      · exact Or.inr (memA.mpr ⟨pw,memPool pw,t⟩)
      · exact Or.inl pw
    · rintro (out|inside)
      · exact colorOuter69 back (rgKeep _ hj) hit out
      · exact (memA.mp inside).2.2
  have calcAll : hot.card=slots69 N C P z+∑w∈A,readsIn C rg w := by
    calc
      hot.card = ∑j∈rg, if color69 N C (N+j) then 1 else 0 := by simp only [hot,Finset.card_filter]
      _ = ∑j∈rg,(gateAt C j).inputs.countP (color69 N C) :=
        Finset.sum_congr rfl (fun j hj=>(markedInputs69 back (rgKeep _ hj)).symm)
      _ = _ := by
        rw [Finset.sum_congr rfl inEq,Finset.sum_add_distrib]
        congr 1;exact Finset.sum_comm
  have lower : (∑w∈A,readsIn C rg w)+(if z∈A then 1 else 0)=A.card := by
    calc
      _ = (∑w∈A,if w=z then 0 else 1) + (∑w∈A,if w=z then 1 else 0) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro w hw;obtain ⟨j,m,rfl⟩:=Finset.mem_image.mp hw
          exact lr _ (Finset.mem_filter.mp m).1
        · simp
      _ = ∑_w∈A,1 := by
        rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro w _;split <;> simp_all
      _ = _ := by simp
  have root:=root_info69 (P:=P) keepSub69 back hz
  have za : z∈A ↔ color69 N C z=true := ⟨fun h=>(memA.mp h).2.2,fun h=>memA.mpr ⟨root.1,root.2.2.1,h⟩⟩
  change slots69 N C P z=_
  simp only [za] at lower
  omega
end CutLib25855.Partition

namespace CutLib25855.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem fiberSlots69 {N z:Nat} {C:Circuit} (back:ReadsBack N C) (hz:z∈roots69 N C (keep69 N C)) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  apply conserved69 back hz
  intro j hj
  by_cases eq:N+j=z
  · rw [eq,ite_eq_left rfl]
    exact root_zero69 keepSub69 back hz
  · rw [ite_eq_right eq]
    obtain ⟨m,e⟩:=Finset.mem_filter.mp hj
    have pool:N+j∈pool69 N C (keep69 N C):=Finset.mem_union_right _ (Finset.mem_image_of_mem _ m)
    exact (local_read69 keepSub69 back pool e eq).1
end CutLib25855.Partition

namespace CutLib25855.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem sum_reads_mask69 (l : List Nat) (A : Finset Nat) :
    (∑w∈A,l.count w) = l.countP (fun w=>decide (w∈A)) := by
  classical
  let f:=l.filter (fun w=>decide (w∈A))
  have sub:f.toFinset⊆A := fun _ hw=>of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change _=f.length
  calc
    _ = ∑w∈A,f.count w := Finset.sum_congr rfl (fun w hw=>(List.count_filter (by simpa using hw)).symm)
    _ = ∑w∈f.toFinset,f.count w := (Finset.sum_subset sub (fun _ _ h=>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))).symm
    _ = _ := List.sum_toFinset_count_eq_length f

private theorem pure_sink69 {N z : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j))
    (hz : z∈roots69 N C (keep69 N C)) (zero : slots69 N C (keep69 N C) z=0) (out : z≠C.output) :
    z∉special N C ∧ ∃k∈gates69 C \ ordinary N C, z∈(gateAt C k).inputs := by
  classical
  obtain ⟨pool,sink,_,_⟩:=root_info69 keepSub69 back hz
  have slot:=fiberSlots69 back hz
  have off : color69 N C z=false := by cases h:color69 N C z <;> simp_all
  have ns : z∉special N C := fun h => by have a:=color_special h;rw [off] at a;contradiction
  have pos : 0<reads69 C z := by
    rcases Finset.mem_union.mp pool with raw|internal
    · have one : reads69 C z=1 := (Finset.mem_filter.mp raw).2;omega
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp internal
      have lt:=ordinary_index69 (keepSub69 hj)
      exact live j lt (by omega)
  have seek : ∃ k∈gates69 C, z∈(gateAt C k).inputs := by
    by_contra! no
    have none : reads69 C z=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
    omega
  obtain ⟨k,hk,hit⟩:=seek
  refine ⟨ns,k,Finset.mem_sdiff.mpr ⟨hk,?_⟩,hit⟩
  intro ord
  by_cases split:k∈split69 N C
  · have on:=color_split_all sh split z hit
    rw [off] at on;contradiction
  · exact sink (N+k) ⟨pool,k,Finset.mem_sdiff.mpr ⟨ord,split⟩,rfl,hit⟩

theorem pure_count69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)).card ≤ exits69 N C+1 := by
  classical
  let T:=(roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)
  let A:=T.erase C.output
  let gs:=gates69 C \ ordinary N C
  have obs (w : Nat) (hw:w∈A) : w∉special N C ∧ ∃k∈gs, w∈(gateAt C k).inputs := by
    obtain ⟨different,hh⟩:=Finset.mem_erase.mp hw
    obtain ⟨inR,zero⟩:=Finset.mem_filter.mp hh
    exact pure_sink69 sh back last live inR zero different
  have each (w:Nat) (hw:w∈A) : 1 ≤ ∑k∈gs,(gateAt C k).inputs.count w := by
    obtain ⟨k,hk,hit⟩:=(obs w hw).2
    exact (List.count_pos_iff.mpr hit).trans_le
      (Finset.single_le_sum (fun t _=>Nat.zero_le ((gateAt C t).inputs.count w)) hk)
  have bound : A.card≤exits69 N C := by
    calc
      _ = ∑ _∈A,1 := by simp
      _ ≤ ∑w∈A,∑k∈gs,(gateAt C k).inputs.count w := Finset.sum_le_sum each
      _ = ∑k∈gs,∑w∈A,(gateAt C k).inputs.count w := Finset.sum_comm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        rw [sum_reads_mask69]
        exact List.countP_mono_left (fun w _ h => decide_eq_true ((obs w (of_decide_eq_true h)).1))
  change T.card≤exits69 N C+1
  have incl : T⊆insert C.output A := by
    intro z mem;by_cases e:z=C.output
    · exact Finset.mem_insert.mpr (Or.inl e)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨e,mem⟩))
  have step:=Finset.card_le_card incl
  have cap:=Finset.card_insert_le C.output A
  change T.card≤(insert C.output A).card at step
  omega
end CutLib25855.Partition

namespace CutLib25855.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem mixed_count69 {N:Nat} {C:Circuit} (sh:shapes69 C) (back:ReadsBack N C) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)).card≤2*entries69 N C := by
  classical
  let P:=keep69 N C
  let R:=(roots69 N C P).filter (fun z=>slots69 N C P z≠0)
  let f:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∉pool69 N C P))
  let g:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
  have per (j:Nat) (hj:j∈P): f j≤g j := by
    apply List.countP_mono_left
    intro w hw out'
    have out:w∉pool69 N C P:=of_decide_eq_true out'
    apply decide_eq_true
    by_cases sp:w∈special N C
    · exact Or.inl sp
    · have color:=colorOuter69 back hj hw out
      have nle : N≤w:=by by_contra! h;rw [color_raw h sp] at color;contradiction
      have eq:N+(w-N)=w:=by omega
      have ji:=ordinary_index69 (keepSub69 hj)
      have wi:=back j ji w hw
      have ord:w-N∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [eq]⟩
      refine Or.inr ⟨nle,?_⟩
      by_contra ns
      have inside:w-N∈P:=Finset.mem_sdiff.mpr ⟨ord,ns⟩
      exact out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,inside,eq⟩))
  have lower (z:Nat) (hz:z∈R) : 1≤ slots69 N C P z := by
    have neq:slots69 N C P z≠0:=(Finset.mem_filter.mp hz).2
    omega
  change R.card≤_
  calc
    R.card = ∑_z∈R,1 := by simp
    _ ≤ ∑z∈R,slots69 N C P z := Finset.sum_le_sum lower
    _ = ∑j∈P.filter (fun i=>owner69 N C P (N+i)∈R), f j :=
      Finset.sum_fiberwise_eq_sum_filter P R (fun j=>owner69 N C P (N+j)) f
    _ ≤ ∑j∈P,f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>Nat.zero_le _)
    _ ≤ ∑j∈P,g j := Finset.sum_le_sum per
    _ ≤ _ := entrySlotsBound69 sh back
end CutLib25855.Partition

namespace CutLib25855.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem finish69 (N : Nat) (C : Circuit) (sh : shapes69 C) (back : ReadsBack N C)
    (_pos : 0<C.size) (last : C.output+1=N+C.size)
    (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ∃ pure chains : List (Finset Nat),
      pure.length≤exits69 N C+1 ∧ chains.length≤2*entries69 N C ∧
      (pure++chains).Pairwise (fun A B=>Disjoint A B) ∧
      (pure++chains).toFinset.biUnion (fun S=>S)=once69 N C ∧
      (∀S∈pure,S.Nonempty ∧ tree69 N C S ∅) ∧
      (∀S∈chains,S.Nonempty ∧ ∃b : Nat,tree69 N C S {b}) := by
  classical
  let P:=keep69 N C
  let roots:=roots69 N C P
  let Q:=roots.filter (fun z=>slots69 N C P z=0)
  let M:=roots.filter (fun z=>slots69 N C P z≠0)
  let leaf:=src69 N C P
  let qr:=Q.toList
  let mr:=M.toList
  have qmem (z:Nat) : z∈qr ↔ z∈roots ∧ slots69 N C P z=0 := by simp [qr,Q]
  have mmem (z:Nat) : z∈mr ↔ z∈roots ∧ slots69 N C P z≠0 := by simp [mr,M]
  have covered (z:Nat) : z∈qr++mr ↔ z∈roots := by
    rw [List.mem_append,qmem,mmem];tauto
  have nd : (qr++mr).Nodup := by
    refine List.nodup_append.mpr ⟨Q.nodup_toList,M.nodup_toList,?_⟩
    intro x hx y hy e;subst y;exact (mmem x|>.mp hy).2 ((qmem x|>.mp hx).2)
  have fiber {w z:Nat}: w∈leaf z ↔ w∈once69 N C ∧ owner69 N C P w=z := Finset.mem_filter
  have facts {z:Nat} (hz:z∈roots) : (leaf z).Nonempty ∧
      tree69 N C (leaf z) (outside69 N C P z) := by
    have count:=fiberSlots69 back hz
    have le : slots69 N C P z≤1 := by rw [count];split <;> decide
    exact ⟨(root_info69 keepSub69 back hz).2.2.2,subtree69 keepSub69 back sh last hz le⟩
  refine ⟨qr.map leaf,mr.map leaf,?_,?_,?_,?_,?_,?_⟩
  · simpa only [qr,List.length_map,Finset.length_toList] using pure_count69 sh back last live
  · simpa only [mr,List.length_map,Finset.length_toList] using mixed_count69 sh back
  · rw [←List.map_append,List.pairwise_map]
    apply nd.imp
    intro a b diff
    apply Finset.disjoint_left.mpr
    intro w ha hb;exact diff ((fiber.mp ha).2.symm.trans (fiber.mp hb).2)
  · rw [←List.map_append]
    ext w
    simp only [Finset.mem_biUnion,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨_,⟨z,_,rfl⟩,hit⟩;exact (fiber.mp hit).1
    · intro raw
      let z:=owner69 N C P w
      have root:z∈roots:=Finset.mem_image_of_mem _ raw
      exact ⟨leaf z,⟨z,(covered z).mpr root,rfl⟩,fiber.mpr ⟨raw,rfl⟩⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,zero⟩:=(qmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    rw [outside_empty69.mpr zero] at tree
    exact ⟨ne,tree⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,nz⟩:=(mmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    have card : (outside69 N C P z).card=1 := by
      have cap:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z)
      have count:=fiberSlots69 back rt
      have nonempty : (outside69 N C P z).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (fun h=>nz (outside_empty69.mp h))
      have pos:=Finset.card_pos.mpr nonempty
      change slots69 N C P z=_ at count
      split at count <;> omega
    obtain ⟨b,eq⟩:=Finset.card_eq_one.mp card
    exact ⟨ne,b,eq ▸ tree⟩
end CutLib25855.Partition

namespace CutLib25855
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

abbrev Active (C : Circuit) := readsIn C (Finset.range C.size)
def DifferentRows {n m : ℕ} (G : Fin n → Fin m → Bool) := ∀ a b, a≠b → ∃ c, G a c≠G b c
def DifferentCols {n m : ℕ} (G : Fin n → Fin m → Bool) := ∀ c d, c≠d → ∃ a, G a c≠G a d

theorem output_not_raw {n m : ℕ} {G : Fin n → Fin m → Bool} {C : Circuit} (rep : Represents G C)
    (horizontal : ∃ a c d, G a c ≠ G a d) (vertical : ∃ a b c, G a c ≠ G b c) : n+m≤C.output := by
  by_contra! small
  have readRaw (a c) : G a c=decide (C.output=a.val ∨ C.output=n+c.val) := by
    rw [←rep a c]
    change (Normalize.run C.gates (oneEach a c)).getD C.output false=_
    rw [Normalize.run_input _ _ _ (by rwa [Normalize.oneEach_length]),Normalize.oneEach_getD]
  by_cases l : C.output<n
  · obtain ⟨a,c,d,diff⟩ := horizontal
    apply diff
    rw [readRaw,readRaw]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]; omega
  · obtain ⟨a,b,c,diff⟩ := vertical
    have ha := a.isLt; have hb := b.isLt
    apply diff
    rw [readRaw,readRaw]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]; omega

theorem wire_positive {C : Circuit} {w j : ℕ} (hj : j<C.size) (hw : w∈(gateAt C j).inputs) :
    0<Active C w := lt_of_lt_of_le (List.count_pos_iff.mpr hw) (Finset.single_le_sum
      (f:=fun k => (gateAt C k).inputs.count w) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj))

theorem normalized {n m : ℕ} {G : Fin n → Fin m → Bool} (C : Circuit) (fan : FanInTwo C)
    (rep : Represents G C) (horizontal : ∃ a c d, G a c ≠ G a d) (vertical : ∃ a b c, G a c ≠ G b c) :
    ∃ D : Circuit, D.size≤C.size ∧ Represents G D ∧ ReadsBack (n+m) D ∧
      (∀ g∈D.gates, ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1)) ∧
      0<D.size ∧ D.output+1=n+m+D.size ∧ (∀ j<D.size, j+1<D.size → 0<Active D (n+m+j)) := by
  classical
  let N := n+m
  let y (p : Fin n × Fin m) := oneEach p.1 p.2
  let f (p : Fin n × Fin m) := G p.1 p.2
  have len (p) : (y p).length=N := Normalize.oneEach_length _ _
  have nc : ¬∃ b : Bool, ∀ p, f p=b := by
    rintro ⟨z,h⟩
    obtain ⟨a,b,c,ne⟩ := vertical
    exact ne ((h (a,c)).trans (h (b,c)).symm)
  obtain ⟨E,shape,back,sz,values⟩ := Normalize.engine False N N C y y len len ∅ fan False.elim
    (fun w hw => Or.inr ⟨w,hw,fun _ => rfl⟩)
    (fun ⟨z,h⟩ => nc ⟨z,fun p => (rep p.1 p.2).symm.trans (h p)⟩) (by simp)
  have esize : E.size≤C.size := by simpa only [Finset.card_empty,Nat.add_zero] using sz
  obtain ⟨D,dshape,db,ds,dv,live⟩ := Normalize.finish_live False N y len f nc E shape back
    (fun p => (values p).trans (rep p.1 p.2))
  have dr : Represents G D := fun a c => dv (a,c)
  have out := output_not_raw dr horizontal vertical
  have bound : D.output<N+D.size := by
    by_contra! high
    apply nc; refine ⟨false,?_⟩; intro p
    rw [←dv p]
    change (Normalize.run D.gates (y p)).getD D.output false=false
    exact Normalize.past _ _ _ (by rw [len]; exact high)
  have pos : 0<D.size := by dsimp [N] at bound; omega
  let last : Fin D.gates.length := ⟨D.size-1,by change D.size-1<D.size; omega⟩
  have final : N+last.val=D.output := by
    by_contra no
    obtain ⟨j,lt,_⟩ := live last no
    have hj := j.isLt
    change D.size-1<j.val at lt
    change j.val<D.size at hj
    omega
  have lastEq : D.output+1=N+D.size := by change N+(D.size-1)=D.output at final; omega
  refine ⟨D,ds.trans esize,dr,db,?_,pos,lastEq,?_⟩
  · intro g hg
    rcases (dshape g hg).1 with ⟨op,a,h⟩|⟨op,a,b,_,h⟩
    · exact Or.inr ⟨op,by simp [h]⟩
    · exact Or.inl ⟨op,by simp [h]⟩
  · intro j hj nonfinal
    have ne : N+j≠D.output := by omega
    obtain ⟨p,_,usage⟩ := live ⟨j,hj⟩ ne
    have ray : (D.gates.get p)=gateAt D p.val := (List.getD_eq_getElem _ _ p.isLt).symm
    change Normalize.reads (D.gates.get p) (N+j) at usage
    rw [ray] at usage
    apply wire_positive p.isLt
    rcases usage with ⟨_,h⟩|⟨_,h⟩
    · cases l : (gateAt D p.val).inputs with
      | nil => simp [l] at h
      | cons a tail =>
        simp [l] at h
        exact List.mem_cons.mpr (Or.inl h.symm)
    · exact h

theorem observed_agree {N : ℕ} {C : Circuit} (back : ReadsBack N C) (x y : List Bool)
    (lx : x.length=N) (ly : y.length=N)
    (h : ∀ i<N, 0<Active C i → x.getD i false=y.getD i false) :
    ∀ w, N≤w → (Normalize.run C.gates x).getD w false=(Normalize.run C.gates y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro ge
    by_cases far : N+C.size≤w
    · rw [Normalize.past C.gates x _ (by rw [lx]; exact far),Normalize.past C.gates y _ (by rw [ly]; exact far)]
    let j := w-N
    have eq : N+j=w := Nat.add_sub_of_le ge
    have len : j<C.size := by dsimp [j]; omega
    rw [←eq,Normalize.gv N C back x lx j len,Normalize.gv N C back y ly j len]
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases raw : i<N
    · rw [Normalize.run_input _ _ _ (by rwa [lx]),Normalize.run_input _ _ _ (by rwa [ly])]
      exact h i raw (wire_positive len hi)
    · have smaller := back j len i hi
      exact ih i (by omega) (by omega)

theorem few_missing {n m : ℕ} (G : Fin n → Fin m → Bool) (D : Circuit) (back : ReadsBack (n+m) D)
    (rep : Represents G D) (out : n+m≤D.output) (rows : DifferentRows G) (cols : DifferentCols G) :
    n+m≤((Finset.range (n+m)).filter (fun i => 1≤Active D i)).card+2 := by
  classical
  let v := Active D
  have equal {a b : Fin n} {c d : Fin m}
      (same : ∀ i<n+m, 0<v i → ((i=a.val ∨ i=n+c.val) ↔ (i=b.val ∨ i=n+d.val))) : G a c=G b d := by
    rw [←rep a c,←rep b d]
    apply observed_agree back _ _ (Normalize.oneEach_length _ _) (Normalize.oneEach_length _ _) _ _ out
    intro i hi hit
    rw [Normalize.oneEach_getD,Normalize.oneEach_getD]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using same i hi hit
  have rsmall : ((Finset.range n).filter (fun i => v i=0)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha,za⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb,zb⟩ := Finset.mem_filter.mp hb
    let A : Fin n := ⟨a,Finset.mem_range.mp ha⟩
    let B : Fin n := ⟨b,Finset.mem_range.mp hb⟩
    by_contra ne
    obtain ⟨c,diff⟩ := rows A B (fun h => ne (congrArg Fin.val h))
    apply diff; apply equal
    intro i hi hit
    have ia : i≠a := fun e => by rw [e,za] at hit; omega
    have ib : i≠b := fun e => by rw [e,zb] at hit; omega
    simp [A,B,ia,ib]
  have csmall : ((Finset.range m).filter (fun i => v (n+i)=0)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro c hc d hd
    obtain ⟨hc,zc⟩ := Finset.mem_filter.mp hc
    obtain ⟨hd,zd⟩ := Finset.mem_filter.mp hd
    let X : Fin m := ⟨c,Finset.mem_range.mp hc⟩
    let Y : Fin m := ⟨d,Finset.mem_range.mp hd⟩
    by_contra ne
    obtain ⟨a,diff⟩ := cols X Y (fun h => ne (congrArg Fin.val h))
    apply diff; apply equal
    intro i hi hit
    have ix : i≠n+c := fun e => by rw [e,zc] at hit; omega
    have iy : i≠n+d := fun e => by rw [e,zd] at hit; omega
    simp [X,Y,ix,iy]
  let A := Finset.range (n+m)
  have split : (A.filter (fun i => v i=0)).card+(A.filter (fun i => 1≤v i)).card=A.card := by
    rw [Finset.card_filter,Finset.card_filter,←Finset.sum_add_distrib]
    calc
      _ = ∑ _i∈A, 1 := by
        apply Finset.sum_congr rfl
        intro i _; split_ifs <;> omega
      _ = _ := by simp
  have zeros : (A.filter (fun i => v i=0)).card≤2 := by
    rw [Finset.card_filter] at rsmall csmall ⊢
    dsimp only [A]
    rw [Finset.sum_range_add]
    omega
  change n+m≤(A.filter (fun i => 1≤v i)).card+2
  have total : A.card=n+m := by simp [A]
  omega

end CutLib25855

namespace CutLib25855
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def used (N : ℕ) (C : Circuit) := ((Finset.range N).filter (fun w => 1≤Active C w)).card
def surplus (N : ℕ) (C : Circuit) := ∑ w∈Finset.range (N+C.size), (Active C w-1)
noncomputable def budget (N : ℕ) (C : Circuit) := surplus N C+(Partition.neg69 C).card

theorem active_last {N : ℕ} (C : Circuit) (back : ReadsBack N C) (pos : 0<C.size)
    (live : ∀ j<C.size, j+1<C.size → 0<Active C (N+j)) :
    ∀ j<C.size, Active C (N+j)=0 ↔ j+1=C.size := by
  intro j hj
  constructor
  · intro zero
    by_contra ne
    have := live j hj (by omega)
    omega
  · intro last
    apply Finset.sum_eq_zero
    intro k hk
    apply List.count_eq_zero.mpr
    intro hit
    have kk := Finset.mem_range.mp hk
    have earlier := back k kk _ hit
    omega

theorem budget_eq {N : ℕ} (C : Circuit) (shape : Partition.shapes69 C) (back : ReadsBack N C)
    (pos : 0<C.size) (live : ∀ j<C.size, j+1<C.size → 0<Active C (N+j)) :
    C.size+1=used N C+budget N C := by
  classical
  let v := Active C
  let rawExtra := ∑ w∈Finset.range N,(v w-1)
  let gateExtra := ∑ j∈Finset.range C.size,(v (N+j)-1)
  have raw : (∑ w∈Finset.range N,v w)=used N C+rawExtra := by
    unfold used; rw [Finset.card_filter]
    dsimp only [rawExtra]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; change v i=(if 1≤v i then 1 else 0)+(v i-1); split_ifs <;> omega
  have zero := active_last C back pos live
  have last : v (N+(C.size-1))=0 := (zero _ (by omega)).mpr (by omega)
  have ex : gateExtra=∑ j∈Finset.range (C.size-1),(v (N+j)-1) := by
    dsimp only [gateExtra]
    conv_lhs => congr; rw [show C.size=(C.size-1)+1 by omega]
    rw [Finset.sum_range_succ,last]; simp
  have endCount := Pins.tail C.size (fun j => v (N+j)) pos zero
  have all := Pins.key N C back
  have slots := Pins.slots C shape
  change (∑ j∈Finset.range C.size,(gateAt C j).inputs.length)+(Partition.neg69 C).card=C.size+C.size at slots
  change (∑ w∈Finset.range N,v w)+(∑ j∈Finset.range C.size,v (N+j))= _ at all
  have extra : surplus N C=rawExtra+gateExtra := Finset.sum_range_add _ _ _
  dsimp only [budget]; rw [extra]; omega

theorem many_count (S : Finset ℕ) (f : ℕ → ℕ) :
    (S.filter (fun w => 2≤f w)).card ≤ ∑ w∈S,(f w-1) := by
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro w _; split_ifs <;> omega

theorem special_count (N : ℕ) (C : Circuit) : (Partition.special N C).card≤budget N C := by
  classical
  unfold Partition.special budget
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ Finset.card_image_le)
  exact many_count _ _

theorem special_range (N : ℕ) (C : Circuit) : Partition.special N C ⊆ Finset.range (N+C.size) := by
  classical
  intro w hw
  rcases Finset.mem_union.mp hw with h|h
  · exact (Finset.mem_filter.mp h).1
  · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp h
    have klt : k<C.size := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact Finset.mem_range.mpr (by omega)

theorem slot_limits (N : ℕ) (C : Circuit) (shape : Partition.shapes69 C) :
    Partition.exits69 N C≤2*budget N C ∧ Partition.entries69 N C≤2*budget N C := by
  classical
  let R := Finset.range C.size
  let O := Partition.ordinary N C
  let S := Partition.special N C
  let v := Active C
  let X := R \ O
  have cardS : S.card≤budget N C := special_count N C
  have subX : X.image (fun j => N+j) ⊆ S := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨mem,absent⟩ := Finset.mem_sdiff.mp hj
    by_contra no
    exact absent (Finset.mem_filter.mpr ⟨mem,no⟩)
  have cx : X.card≤S.card := by
    have h := Finset.card_le_card subX
    have inj : Function.Injective (fun j : ℕ => N+j) := fun _ _ eq => Nat.add_left_cancel eq
    rwa [Finset.card_image_of_injective _ inj] at h
  constructor
  · change (∑ j∈X,(gateAt C j).inputs.countP (fun w => decide (w∉S)))≤2*budget N C
    calc
      _ ≤ ∑ _j∈X, 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have low : j<C.gates.length := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
        have gmem : gateAt C j∈C.gates := by rw [gateAt,List.getD_eq_getElem _ _ low]; exact List.getElem_mem low
        have le : (gateAt C j).inputs.length≤2 := by rcases shape _ gmem with h|h <;> omega
        exact (List.countP_le_length ..).trans le
      _ ≤ _ := by simp; omega
  · have inc : O⊆R := Finset.filter_subset _ _
    have sub := special_range N C
    have cap : (∑ w∈S,v w) ≤ S.card+surplus N C := by
      calc
        _ ≤ ∑ w∈S, (1+(v w-1)) := by apply Finset.sum_le_sum; intro w _; omega
        _ = S.card+∑ w∈S,(v w-1) := by simp [Finset.sum_add_distrib]
        _ ≤ _ := Nat.add_le_add_left (Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)) _
    change (∑ j∈O,(gateAt C j).inputs.countP (fun w => decide (w∈S)))≤2*budget N C
    calc
      _ ≤ ∑ j∈R, (gateAt C j).inputs.countP (fun w => decide (w∈S)) :=
        Finset.sum_le_sum_of_subset_of_nonneg inc (fun _ _ _ => Nat.zero_le _)
      _ = ∑ w∈S,v w := by
        simp_rw [←Partition.sum_reads_mask69]
        exact Finset.sum_comm
      _ ≤ _ := by have le : surplus N C ≤ budget N C := Nat.le_add_right _ _; omega

theorem union_bound (L : List (Finset ℕ)) (p : ℕ) (bound : ∀ S∈L, S.card≤p) :
    (L.toFinset.biUnion id).card≤p*L.length := by
  classical
  induction L with
  | nil => simp
  | cons S l ih =>
    have first := bound S (by simp)
    have tail := ih (fun A h => bound A (by simp [h]))
    rw [List.toFinset_cons,Finset.biUnion_insert,List.length_cons,Nat.mul_succ]
    have h := Finset.card_union_le S (l.toFinset.biUnion id)
    change (S∪l.toFinset.biUnion id).card≤_
    omega

theorem account (N : ℕ) (C : Circuit) (p c : ℕ) (shape : Partition.shapes69 C) (back : ReadsBack N C)
    (pos : 0<C.size) (last : C.output+1=N+C.size) (live : ∀ j<C.size, j+1<C.size → 0<Active C (N+j))
    (pureLimit : ∀ S, S⊆Finset.range N → Partition.tree69 N C S ∅ → S.card≤p)
    (chainLimit : ∀ S b, S⊆Finset.range N → Partition.tree69 N C S {b} → S.card≤c) :
    used N C≤(2*p+4*c+1)*budget N C+p := by
  classical
  let v := Active C
  let K := budget N C
  obtain ⟨ep,en⟩ := slot_limits N C shape
  obtain ⟨P,Q,pq,qq,_,allSets,pureTrees,chainTrees⟩ := Partition.finish69 N C shape back pos last live
  have raw {S} (mem : S∈P++Q) : S⊆Finset.range N := by
    intro w hw
    have h : w∈(P++Q).toFinset.biUnion id := Finset.mem_biUnion.mpr ⟨S,List.mem_toFinset.mpr mem,hw⟩
    rw [show (P++Q).toFinset.biUnion id=Partition.once69 N C from allSets] at h
    exact (Finset.mem_filter.mp h).1
  have pc := union_bound P p (fun S h => pureLimit S (raw (List.mem_append_left _ h)) (pureTrees S h).2)
  have qc := union_bound Q c (fun S h => by
    obtain ⟨_,b,tree⟩ := chainTrees S h
    exact chainLimit S b (raw (List.mem_append_right _ h)) tree)
  have union : (Partition.once69 N C).card ≤ (P.toFinset.biUnion id).card+(Q.toFinset.biUnion id).card := by
    rw [←allSets,List.toFinset_append,Finset.union_biUnion]
    exact Finset.card_union_le _ _
  have pp : P.length≤2*K+1 := by omega
  have cc : Q.length≤4*K := by omega
  have pl := Nat.mul_le_mul_left p pp
  have cl := Nat.mul_le_mul_left c cc
  have excess : ((Finset.range N).filter (fun i => 2≤v i)).card≤K := by
    have h := many_count (Finset.range N) v
    have sub : Finset.range N ⊆ Finset.range (N+C.size) := Finset.range_mono (Nat.le_add_right _ _)
    have s : (∑ i∈Finset.range N,(v i-1)) ≤ surplus N C :=
      Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
    have k : surplus N C≤K := Nat.le_add_right _ _
    omega
  have split : used N C=(Partition.once69 N C).card+((Finset.range N).filter (fun i => 2≤v i)).card := by
    unfold used Partition.once69
    rw [Finset.card_filter,Finset.card_filter,Finset.card_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (if 1≤v i then 1 else 0)=(if v i=1 then 1 else 0)+(if 2≤v i then 1 else 0)
    split_ifs <;> omega
  change used N C≤(2*p+4*c+1)*K+p
  rw [split]
  nlinarith

end CutLib25855

namespace CutLib25855
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

theorem raw_parts {n m : ℕ} (S : Finset ℕ) (sub : S⊆Finset.range (n+m)) :
    ∃ (R : Finset (Fin n)) (B : Finset (Fin m)),
      R.image (fun a => a.val) ∪ B.image (fun c => n+c.val)=S ∧ S.card=R.card+B.card := by
  classical
  let R := Finset.univ.filter (fun a : Fin n => a.val∈S)
  let B := Finset.univ.filter (fun c : Fin m => n+c.val∈S)
  have joined : R.image (fun a => a.val) ∪ B.image (fun c => n+c.val)=S := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with h|h
      · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_filter.mp ha).2
      · obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_filter.mp hc).2
    · intro hi
      have bound := Finset.mem_range.mp (sub hi)
      by_cases low : i<n
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨⟨i,low⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩)
      · have eq : n+(i-n)=i := by omega
        let c : Fin m := ⟨i-n,by omega⟩
        have cv : n+c.val=i := eq
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,cv ▸ hi⟩,cv⟩)
  have separate : Disjoint (R.image (fun a => a.val)) (B.image (fun c => n+c.val)) := by
    apply Finset.disjoint_left.mpr
    rintro i hi hj
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hi
    obtain ⟨c,_,hc⟩ := Finset.mem_image.mp hj
    have small := a.isLt
    change n+c.val=i at hc
    change a.val=i at ha
    omega
  refine ⟨R,B,joined,?_⟩
  rw [←joined,Finset.card_union_of_disjoint separate,Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ (show Function.Injective (fun c : Fin m => n+c.val) from
      fun _ _ eq => Fin.ext (Nat.add_left_cancel eq))]

end CutLib25855

namespace CutLib25855.Tree.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_init (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_init [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_init gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_init gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

theorem gv (N : ℕ) (C : Circuit) (hb : ReadsBack N C) (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) :
    (run C.gates x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  have hw := run_gate C.gates x j hj
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [hx, ← he] at hw
  rw [hw]
  congr 1
  exact List.map_congr_left fun i hi => ite_eq_left (hb j hj i hi)

theorem past (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (run gs x).getD i false = false :=
  List.getD_eq_default _ _ (by rw [run_length]; exact hi)

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn]
    simp [h, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp [h2, Fin.ext_iff]
      have hu : ¬ i = u.val := by omega
      by_cases hv : i = n + v.val
      · simp [hv]
      · have hv' : ¬ i - n = v.val := by omega
        simp [hu, hv, hv']
    · simp [h2]
      omega

def inside (N : ℕ) (region : Finset ℕ) (w : ℕ) : Prop := N≤w ∧ w-N∈region
def V (C : Circuit) (x : List Bool) (i : ℕ) := (run C.gates x).getD i false

structure Layout (N : ℕ) (C : Circuit) (src reg ent : Finset ℕ) (top : ℕ) : Prop where
  back : ReadsBack N C
  valid : reg ⊆ Finset.range C.size
  member : top∈reg
  one : ent.card≤1
  ports : ∀ w∈ent, w<N+top ∧ w∉src ∧ ¬inside N reg w
  interior : ∀ j∈reg, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    ∀ w∈(gateAt C j).inputs, w∈src ∨ inside N reg w ∨ w∈ent
  exterior : ∀ j<C.size, j∉reg → ∀ w∈(gateAt C j).inputs, w∉src ∧ (inside N reg w → w=N+top)
  output : C.output∉src
  visible : inside N reg C.output → C.output=N+top

variable {N top : ℕ} {C : Circuit} {src reg ent : Finset ℕ}

theorem gate_mono (g : Gate) (op : g.op=.and ∨ g.op=.or) {x y : ℕ → Bool}
    (le : ∀ i∈g.inputs, x i=true → y i=true) :
    g.op.eval (g.inputs.map x)=true → g.op.eval (g.inputs.map y)=true := by
  rcases op with op|op <;> rw [op]
  · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id]
    exact fun h i hi => le i hi (h i hi)
  · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id]
    rintro ⟨i,hi,h⟩; exact ⟨i,hi,le i hi h⟩

theorem inside_mono (L : Layout N C src reg ent top) (x y : List Bool) (hx : x.length=N) (hy : y.length=N)
    (hs : ∀ i∈src, V C x i=true → V C y i=true) (he : ∀ i∈ent, V C x i=true → V C y i=true) :
    ∀ i, inside N reg i → V C x i=true → V C y i=true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rintro ⟨ge,mem⟩
    let j := i-N
    have jmem : j∈reg := mem
    have jlen : j<C.gates.length := Finset.mem_range.mp (L.valid jmem)
    have idx : N+j=i := Nat.add_sub_of_le ge
    have vx : V C x i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C x)) := idx ▸ gv N C L.back x hx j jlen
    have vy : V C y i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C y)) := idx ▸ gv N C L.back y hy j jlen
    rw [vx,vy]
    apply gate_mono _ (L.interior j jmem).1
    intro w hw
    rcases (L.interior j jmem).2 w hw with h|h|h
    · exact hs w h
    · exact ih w (idx ▸ L.back j jlen w hw) h
    · exact he w h

theorem outside_agree (L : Layout N C src reg ent top) (x y : List Bool) (hx : x.length=N) (hy : y.length=N)
    (raw : ∀ i<N, i∉src → V C x i=V C y i) (cap : ℕ)
    (ht : N+top<cap → V C x (N+top)=V C y (N+top)) :
    ∀ i<cap, i∉src → ¬inside N reg i → V C x i=V C y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro bound hs hi
    by_cases low : i<N
    · exact raw i low hs
    by_cases far : N+C.gates.length ≤ i
    · have a := past C.gates x i (by rwa [hx])
      have b := past C.gates y i (by rwa [hy])
      exact a.trans b.symm
    let j := i-N
    have jlen : j<C.gates.length := by dsimp [j]; omega
    have idx : N+j=i := by dsimp [j]; omega
    have jr : j∉reg := fun h => hi ⟨by omega,h⟩
    have vx : V C x i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C x)) := idx ▸ gv N C L.back x hx j jlen
    have vy : V C y i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C y)) := idx ▸ gv N C L.back y hy j jlen
    rw [vx,vy]; congr 1
    apply List.map_congr_left
    intro w hw
    have smaller : w < i := idx ▸ L.back j jlen w hw
    have cut := L.exterior j jlen jr w hw
    by_cases h : inside N reg w
    · have eq := cut.2 h
      rw [eq]; exact ht (by omega)
    · exact ih w smaller (by omega) cut.1 h

noncomputable def port (ent : Finset ℕ) (v : ℕ → Bool) : Bool := decide (∃ i∈ent, v i=true)

theorem port_le (one : ent.card≤1) (x y : ℕ → Bool) (h : port ent x=true → port ent y=true) :
    ∀ i∈ent, x i=true → y i=true := by
  classical
  intro i hi xi
  have a : port ent x=true := by simpa only [port,decide_eq_true_eq] using (show ∃ j∈ent, x j=true from ⟨i,hi,xi⟩)
  have b := h a
  obtain ⟨j,hj,yj⟩ := of_decide_eq_true b
  exact (Finset.card_le_one.mp one j hj i hi) ▸ yj

noncomputable def low {β : Type} (bad : Finset β) (bit out : β → Bool) :=
  decide (∃ c, c∉bad ∧ bit c=false ∧ out c=true)
noncomputable def high {β : Type} (bad : Finset β) (out : β → Bool) :=
  decide (∃ c, c∉bad ∧ out c=true)

theorem low_high {β : Type} (bad : Finset β) (bit out : β → Bool) :
    low bad bit out=true → high bad out=true := by
  simp only [low,high,decide_eq_true_eq]
  rintro ⟨c,h,_,v⟩; exact ⟨c,h,v⟩

theorem reproduce {β : Type} (bad : Finset β) (bit out : β → Bool)
    (mono : ∀ c∉bad, ∀ c'∉bad, (bit c=true → bit c'=true) → out c=true → out c'=true)
    (c : β) (hc : c∉bad) : out c = if bit c then high bad out else low bad bit out := by
  apply Bool.eq_iff_iff.mpr
  cases h : bit c with
  | false =>
    simp only [Bool.false_eq_true,ite_false,low,decide_eq_true_eq]
    constructor
    · exact fun yes => ⟨c,hc,h,yes⟩
    · rintro ⟨w,hw,h0,yes⟩; exact mono w hw c hc (by simp [h0]) yes
  | true =>
    simp only [ite_true,high,decide_eq_true_eq]
    constructor
    · exact fun yes => ⟨c,hc,yes⟩
    · rintro ⟨w,hw,yes⟩; exact mono w hw c hc (fun _ => h) yes

theorem pairs : ∀ a b c d : Bool, (a=true → b=true) → (c=true → d=true) →
    a.toNat+b.toNat=c.toNat+d.toNat → a=c ∧ b=d := by decide

theorem side_bound {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β]
    (L : Layout N C src reg ent top) (S : Finset α) (bad : Finset β)
    (A : α → β → Bool) (xs : α → β → List Bool) (len : ∀ a c, (xs a c).length=N)
    (sem : ∀ a c, C.eval (xs a c)=A a c)
    (outside : ∀ a∈S, ∀ b∈S, ∀ c∉bad, ∀ i<N, i∉src → V C (xs a c) i=V C (xs b c) i)
    (privatePins : ∀ a∈S, ∀ c∉bad, ∀ c'∉bad, ∀ i∈src, V C (xs a c) i=V C (xs a c') i)
    : (S.image (fun a => (Finset.univ \ bad).filter (fun c => A a c=true))).card ≤ 2+ent.card := by
  classical
  let bit := fun a c => port ent (V C (xs a c))
  let out := fun a c => V C (xs a c) (N+top)
  have imem : inside N reg (N+top) := ⟨by omega,by simpa using L.member⟩
  have localEval (a) (ha : a∈S) (c) (hc : c∉bad) :
      out a c = if bit a c then high bad (out a) else low bad (bit a) (out a) := by
    apply reproduce
    · intro q hq w hw le
      exact inside_mono L _ _ (len a q) (len a w)
        (fun i hi v => (privatePins a ha q hq w hw i hi) ▸ v) (port_le L.one _ _ le) _ imem
    · exact hc
  have sameBit (a) (ha : a∈S) (b) (hb : b∈S) (c) (hc : c∉bad) : bit a c=bit b c := by
    apply Bool.eq_iff_iff.mpr
    simp only [bit,port,decide_eq_true_eq]
    have atEntry (i) (hi : i∈ent) : V C (xs a c) i=V C (xs b c) i :=
      outside_agree L _ _ (len a c) (len b c) (outside a ha b hb c hc) (N+top) (by omega)
        i (L.ports i hi).1 (L.ports i hi).2.1 (L.ports i hi).2.2
    constructor <;> rintro ⟨i,hi,yes⟩
    · exact ⟨i,hi,(atEntry i hi) ▸ yes⟩
    · exact ⟨i,hi,(atEntry i hi).symm ▸ yes⟩
  let lo := fun a => low bad (bit a) (out a)
  let hi := fun a => high bad (out a)
  let code := fun a => if ent=∅ then (lo a).toNat else (lo a).toNat+(hi a).toNat
  have maxBit (b : Bool) : b.toNat≤1 := by cases b <;> decide
  have bound (a : α) : code a<2+ent.card := by
    have l := maxBit (lo a); have h := maxBit (hi a)
    dsimp only [code]
    split_ifs with empty
    · omega
    · have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty); omega
  let profile := fun a : α => (⟨code a,bound a⟩ : Fin (2+ent.card))
  let face := fun a => (Finset.univ \ bad).filter (fun c => A a c=true)
  have same (a) (ha : a∈S) (b) (hb : b∈S) (eq : profile a=profile b) : face a=face b := by
    have keys : code a=code b := congrArg Fin.val eq
    have outsideCol (c : β) (hc : c∉bad) : A a c=A b c := by
      have agreePort := sameBit a ha b hb c hc
      have agreeTop : out a c=out b c := by
        rw [localEval a ha c hc,localEval b hb c hc,agreePort]
        by_cases empty : ent=∅
        · have zero : bit b c=false := by simp [bit,port,empty]
          simp only [zero,Bool.false_eq_true,ite_false]
          have k : (lo a).toNat=(lo b).toNat := by simpa only [code,empty,ite_true] using keys
          exact (by cases h : lo a <;> cases j : lo b <;> simp_all : lo a=lo b)
        · have k : (lo a).toNat+(hi a).toNat=(lo b).toNat+(hi b).toNat := by simpa only [code,empty,ite_false] using keys
          obtain ⟨lowEq,highEq⟩ := pairs _ _ _ _ (low_high bad (bit a) (out a)) (low_high bad (bit b) (out b)) k
          split <;> assumption
      rw [←sem,←sem]
      change V C (xs a c) C.output = V C (xs b c) C.output
      by_cases interior : inside N reg C.output
      · rw [L.visible interior]; exact agreeTop
      · exact outside_agree L _ _ (len a c) (len b c) (outside a ha b hb c hc) (C.output+1)
          (fun _ => agreeTop) _ (by omega) L.output interior
    ext c
    by_cases mem : c∈bad
    · simp [face,mem]
    · simp [face,mem,outsideCol c mem]
  let decode (z : Fin (2+ent.card)) := if h : ∃ a∈S, profile a=z then face h.choose else ∅
  have sub : S.image face ⊆ Finset.univ.image decode := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨profile a,Finset.mem_univ _,?_⟩
    have h : ∃ b∈S, profile b=profile a := ⟨a,ha,rfl⟩
    simpa only [decode,dif_pos h] using same h.choose h.choose_spec.1 a ha h.choose_spec.2
  exact (Finset.card_le_card sub).trans ((Finset.card_image_le).trans (by simp))

theorem axis {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β]
    (L : Layout N C src reg ent top) (S : Finset α) (bad : Finset β)
    (A : α → β → Bool) (xs : α → β → List Bool) (len : ∀ a c, (xs a c).length=N)
    (sem : ∀ a c, C.eval (xs a c)=A a c)
    (left : α → ℕ) (right : β → ℕ) (ltL : ∀ a, left a<N) (ltR : ∀ b, right b<N)
    (injR : Function.Injective right) (disjoint : ∀ a b, left a≠right b)
    (hs : src=S.image left ∪ bad.image right)
    (atRaw : ∀ a c i, i<N → V C (xs a c) i = decide (i=left a ∨ i=right c))
    : (S.image (fun a => (Finset.univ \ bad).filter (fun c => A a c=true))).card ≤ 2+ent.card := by
  apply side_bound L S bad A xs len sem
  · intro a ha b hb c _ i hi off
    have na : i≠left a := fun eq => off (hs ▸ eq ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem left ha))
    have nb : i≠left b := fun eq => off (hs ▸ eq ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem left hb))
    simp [atRaw a c i hi,atRaw b c i hi,na,nb]
  · intro a _ c hc c' hc' i hi
    rw [hs] at hi
    rcases Finset.mem_union.mp hi with l|r
    · obtain ⟨a',_,rfl⟩ := Finset.mem_image.mp l
      simp [atRaw,ltL,disjoint]
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp r
      have p : right b≠right c := fun eq => hc (injR eq ▸ hb)
      have q : right b≠right c' := fun eq => hc' (injR eq ▸ hb)
      simp [atRaw,ltR,p,q]

theorem both_axes {n m : ℕ} (G : Fin n → Fin m → Bool) (C : Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (reg ent : Finset ℕ) (top : ℕ)
    (L : Layout (n+m) C (R.image Fin.val ∪ B.image (fun j => n+j.val)) reg ent top)
    (rep : Represents G C) :
    (R.image (fun a => (Finset.univ \ B).filter (fun c => G a c=true))).card≤2+ent.card ∧
    (B.image (fun c => (Finset.univ \ R).filter (fun a => G a c=true))).card≤2+ent.card := by
  classical
  let N := n+m
  have lowVal (u : Fin n) (v : Fin m) (i : ℕ) (hi : i<N) :
      V C (oneEach u v) i=decide (i=u.val ∨ i=n+v.val) := by
    change (run C.gates (oneEach u v)).getD i false=_
    rw [run_input _ _ _ (by rwa [oneEach_length]),oneEach_getD]
  have hr (i : Fin n) : i.val<N := by dsimp [N]; have := i.isLt; omega
  have hc (j : Fin m) : n+j.val<N := by dsimp [N]; have := j.isLt; omega
  have dis (i : Fin n) (j : Fin m) : i.val≠n+j.val := by have := i.isLt; omega
  constructor
  · exact axis L R B G oneEach oneEach_length rep (fun i => i.val) (fun j => n+j.val)
      hr hc (fun _ _ eq => Fin.ext (Nat.add_left_cancel eq)) dis rfl lowVal
  · exact axis L B R (fun j i => G i j) (fun j i => oneEach i j) (fun j i => oneEach_length i j)
      (fun j i => rep i j) (fun j => n+j.val) (fun i => i.val) hc hr Fin.val_injective
      (fun j i => (dis i j).symm) (Finset.union_comm _ _)
      (fun j i k hk => by simpa only [or_comm] using lowVal i j k hk)

end CutLib25855.Tree.Cut

namespace CutLib25855.Tree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

theorem only_reader (C : Circuit) (i j k : ℕ) (hj : j < C.size) (hk : k < C.size)
    (hc : readsIn C (Finset.range C.size) i = 1)
    (hij : i ∈ (gateAt C j).inputs) (hik : i ∈ (gateAt C k).inputs) : j = k := by
  by_contra h
  have hs : ({j, k} : Finset ℕ) ⊆ Finset.range C.size := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
  have hsum : (∑ g ∈ ({j, k} : Finset ℕ), (gateAt C g).inputs.count i) ≤
      readsIn C (Finset.range C.size) i :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair h, hc] at hsum
  have ha := List.count_pos_iff.mpr hij
  have hb := List.count_pos_iff.mpr hik
  omega

def wireSet (N : ℕ) (S reg : Finset ℕ) := S ∪ reg.image (fun j => N+j)
def edge (N : ℕ) (C : Circuit) (reg : Finset ℕ) (w z : ℕ) : Prop :=
  ∃ j∈reg, z=N+j ∧ w∈(gateAt C j).inputs
abbrev reach (N : ℕ) (C : Circuit) (reg : Finset ℕ) := Relation.ReflTransGen (edge N C reg)
noncomputable def leaves {α : Type} (N : ℕ) (C : Circuit) (reg : Finset ℕ) (f : α → ℕ)
    (S : Finset α) (z : ℕ) := S.filter fun a => reach N C reg (f a) z
noncomputable def stages (N : ℕ) (C : Circuit) (reg : Finset ℕ) (z : ℕ) :=
  reg.filter fun j => reach N C reg (N+j) z

structure Tree (N : ℕ) (C : Circuit) (sources reg : Finset ℕ) (root : ℕ) (ext : Finset ℕ) : Prop where
  rawLt : ∀ i∈sources, i<N
  back : ReadsBack N C
  valid : reg ⊆ Finset.range C.size
  rootMem : root∈wireSet N sources reg
  gates : ∀ j∈reg, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀ i∈(gateAt C j).inputs, i∈wireSet N sources reg ∨ i∈ext
  portData : ∀ w∈ext, w∉wireSet N sources reg ∧ w<root ∧ readsIn C reg w=1
  endReads : readsIn C reg root=0
  uniq : ∀ w∈wireSet N sources reg, w≠root →
    readsIn C reg w=1 ∧ readsIn C (Finset.range C.size) w=1 ∧ C.output≠w

variable {N root : ℕ} {C : Circuit} {s r ext : Finset ℕ}

theorem tail_step {a b : ℕ} (h : reach N C r a b) (ne : a≠b) :
    ∃ w, reach N C r a w ∧ edge N C r w b := by
  cases h with
  | refl => contradiction
  | tail h last => exact ⟨_,h,last⟩

theorem head_step {a b : ℕ} (h : reach N C r a b) (ne : a≠b) :
    ∃ w, edge N C r a w ∧ reach N C r w b := by
  induction h with
  | refl => contradiction
  | @tail b c h last ih =>
    by_cases zero : a=b
    · subst b; exact ⟨c,last,.refl⟩
    · obtain ⟨w,e,p⟩ := ih zero
      exact ⟨w,e,p.tail last⟩

theorem edge_lt (T : Tree N C s r root ext) {a b : ℕ} (h : edge N C r a b) : a<b := by
  obtain ⟨j,hj,rfl,hr⟩ := h
  exact T.back j (Finset.mem_range.mp (T.valid hj)) a hr

theorem wire_bound (T : Tree N C s r root ext) {w : ℕ} (h : w∈wireSet N s r) : w<N+C.size := by
  rcases Finset.mem_union.mp h with h|h
  · have := T.rawLt w h; omega
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    have := Finset.mem_range.mp (T.valid hj); omega

theorem exists_reader {reg : Finset ℕ} {w : ℕ} (pos : 0<readsIn C reg w) :
    ∃ j∈reg,w∈(gateAt C j).inputs := by
  classical
  by_contra no
  have z : readsIn C reg w=0 := Finset.sum_eq_zero fun j hj =>
    List.count_eq_zero.mpr (fun h => no ⟨j,hj,h⟩)
  omega

theorem root_ends (T : Tree N C s r root ext) {j : ℕ} (hj : j∈r) : root∉(gateAt C j).inputs := by
  intro h
  have le : (gateAt C j).inputs.count root≤readsIn C r root :=
    Finset.single_le_sum (f:=fun j => (gateAt C j).inputs.count root) (fun _ _ => Nat.zero_le _) hj
  have pos := List.count_pos_iff.mpr h
  have z := T.endReads; omega

theorem to_root (T : Tree N C s r root ext) (w : ℕ) (hw : w∈wireSet N s r) : reach N C r w root := by
  by_cases terminal : w=root
  · subst w; exact .refl
  · obtain ⟨once,_,_⟩ := T.uniq w hw terminal
    obtain ⟨j,hj,reads⟩ := exists_reader (show 0<readsIn C r w by omega)
    have e : edge N C r w (N+j) := ⟨j,hj,rfl,reads⟩
    have member : N+j∈wireSet N s r := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
    exact (Relation.ReflTransGen.single e).trans (to_root T _ member)
termination_by N+C.size-w
decreasing_by
  have := edge_lt T e
  have := wire_bound T member
  omega

theorem no_escape (T : Tree N C s r root ext) {w z j : ℕ} (hw : w∈wireSet N s r)
    (path : reach N C r w z) (neq : w≠z) (hj : j<C.size) (hr : w∈(gateAt C j).inputs) :
    j∈stages N C r z := by
  obtain ⟨next,⟨k,hk,rfl,read⟩,p⟩ := head_step path neq
  have nonroot : w≠root := fun e => root_ends T hk (e ▸ read)
  have eq := only_reader C w j k hj (Finset.mem_range.mp (T.valid hk)) (T.uniq w hw nonroot).2.1 hr read
  subst j; exact Finset.mem_filter.mpr ⟨hk,p⟩

theorem hidden (T : Tree N C s r root ext) {w z : ℕ} (hw : w∈wireSet N s r)
    (path : reach N C r w z) (neq : w≠z) : C.output≠w := by
  obtain ⟨next,⟨j,hj,_,read⟩,_⟩ := head_step path neq
  exact (T.uniq w hw (fun e => root_ends T hj (e ▸ read))).2.2

theorem path_le (T : Tree N C s r root ext) {a b : ℕ} (p : reach N C r a b) : a≤b := by
  induction p with
  | refl => rfl
  | tail h last ih => exact ih.trans (edge_lt T last).le

theorem at_most_one (T : Tree N C s r root ext) {v j : ℕ} (hj : j∈r)
    (h : v∈(gateAt C j).inputs) : readsIn C r v≤1 := by
  rcases (T.gates j hj).2.2 v h with w|e
  · by_cases terminal : v=root
    · subst v; rw [T.endReads]; decide
    · exact (T.uniq v w terminal).1.le
  · exact (T.portData v e).2.2.le

theorem deterministic (T : Tree N C s r root ext) {a b c : ℕ} (ab : edge N C r a b)
    (ac : edge N C r a c) : b=c := by
  obtain ⟨j,jr,rfl,aj⟩ := ab
  obtain ⟨k,kr,rfl,ak⟩ := ac
  congr 1
  by_contra ne
  have sub : ({j,k} : Finset ℕ) ⊆ r := by
    intro i hi; simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    exact hi.elim (fun h => h ▸ jr) (fun h => h ▸ kr)
  have sum : (∑ g∈({j,k} : Finset ℕ), (gateAt C g).inputs.count a) ≤ readsIn C r a :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair ne] at sum
  have p := List.count_pos_iff.mpr aj; have q := List.count_pos_iff.mpr ak
  have bound := at_most_one T jr aj; omega

theorem comparable (T : Tree N C s r root ext) {u a b : ℕ} (pa : reach N C r u a)
    (pb : reach N C r u b) : reach N C r a b ∨ reach N C r b a := by
  by_cases ua : u=a
  · subst a; exact Or.inl pb
  by_cases ub : u=b
  · subst b; exact Or.inr pa
  obtain ⟨w,uw,wa⟩ := head_step pa ua
  obtain ⟨v,uv,vb⟩ := head_step pb ub
  have eq := deterministic T uw uv
  subst v
  exact comparable T wa vb
termination_by N+C.size-u
decreasing_by
  have lt := edge_lt T uw
  obtain ⟨j,hj,eq,_⟩ := uw
  have := Finset.mem_range.mp (T.valid hj)
  omega

theorem distinct_operands (T : Tree N C s r root ext) {k a b : ℕ} (hk : k∈r)
    (ops : (gateAt C k).inputs=[a,b]) : a≠b := by
  intro eq; subst b
  have h : a∈(gateAt C k).inputs := by simp [ops]
  have two : (gateAt C k).inputs.count a=2 := by simp [ops]
  have le : (gateAt C k).inputs.count a ≤ readsIn C r a :=
    Finset.single_le_sum (f:=fun j => (gateAt C j).inputs.count a) (fun _ _ => Nat.zero_le _) hk
  have cap := at_most_one T hk h; omega

theorem branch (T : Tree N C s r root ext) {a b z : ℕ} (az : edge N C r a z)
    (bz : edge N C r b z) (diff : a≠b) (u : ℕ) : ¬reach N C r u a ∨ ¬reach N C r u b := by
  by_contra two
  push_neg at two
  have no {x y : ℕ} (xz : edge N C r x z) (yz : edge N C r y z) (xy : x≠y) (p : reach N C r x y) : False := by
    obtain ⟨w,xw,wy⟩ := head_step p xy
    have eq := deterministic T xz xw
    have le := path_le T wy; have lt := edge_lt T yz; omega
  rcases comparable T two.1 two.2 with h|h
  · exact no az bz diff h
  · exact no bz az diff.symm h

theorem binary_list {α : Type} (l : List α) (h : l.length=2) : ∃ a b, l=[a,b] := by
  obtain _|⟨a,l⟩ := l <;> simp_all
  obtain _|⟨b,l⟩ := l <;> simp_all

end CutLib25855.Tree

namespace CutLib25855.Tree.Shape

abbrev Signal := Finset ℕ → Bool
def pair (f : Signal) (a c : ℕ) : Prop :=
  f {a}=false ∧ f {c}=false ∧ f {a,c}=true
def Closed (P : ℕ → ℕ → Prop) := ∀ a b x y, P a x → P b x → P b y → P a y
theorem yes_or (a b : Bool) : (a || b)=true ↔ a=true ∨ b=true := by cases a <;> cases b <;> decide
theorem yes_and (a b : Bool) : (a && b)=true ↔ a=true ∧ b=true := by cases a <;> cases b <;> decide
structure Model (f : Signal) (A : Set ℕ) : Prop where
  mono : ∀ U V : Finset ℕ, U ⊆ V → f U=true → f V=true
  agree : ∀ U V : Finset ℕ, (∀ i∈A, i∈U ↔ i∈V) → f U=f V
  rect : Closed (pair f)

theorem widen {f : Signal} {A B : Set ℕ} (F : Model f A) (h : A⊆B) : Model f B :=
  ⟨F.mono,fun U V e => F.agree U V (fun i hi => e i (h hi)),F.rect⟩

theorem fixed (v : Bool) : Model (fun _ => v) ∅ := by
  refine ⟨fun _ _ _ h => h,fun _ _ _ => rfl,?_⟩
  intro a b x y first _ _
  exact False.elim (Bool.false_ne_true (first.1.symm.trans first.2.2))

theorem input (i : ℕ) : Model (fun U => decide (i∈U)) {i} := by
  classical
  constructor
  · intro U V sub yes; exact decide_eq_true (sub (of_decide_eq_true yes))
  · intro U V h; apply Bool.eq_iff_iff.mpr; simpa only [decide_eq_true_eq] using h i (Set.mem_singleton i)
  · intro a b x y p _ _
    obtain ⟨l,r,z⟩ := p
    simp only [decide_eq_false_iff_not,Finset.mem_singleton,decide_eq_true_eq,
      Finset.mem_insert] at l r z
    exact False.elim (z.elim l r)

theorem singleton_agree {f : Signal} {A : Set ℕ} (F : Model f A) {a x : ℕ} (h : x∉A) :
    f {a,x}=f {a} := by
  apply F.agree
  intro i hi
  have ne : i≠x := fun eq => h (eq ▸ hi)
  simp [ne]

theorem absent {f : Signal} {A : Set ℕ} (F : Model f A) {a : ℕ} (h : a∉A) : f {a}=f ∅ := by
  apply F.agree
  intro i hi
  have ne : i≠a := fun eq => h (eq ▸ hi)
  simp [ne]

theorem endpoints {f : Signal} {A : Set ℕ} (F : Model f A) {a x : ℕ} (p : pair f a x) : a∈A ∧ x∈A := by
  constructor
  · by_contra h
    have e : f {a,x}=f {x} := by rw [Finset.pair_comm]; exact singleton_agree F h
    exact Bool.false_ne_true (p.2.1.symm.trans (e.symm.trans p.2.2))
  · by_contra h
    exact Bool.false_ne_true (p.1.symm.trans ((singleton_agree F h).symm.trans p.2.2))

theorem combine {P Q : ℕ → ℕ → Prop} (p : Closed P) (q : Closed Q)
    (row : ∀ i x y, P i x → Q i y → False) (col : ∀ a b x, P a x → Q b x → False) :
    Closed (fun i j => P i j ∨ Q i j) := by
  intro a b x y ax bx byy
  rcases ax with h|h
  · rcases bx with h2|h2
    · rcases byy with h3|h3
      · exact Or.inl (p _ _ _ _ h h2 h3)
      · exact False.elim (row _ _ _ h2 h3)
    · exact False.elim (col _ _ _ h h2)
  · rcases bx with h2|h2
    · exact False.elim (col _ _ _ h2 h)
    · rcases byy with h3|h3
      · exact False.elim (row _ _ _ h3 h2)
      · exact Or.inr (q _ _ _ _ h h2 h3)

theorem or_model {f g : Signal} {A B : Set ℕ} (F : Model f A) (H : Model g B)
    (dis : ∀ i∈A, i∉B) : Model (fun U => f U || g U) (A∪B) := by
  refine ⟨?_,?_,?_⟩
  · intro U V sub h
    simp only [Bool.or_eq_true] at h ⊢
    exact h.imp (F.mono U V sub) (H.mono U V sub)
  · intro U V h
    rw [F.agree U V (fun i hi => h i (Or.inl hi)),H.agree U V (fun i hi => h i (Or.inr hi))]
  · have liftPair {a x} (p : pair (fun U => f U || g U) a x) : pair f a x ∨ pair g a x := by
      obtain ⟨pa,px,pax⟩ := p
      simp only [Bool.or_eq_false_iff] at pa px
      simp only [Bool.or_eq_true] at pax
      exact pax.imp (fun z => ⟨pa.1,px.1,z⟩) (fun z => ⟨pa.2,px.2,z⟩)
    have closed := combine F.rect H.rect
      (fun i x y l r => dis i (endpoints F l).1 (endpoints H r).1)
      (fun a b x l r => dis x (endpoints F l).2 (endpoints H r).2)
    intro a b x y ax bx byy
    refine ⟨ax.1,byy.2.1,?_⟩
    apply (yes_or _ _).mpr
    exact (closed a b x y (liftPair ax) (liftPair bx) (liftPair byy)).imp (fun h => h.2.2) (fun h => h.2.2)

theorem hits {f : Signal} {A : Set ℕ} (F : Model f A) (base : f ∅=false)
    {a x} (h : f {a,x}=true) : a∈A ∨ x∈A := by
  by_contra! miss
  have z := (singleton_agree F miss.2).trans ((absent F miss.1).trans base)
  exact Bool.false_ne_true (z.symm.trans h)

theorem and_model {f g : Signal} {A B : Set ℕ} (F : Model f A) (H : Model g B)
    (dis : ∀ i∈A, i∉B) : Model (fun U => f U && g U) (A∪B) := by
  have constant {v : Signal} {S : Set ℕ} (M : Model v S) (h : v ∅=true) (U) : v U=true :=
    M.mono ∅ U (Finset.empty_subset _) h
  cases bf : f ∅ with
  | true =>
    have eq : (fun U => f U && g U)=g := by funext U; simp [constant F bf U]
    rw [eq]; exact widen H (fun _ h => Or.inr h)
  | false =>
    cases bg : g ∅ with
    | true =>
      have eq : (fun U => f U && g U)=f := by funext U; simp [constant H bg U]
      rw [eq]; exact widen F (fun _ h => Or.inl h)
    | false =>
      have unique (i) (p : f {i}=true) (q : g {i}=true) : False := by
        have mem {v : Signal} {S : Set ℕ} (M : Model v S) (z : v ∅=false) (t : v {i}=true) : i∈S := by
          by_contra no; exact Bool.false_ne_true (z.symm.trans ((absent M no).symm.trans t))
        exact dis i (mem F bf p) (mem H bg q)
      let P := fun i j : ℕ => f {i}=true ∧ g {j}=true
      let Q := fun i j : ℕ => g {i}=true ∧ f {j}=true
      have pc : Closed P := fun _ _ _ _ ax _ byy => ⟨ax.1,byy.2⟩
      have qc : Closed Q := fun _ _ _ _ ax _ byy => ⟨ax.1,byy.2⟩
      have closed := combine pc qc (fun i _ _ p q => unique i p.1 q.1) (fun _ _ j p q => unique j q.2 p.2)
      have classify {a x} (h : pair (fun U => f U && g U) a x) : P a x ∨ Q a x := by
        obtain ⟨_,_,hit⟩ := h
        obtain ⟨l,r⟩ := (yes_and _ _).mp hit
        have slice {v : Signal} {S : Set ℕ} (M : Model v S) {i j : ℕ} (ni : i∉S) (vij : v {i,j}=true) :
            v {j}=true := by
          rw [Finset.pair_comm,singleton_agree M ni] at vij
          exact vij
        rcases hits F bf l with aA|xA
        · rcases hits H bg r with aB|xB
          · exact False.elim (dis a aA aB)
          · exact Or.inl ⟨(singleton_agree F (fun h => dis x h xB)).symm.trans l,slice H (dis a aA) r⟩
        · rcases hits H bg r with aB|xB
          · exact Or.inr ⟨(singleton_agree H (dis x xA)).symm.trans r,slice F (fun h => dis a h aB) l⟩
          · exact False.elim (dis x xA xB)
      refine ⟨?_,?_,?_⟩
      · intro U V sub h
        obtain ⟨l,r⟩ := (yes_and _ _).mp h
        exact (yes_and _ _).mpr ⟨F.mono U V sub l,H.mono U V sub r⟩
      · intro U V h
        rw [F.agree U V (fun i hi => h i (Or.inl hi)),H.agree U V (fun i hi => h i (Or.inr hi))]
      · intro a b x y ax bx byy
        refine ⟨ax.1,byy.2.1,(yes_and _ _).mpr ?_⟩
        have subL : ({a} : Finset ℕ)⊆{a,y} := by simp
        have subR : ({y} : Finset ℕ)⊆{a,y} := by simp
        rcases closed a b x y (classify ax) (classify bx) (classify byy) with h|h
        · exact ⟨F.mono _ _ subL h.1,H.mono _ _ subR h.2⟩
        · exact ⟨F.mono _ _ subR h.2,H.mono _ _ subL h.1⟩

end CutLib25855.Tree.Shape

namespace CutLib25855.Tree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
variable {N root : ℕ} {C : Circuit} {s r e : Finset ℕ}

theorem whole_layout (T : Tree N C s r root e) (one : e.card≤1) {k : ℕ}
    (hk : k∈r) (eq : root=N+k) : Cut.Layout N C s r e k := by
  have insideWire {w} (h : Cut.inside N r w) : w∈wireSet N s r := by
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,h.2,Nat.add_sub_of_le h.1⟩)
  have privateRead {w j} (h : w∈wireSet N s r) (ne : w≠root) (hj : j<C.size)
      (read : w∈(gateAt C j).inputs) : j∈r :=
    (Finset.mem_filter.mp (no_escape T h (to_root T w h) ne hj read)).1
  refine ⟨T.back,T.valid,hk,one,?_,?_,?_,?_,?_⟩
  · intro w hw
    obtain ⟨away,low,_⟩ := T.portData w hw
    exact ⟨eq ▸ low,fun hs => away (Finset.mem_union_left _ hs),fun h => away (insideWire h)⟩
  · intro j hj
    refine ⟨(T.gates j hj).1,?_⟩
    intro w hw
    rcases (T.gates j hj).2.2 w hw with a|b
    · rcases Finset.mem_union.mp a with hs|hr
      · exact Or.inl hs
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
        exact Or.inr (Or.inl ⟨by omega,by simpa using hi⟩)
    · exact Or.inr (Or.inr b)
  · intro j hj out w hw
    constructor
    · intro hs
      have low := T.rawLt w hs
      exact out (privateRead (Finset.mem_union_left _ hs) (by omega) hj hw)
    · intro within
      by_contra ne
      exact out (privateRead (insideWire within) (fun h => ne (h.trans eq)) hj hw)
  · intro hs
    have low := T.rawLt _ hs
    exact (T.uniq _ (Finset.mem_union_left _ hs) (by omega)).2.2 rfl
  · intro inside
    by_contra ne
    exact (T.uniq _ (insideWire inside) (fun h => ne (h.trans eq))).2.2 rfl

def sample (N : ℕ) (S U : Finset ℕ) : List Bool :=
  List.ofFn fun i : Fin N => decide (i.val∈S ∧ i.val∈U)
theorem sample_length (N : ℕ) (S U : Finset ℕ) : (sample N S U).length=N := by simp [sample]
theorem sample_read (N : ℕ) (S U : Finset ℕ) (i : ℕ) (h : i<N) :
    (sample N S U).getD i false=decide (i∈S ∧ i∈U) := by
  simp [sample,List.getD_eq_getElem?_getD,List.getElem?_ofFn,h]
def sig (N : ℕ) (C : Circuit) (s : Finset ℕ) (w : ℕ) (U : Finset ℕ) :=
  Cut.V C (sample N s U) w
theorem sig_raw {i : ℕ} (low : i<N) (U : Finset ℕ) :
    sig N C s i U=decide (i∈s ∧ i∈U) := by
  change (Cut.run C.gates (sample N s U)).getD i false=_
  rw [Cut.run_input _ _ _ (by rwa [sample_length]),sample_read _ _ _ _ low]

theorem raw_same (U V : Finset ℕ) (i : ℕ) (low : i<N) (away : i∉s) :
    Cut.V C (sample N s U) i=Cut.V C (sample N s V) i := by
  change sig _ _ _ _ _=sig _ _ _ _ _
  rw [sig_raw low,sig_raw low]; simp [away]

theorem port_value {k : ℕ} (L : Cut.Layout N C s r e k) {w : ℕ} (hw : w∈e) (U : Finset ℕ) :
    sig N C s w U=sig N C s w ∅ := by
  exact Cut.outside_agree L _ _ (sample_length _ _ _) (sample_length _ _ _) (raw_same U ∅)
    (N+k) (by omega) w (L.ports w hw).1 (L.ports w hw).2.1 (L.ports w hw).2.2

theorem readout {k : ℕ} (L : Cut.Layout N C s r e k) :
    ∃ out : Bool → Bool, ∀ U, sig N C s C.output U=out (sig N C s (N+k) U) := by
  classical
  let head := sig N C s (N+k)
  let endVal := sig N C s C.output
  have single (U V) (h : head U=head V) : endVal U=endVal V := by
    by_cases inner : Cut.inside N r C.output
    · simpa only [endVal,L.visible inner] using h
    · exact Cut.outside_agree L _ _ (sample_length _ _ _) (sample_length _ _ _) (raw_same U V)
        (C.output+1) (fun _ => h) _ (by omega) L.output inner
  let out (b) := if h : ∃ U, head U=b then endVal h.choose else false
  refine ⟨out,?_⟩
  intro U
  have h : ∃ V, head V=head U := ⟨U,rfl⟩
  change endVal U=out (head U)
  simpa only [out,dif_pos h] using single U h.choose h.choose_spec.symm

def support (N : ℕ) (C : Circuit) (s r : Finset ℕ) (w : ℕ) : Set ℕ :=
  {i | i∈s ∧ reach N C r i w}

theorem structural (T : Tree N C s r root e) {k : ℕ} (L : Cut.Layout N C s r e k)
    (w : ℕ) : w∈wireSet N s r ∨ w∈e → Shape.Model (sig N C s w) (support N C s r w) := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rintro (hw|port)
    · rcases Finset.mem_union.mp hw with raw|gateMem
      · have eq : sig N C s w=(fun U => decide (w∈U)) := by
          funext U; simp [sig_raw (T.rawLt w raw),raw]
        rw [eq]
        apply Shape.widen (Shape.input w)
        intro u hu
        obtain rfl : u=w := Set.mem_singleton_iff.mp hu
        exact ⟨raw,.refl⟩
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp gateMem
        obtain ⟨a,b,ops⟩ := binary_list _ (T.gates j hj).2.1
        have ha : a∈(gateAt C j).inputs := by simp [ops]
        have hb : b∈(gateAt C j).inputs := by simp [ops]
        have len := Finset.mem_range.mp (T.valid hj)
        have A := ih a (T.back j len a ha) ((T.gates j hj).2.2 a ha)
        have B := ih b (T.back j len b hb) ((T.gates j hj).2.2 b hb)
        have ea : edge N C r a (N+j) := ⟨j,hj,rfl,ha⟩
        have eb : edge N C r b (N+j) := ⟨j,hj,rfl,hb⟩
        have dis (i) (la : i∈support N C s r a) (lb : i∈support N C s r b) : False :=
          (branch T ea eb (distinct_operands T hj ops) i).elim (fun no => no la.2) (fun no => no lb.2)
        have sub : support N C s r a ∪ support N C s r b ⊆ support N C s r (N+j) := by
          intro i hi
          rcases hi with l|h
          · exact ⟨l.1,l.2.tail ea⟩
          · exact ⟨h.1,h.2.tail eb⟩
        have val U : sig N C s (N+j) U=(gateAt C j).op.eval [sig N C s a U,sig N C s b U] := by
          have v := Cut.gv N C T.back (sample N s U) (sample_length _ _ _) j len
          simpa only [sig,Cut.V,ops,List.map_cons,List.map_nil] using v
        rcases (T.gates j hj).1 with op|op
        · have eq : sig N C s (N+j)=(fun U => sig N C s a U && sig N C s b U) := by
            funext U; simp [val,op,GateOp.eval]
          rw [eq]; exact Shape.widen (Shape.and_model A B dis) sub
        · have eq : sig N C s (N+j)=(fun U => sig N C s a U || sig N C s b U) := by
            funext U; simp [val,op,GateOp.eval]
          rw [eq]; exact Shape.widen (Shape.or_model A B dis) sub
    · have eq : sig N C s w=(fun _ => sig N C s w ∅) := funext (port_value L port)
      rw [eq]
      exact Shape.widen (Shape.fixed _) (Set.empty_subset _)

end CutLib25855.Tree

namespace CutLib25855.Tree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

theorem one_pair {n m : ℕ} (u : Fin n) (c : Fin m) (S : Finset ℕ) (hu : u.val∈S) (hc : n+c.val∈S) :
    sample (n+m) S {u.val,n+c.val}=oneEach u c := by
  apply List.ext_getElem (by rw [sample_length,Cut.oneEach_length])
  intro i hi hj
  have low : i<n+m := by simpa only [sample_length] using hi
  rw [←List.getD_eq_getElem _ false hi,←List.getD_eq_getElem _ false hj,
    sample_read _ _ _ _ low,Cut.oneEach_getD]
  congr 1
  apply propext
  simp only [Finset.mem_insert,Finset.mem_singleton]
  exact ⟨And.right,fun h => ⟨h.elim (fun eq => eq ▸ hu) (fun eq => eq ▸ hc),h⟩⟩

theorem core_rectangle {α β : Type} [DecidableEq α] [DecidableEq β]
    (G : α → β → Bool) (R : Finset α) (B : Finset β) (left : α → ℕ) (right : β → ℕ)
    (f : Shape.Signal) (support : Set ℕ) (M : Shape.Model f support) (out : Bool → Bool)
    (cells : ∀ a∈R, ∀ c∈B, G a c=out (f {left a,right c})) :
    ∃ mark : Bool,
      ∀ a ∈ R.filter (fun i => ∃ j∈B, G i j≠mark),
      ∀ b ∈ R.filter (fun i => ∃ j∈B, G i j≠mark),
      ∀ x ∈ B.filter (fun j => ∃ i∈R, G i j≠mark),
      ∀ y ∈ B.filter (fun j => ∃ i∈R, G i j≠mark),
        G a x=mark → G b x=mark → G b y=mark → G a y=mark := by
  classical
  refine ⟨out true,?_⟩
  intro a ha b hb x hx y hy ax bx byy
  obtain ⟨ra,ac,hac,nac⟩ := Finset.mem_filter.mp ha
  obtain ⟨rb,bc,hbc,nbc⟩ := Finset.mem_filter.mp hb
  obtain ⟨cx,xr,hxr,nxr⟩ := Finset.mem_filter.mp hx
  obtain ⟨cy,yr,hyr,nyr⟩ := Finset.mem_filter.mp hy
  have binary : out false≠out true := by
    intro eq
    apply nac
    rw [cells a ra ac hac]
    cases f {left a,right ac} <;> simp_all
  have rowOff (i) (ri : i∈R) (j) (bj : j∈B) (ne : G i j≠out true) : f {left i}=false := by
    cases h : f {left i} with
    | false => rfl
    | true =>
      have yes := M.mono {left i} {left i,right j} (by simp) h
      exact False.elim (ne ((cells i ri j bj).trans (congrArg out yes)))
  have colOff (j) (bj : j∈B) (i) (ri : i∈R) (ne : G i j≠out true) : f {right j}=false := by
    cases h : f {right j} with
    | false => rfl
    | true =>
      have yes := M.mono {right j} {left i,right j} (by simp) h
      exact False.elim (ne ((cells i ri j bj).trans (congrArg out yes)))
  have hit (i) (ri : i∈R) (j) (cj : j∈B) (yes : G i j=out true) : f {left i,right j}=true := by
    cases z : f {left i,right j} with
    | false =>
      rw [cells i ri j cj,z] at yes
      exact False.elim (binary yes)
    | true => rfl
  have a0 := rowOff a ra ac hac nac
  have b0 := rowOff b rb bc hbc nbc
  have x0 := colOff x cx xr hxr nxr
  have y0 := colOff y cy yr hyr nyr
  have yes := M.rect (left a) (left b) (right x) (right y)
    ⟨a0,x0,hit a ra x cx ax⟩ ⟨b0,x0,hit b rb x cx bx⟩ ⟨b0,y0,hit b rb y cy byy⟩
  exact (cells a ra y cy).trans (congrArg out yes.2.2)

end CutLib25855.Tree

namespace CutLib25855
open CutLib25855.Tree PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem rectangle : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (root : ℕ),
  let raw := n + m
  let sources := R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)
  let wires := sources ∪ region.image (fun idx => raw + idx)
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
  let allReads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  let rowTypes := R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))
  let colTypes := B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))
  let coreRows := fun (rowPol : Bool) => R.filter (fun keptRow => ∃ witnessCol ∈ B, G keptRow witnessCol ≠ rowPol)
  let coreCols := fun (colPol : Bool) => B.filter (fun keptCol => ∃ witnessRow ∈ R, G witnessRow keptCol ≠ colPol)
  let rectangles := ∃ mark : Bool,
    ∀ a ∈ coreRows mark, ∀ b ∈ coreRows mark, ∀ x ∈ coreCols mark, ∀ y ∈ coreCols mark,
      G a x = mark → G b x = mark → G b y = mark → G a y = mark
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → root ∈ wires →
  entry.card ≤ 1 → (∀ w ∈ entry, w ∉ wires ∧ w < root ∧ localReads w = 1) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    (gate k).inputs.length = 2 ∧ ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w ∈ entry) →
  localReads root = 0 →
  (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ allReads w = 1 ∧ C.output ≠ w) →
  rowTypes.card ≤ 2 + entry.card ∧ colTypes.card ≤ 2 + entry.card ∧ rectangles := by
  classical
  intro n m G C R B reg ent root
  dsimp only
  intro back rep valid rootMem one ports gates endReads uses
  let N := n+m
  let left := fun i : Fin n => i.val
  let right := fun j : Fin m => n+j.val
  let S := R.image left ∪ B.image right
  have lm (a : Fin n) (h : a∈R) : left a∈S := Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
  have rm (b : Fin m) (h : b∈B) : right b∈S := Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  have rawLt (i : ℕ) (h : i∈S) : i<N := by
    rcases Finset.mem_union.mp h with a|a
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp a
      dsimp [left,N]; have := x.isLt; omega
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp a
      dsimp [right,N]; have := x.isLt; omega
  have T : Tree N C S reg root ent := ⟨rawLt,back,valid,rootMem,gates,ports,endReads,uses⟩
  rcases Finset.mem_union.mp T.rootMem with rawRoot|gateRoot
  · have low := rawLt root rawRoot
    have collapse (i) (hi : i∈S) : i=root := by
      by_contra neq
      obtain ⟨_,_,j,_,eq,_⟩ := tail_step (to_root T i (Finset.mem_union_left _ hi)) neq
      omega
    have rsmall (a) (ha : a∈R) (b) (hb : b∈R) : a=b :=
      Fin.ext ((collapse _ (lm a ha)).trans (collapse _ (lm b hb)).symm)
    have rc := Finset.card_le_one.mpr rsmall
    have bc : B.card≤1 := Finset.card_le_one.mpr (fun a ha b hb =>
      Fin.ext (Nat.add_left_cancel ((collapse _ (rm a ha)).trans (collapse _ (rm b hb)).symm)))
    refine ⟨Finset.card_image_le.trans (by omega),Finset.card_image_le.trans (by omega),false,?_⟩
    intro a ha b hb x hx y hy ax bx byy
    have ab := rsmall a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
    simpa only [ab] using byy
  · obtain ⟨k,hk,eq⟩ := Finset.mem_image.mp gateRoot
    have L := whole_layout T one hk eq.symm
    obtain ⟨rows,cols⟩ := Cut.both_axes G C R B reg ent k L rep
    refine ⟨rows,cols,?_⟩
    obtain ⟨out,outputs⟩ := readout L
    have M := structural T L (N+k) (Or.inl (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)))
    have cells (a) (ha : a∈R) (j) (hj : j∈B) : G a j=out (sig N C S (N+k) {left a,right j}) := by
      have sp : sample N S {left a,right j}=oneEach a j := one_pair a j S (lm a ha) (rm j hj)
      have output := outputs {left a,right j}
      rw [←rep a j]
      change Cut.V C (oneEach a j) C.output=_
      rw [←sp]
      exact output
    obtain ⟨mark,closed⟩ := core_rectangle G R B left right (sig N C S (N+k)) _ M out cells
    refine ⟨mark,?_⟩
    simpa only [Finset.mem_filter] using closed

end CutLib25855

namespace CutLib25855.Sparse

def admissible (d t n m : Nat) (G : Fin n → Fin m → Bool) (edge : Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m)) : Prop :=
  let nbrR := fun (row : Fin n) => Finset.univ.filter (fun dest : Fin m => G row dest = edge)
  let nbrC := fun (col : Fin m) => Finset.univ.filter (fun src : Fin n => G src col = edge)
  let rowTypes := R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))
  let colTypes := B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))
  let coreRows := fun (rowPol : Bool) => R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ rowPol)
  let coreCols := fun (colPol : Bool) => B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ colPol)
  (∀ a, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d) ∧
  (∀ c, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d) ∧
  (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) ∧
  rowTypes.card ≤ t ∧ colTypes.card ≤ t ∧
  ∃ mark : Bool, ∀ a ∈ coreRows mark, ∀ b ∈ coreRows mark,
    ∀ x ∈ coreCols mark, ∀ y ∈ coreCols mark,
      G a x = mark → G b x = mark → G b y = mark → G a y = mark

private theorem card_image_le_of_eq_imp {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f : α → β) (g : α → γ)
    (hfg : ∀ a ∈ s, ∀ b ∈ s, f a = f b → g a = g b) :
    (s.image g).card ≤ (s.image f).card := by
  classical
  by_cases hne : s.Nonempty
  · rcases hne with ⟨a0, _⟩
    have hsurj : ∀ y : γ, ∃ x : β, y ∈ s.image g →
        x ∈ s.image f ∧ ∃ a ∈ s, g a = y ∧ f a = x := by
      intro y
      by_cases hy : y ∈ s.image g
      · rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
        exact ⟨f a, fun _ => ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, a, ha, rfl, rfl⟩⟩
      · exact ⟨f a0, fun h1 => absurd h1 hy⟩
    choose φ hφ using hsurj
    refine Finset.card_le_card_of_injOn φ (fun y hy => (hφ y hy).1) ?_
    intro y₁ hy₁ y₂ hy₂ heq
    rcases (hφ y₁ hy₁).2 with ⟨a₁, ha₁, rfl, hfa₁⟩
    rcases (hφ y₂ hy₂).2 with ⟨a₂, ha₂, rfl, hfa₂⟩
    exact hfg a₁ ha₁ a₂ ha₂ (hfa₁.trans (heq.trans hfa₂.symm))
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst hs0
    simp

private theorem card_image_eq_of_eq_iff {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ g a = g b) :
    (s.image f).card = (s.image g).card :=
  le_antisymm
    (card_image_le_of_eq_imp s g f (fun a ha b hb h1 => (h a ha b hb).mpr h1))
    (card_image_le_of_eq_imp s f g (fun a ha b hb h1 => (h a ha b hb).mp h1))

private theorem card_filter_split {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    s.card = (s.filter p).card + (s.filter (fun a => ¬ p a)).card := by
  have hun : s = s.filter p ∪ s.filter (fun a => ¬ p a) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hp : p a <;> simp [hp]
  have hdisj : Disjoint (s.filter p) (s.filter (fun a => ¬ p a)) := by
    rw [Finset.disjoint_left]
    intro a h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  conv_lhs => rw [hun]
  exact Finset.card_union_of_disjoint hdisj

private theorem admissible_flip (d t n m : Nat) (G : Fin n → Fin m → Bool) (edge : Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m)) :
    admissible d t n m G edge R B ↔
    admissible d t n m (fun a c => G a c == edge) true R B := by
  have hbeq : ∀ (x y : Bool), ((x == edge) = (y == edge)) ↔ (x = y) := by
    intro x y; cases edge <;> cases x <;> cases y <;> decide
  have hrow_card :
      (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card =
      (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => (G inRow outCol == edge) = true))).card := by
    apply card_image_eq_of_eq_iff
    intro a _ b _
    constructor <;> intro h <;> ext c <;>
      have hc := Finset.ext_iff.mp h c <;>
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc ⊢
    · constructor <;> rintro ⟨hcB, h1⟩ <;> refine ⟨hcB, ?_⟩
      · cases edge <;> cases ha : G a c <;> cases hb : G b c <;> simp_all
      · cases edge <;> cases ha : G a c <;> cases hb : G b c <;> simp_all
    · constructor <;> rintro ⟨hcB, h1⟩ <;> refine ⟨hcB, ?_⟩
      · cases edge <;> cases ha : G a c <;> cases hb : G b c <;> simp_all
      · cases edge <;> cases ha : G a c <;> cases hb : G b c <;> simp_all
  have hcol_card :
      (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))).card =
      (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => (G outRow inCol == edge) = true))).card := by
    apply card_image_eq_of_eq_iff
    intro a _ b _
    constructor <;> intro h <;> ext c <;>
      have hc := Finset.ext_iff.mp h c <;>
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc ⊢
    · constructor <;> rintro ⟨hcR, h1⟩ <;> refine ⟨hcR, ?_⟩
      · cases edge <;> cases ha : G c a <;> cases hb : G c b <;> simp_all
      · cases edge <;> cases ha : G c a <;> cases hb : G c b <;> simp_all
    · constructor <;> rintro ⟨hcR, h1⟩ <;> refine ⟨hcR, ?_⟩
      · cases edge <;> cases ha : G c a <;> cases hb : G c b <;> simp_all
      · cases edge <;> cases ha : G c a <;> cases hb : G c b <;> simp_all
  have hnbrR : ∀ a,
      Finset.univ.filter (fun dest : Fin m => G a dest = edge) =
      Finset.univ.filter (fun dest : Fin m => (G a dest == edge) = true) := by
    intro a; ext c; simp [beq_iff_eq]
  have hnbrC : ∀ c,
      Finset.univ.filter (fun src : Fin n => G src c = edge) =
      Finset.univ.filter (fun src : Fin n => (G src c == edge) = true) := by
    intro c; ext a; simp [beq_iff_eq]
  unfold admissible
  dsimp only
  simp only [hnbrR, hnbrC, hrow_card, hcol_card]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, mark, hrect⟩
    refine ⟨h1, h2, h3, h4, h5, mark == edge, ?_⟩
    intro a ha b hb x hx y hy hax hbx hby
    have hcoreR : ∀ r, r ∈ R.filter (fun keptRow => ∃ w ∈ B, (G keptRow w == edge) ≠ (mark == edge)) →
        r ∈ R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ mark) := by
      intro r hr
      simp only [Finset.mem_filter] at hr ⊢
      rcases hr with ⟨hrR, w, hwB, hne⟩
      exact ⟨hrR, w, hwB, fun h => hne (by rw [h])⟩
    have hcoreC : ∀ c, c ∈ B.filter (fun keptCol => ∃ w ∈ R, (G w keptCol == edge) ≠ (mark == edge)) →
        c ∈ B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ mark) := by
      intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      rcases hc with ⟨hcB, w, hwR, hne⟩
      exact ⟨hcB, w, hwR, fun h => hne (by rw [h])⟩
    exact (hbeq (G a y) mark).mpr
      (hrect a (hcoreR a ha) b (hcoreR b hb) x (hcoreC x hx) y (hcoreC y hy)
        ((hbeq _ _).mp hax) ((hbeq _ _).mp hbx) ((hbeq _ _).mp hby))
  · rintro ⟨h1, h2, h3, h4, h5, mark, hrect⟩
    refine ⟨h1, h2, h3, h4, h5, mark == edge, ?_⟩
    have hinv : ∀ z : Bool, ((z == edge) == edge) = z := by
      intro z; cases edge <;> cases z <;> decide
    intro a ha b hb x hx y hy hax hbx hby
    have hcoreR : ∀ r, r ∈ R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ (mark == edge)) →
        r ∈ R.filter (fun keptRow => ∃ w ∈ B, (G keptRow w == edge) ≠ mark) := by
      intro r hr
      simp only [Finset.mem_filter] at hr ⊢
      rcases hr with ⟨hrR, w, hwB, hne⟩
      exact ⟨hrR, w, hwB, fun h => hne (by rw [← h, hinv])⟩
    have hcoreC : ∀ c, c ∈ B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ (mark == edge)) →
        c ∈ B.filter (fun keptCol => ∃ w ∈ R, (G w keptCol == edge) ≠ mark) := by
      intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      rcases hc with ⟨hcB, w, hwR, hne⟩
      exact ⟨hcB, w, hwR, fun h => hne (by rw [← h, hinv])⟩
    have hay := hrect a (hcoreR a ha) b (hcoreR b hb) x (hcoreC x hx) y (hcoreC y hy)
      (by rw [hax, hinv]) (by rw [hbx, hinv]) (by rw [hby, hinv])
    rw [← hay, hinv]

private theorem col_c4_of_row_c4 {n m : Nat} (G : Fin n → Fin m → Bool)
    (hrow : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter (fun c : Fin m => G a c = true)) ∩
       (Finset.univ.filter (fun c : Fin m => G b c = true))).card ≤ 1) :
    ∀ x y : Fin m, x ≠ y →
      ((Finset.univ.filter (fun a : Fin n => G a x = true)) ∩
       (Finset.univ.filter (fun a : Fin n => G a y = true))).card ≤ 1 := by
  intro x y hxy
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hsub : ({x, y} : Finset (Fin m)) ⊆
      (Finset.univ.filter (fun c : Fin m => G a c = true)) ∩
      (Finset.univ.filter (fun c : Fin m => G b c = true)) := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hc with rfl | rfl
    · exact ⟨ha.1, hb.1⟩
    · exact ⟨ha.2, hb.2⟩
  have h2 : 2 ≤ ({x, y} : Finset (Fin m)).card := by
    rw [Finset.card_pair hxy]
  have hle := Finset.card_le_card hsub
  have h1 := hrow a b hab
  omega

private theorem admissible_transpose (d t n m : Nat) (G : Fin n → Fin m → Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m)) :
    admissible d t n m G true R B →
    admissible d t m n (fun c a => G a c) true B R := by
  rintro ⟨h1, h2, h3, h4, h5, mark, hrect⟩
  refine ⟨h2, h1, col_c4_of_row_c4 G h3, h5, h4, mark, ?_⟩
  intro x hx y hy a ha b hb hxa hya hyb
  exact hrect b hb a ha y hy x hx hyb hya hxa

private theorem card_le_mul_of_fiber_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (k M : Nat)
    (him : (s.image f).card ≤ k)
    (hfib : ∀ y ∈ s.image f, (s.filter (fun a => f a = y)).card ≤ M) :
    s.card ≤ k * M := by
  have heq : s.card = ∑ y ∈ s.image f, (s.filter (fun a => f a = y)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := s.image f)]
    intro a ha
    exact Finset.mem_image_of_mem f ha
  rw [heq]
  calc ∑ y ∈ s.image f, (s.filter (fun a => f a = y)).card
      ≤ ∑ _y ∈ s.image f, M := Finset.sum_le_sum (fun y hy => hfib y hy)
    _ = (s.image f).card * M := by simp
    _ ≤ k * M := Nat.mul_le_mul_right M him

private theorem card_le_dt_of_empty_le_d {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) (d t : Nat)
    (him : (s.image f).card ≤ t)
    (hnonempty_fib : ∀ P : Finset β, P.Nonempty → (s.filter (fun a => f a = P)).card ≤ d)
    (h0 : (s.filter (fun a => f a = ∅)).card ≤ d) :
    s.card ≤ d * t := by
  let s0 := s.filter (fun a => f a = ∅)
  let s1 := s.filter (fun a => f a ≠ ∅)
  have h0' : s0.card ≤ d := h0
  have hsum : s.card = s0.card + s1.card := card_filter_split s (fun a => f a = ∅)
  by_cases h0ne : s0.Nonempty
  · have hmem0 : (∅ : Finset β) ∈ s.image f := by
      rcases h0ne with ⟨a, ha⟩
      exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩
    have hsub : s1.image f ⊆ (s.image f).erase ∅ := by
      intro P hP
      rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
      rcases Finset.mem_filter.mp ha with ⟨has, hne⟩
      exact Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f has⟩
    have him1 : (s1.image f).card ≤ t - 1 := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hmem0] at h1
      omega
    have hs1 : s1.card ≤ (t - 1) * d := by
      apply card_le_mul_of_fiber_bound s1 f (t - 1) d him1
      intro P hP
      rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
      have hPne : (f a).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp ha).2
      calc (s1.filter (fun x => f x = f a)).card
          ≤ (s.filter (fun x => f x = f a)).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [s1, Finset.mem_filter] at hx ⊢
            exact ⟨hx.1.1, hx.2⟩
        _ ≤ d := hnonempty_fib (f a) hPne
    have hdt : d + (t - 1) * d ≤ d * t := by
      cases t with
      | zero =>
        have hpos : 0 < (s.image f).card := Finset.card_pos.mpr ⟨∅, hmem0⟩
        omega
      | succ t' =>
        simp only [Nat.add_sub_cancel]
        rw [Nat.mul_comm t' d, Nat.mul_succ, Nat.add_comm]
    omega
  · have hs0 : s0.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h0ne)
    have hs1 : s1.card ≤ t * d := by
      apply card_le_mul_of_fiber_bound s1 f t d
      · exact (Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))).trans him
      · intro P hP
        rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
        have hPne : (f a).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp ha).2
        calc (s1.filter (fun x => f x = f a)).card
            ≤ (s.filter (fun x => f x = f a)).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [s1, Finset.mem_filter] at hx ⊢
              exact ⟨hx.1.1, hx.2⟩
          _ ≤ d := hnonempty_fib (f a) hPne
    rw [Nat.mul_comm] at hs1
    omega

private theorem upper_bound_one_empty_side (d t n m : Nat) (G : Fin n → Fin m → Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m))
    (hd : 2 ≤ d) (ht : 2 ≤ t)
    (hnbrR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter (fun c : Fin m => G a c = true)).card ∧
      (Finset.univ.filter (fun c : Fin m => G a c = true)).card ≤ d)
    (hnbrC : ∀ c : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => G a c = true)).card ∧
      (Finset.univ.filter (fun a : Fin n => G a c = true)).card ≤ d)
    (hc4R : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter (fun c : Fin m => G a c = true)) ∩
       (Finset.univ.filter (fun c : Fin m => G b c = true))).card ≤ 1)
    (hrowT : (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card ≤ t)
    (hcolT : (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))).card ≤ t)
    (hrect : ∀ a ∈ R, ∀ b ∈ R, ∀ x ∈ B, ∀ y ∈ B,
      G a x = true → G b x = true → G b y = true → G a y = true)
    (hR0_empty : R.filter (fun a => (Finset.univ \ B).filter (fun c => G a c = true) = ∅) = ∅)
    (hB0_ne : (B.filter (fun c => (Finset.univ \ R).filter (fun a => G a c = true) = ∅)).Nonempty) :
    R.card + B.card ≤ max (2 * d * t) (2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2)) := by
  let nbrR := fun a : Fin n => Finset.univ.filter (fun c : Fin m => G a c = true)
  let nbrC := fun c : Fin m => Finset.univ.filter (fun a : Fin n => G a c = true)
  let extR := fun a : Fin n => (Finset.univ \ B).filter (fun c : Fin m => G a c = true)
  let extC := fun c : Fin m => (Finset.univ \ R).filter (fun a : Fin n => G a c = true)
  let B0 := B.filter (fun c => extC c = ∅)
  let B1 := B.filter (fun c => extC c ≠ ∅)
  have h2dt : 2 * d * t = d * t + d * t := by rw [Nat.two_mul, Nat.add_mul]
  change ∀ a : Fin n, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d at hnbrR
  change ∀ c : Fin m, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d at hnbrC
  change ∀ a b : Fin n, a ≠ b → (nbrR a ∩ nbrR b).card ≤ 1 at hc4R
  change (R.image extR).card ≤ t at hrowT
  change (B.image extC).card ≤ t at hcolT
  have hc4C : ∀ x y : Fin m, x ≠ y → (nbrC x ∩ nbrC y).card ≤ 1 := col_c4_of_row_c4 G hc4R
  have hBsum : B.card = B0.card + B1.card := card_filter_split B (fun c => extC c = ∅)
  have hfibR : ∀ P : Finset (Fin m), P.Nonempty → (R.filter (fun a => extR a = P)).card ≤ d := by
    rintro P ⟨c0, hc0⟩
    have hsub : R.filter (fun a => extR a = P) ⊆ nbrC c0 := by
      intro a ha
      rcases Finset.mem_filter.mp ha with ⟨_, hP⟩
      have hc0' : c0 ∈ extR a := hP ▸ hc0
      simp only [extR, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc0' ⊢
      exact hc0'.2
    exact (Finset.card_le_card hsub).trans (hnbrC c0).2
  have hfibB : ∀ P : Finset (Fin n), P.Nonempty → (B.filter (fun c => extC c = P)).card ≤ d := by
    rintro P ⟨a0, ha0⟩
    have hsub : B.filter (fun c => extC c = P) ⊆ nbrR a0 := by
      intro c hc
      rcases Finset.mem_filter.mp hc with ⟨_, hP⟩
      have ha0' : a0 ∈ extC c := hP ▸ ha0
      simp only [extC, nbrR, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha0' ⊢
      exact ha0'.2
    exact (Finset.card_le_card hsub).trans (hnbrR a0).2
  have hR_le_dt : R.card ≤ d * t := by
    apply card_le_dt_of_empty_le_d R extR d t hrowT hfibR
    rw [hR0_empty]; simp
  have hB0_sub_R : ∀ x ∈ B0, nbrC x ⊆ R := by
    intro x hx a ha
    have hxe : extC x = ∅ := (Finset.mem_filter.mp hx).2
    by_contra haR
    have hmem : a ∈ extC x := by
      simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha ⊢
      exact ⟨haR, ha⟩
    rw [hxe] at hmem; simp at hmem
  have hstar_B0 : ∀ x ∈ B0, ∀ a ∈ nbrC x, ∀ y ∈ B, G a y = true → y = x := by
    intro x hx a ha y hy hay
    have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
    have haR : a ∈ R := hB0_sub_R x hx ha
    by_contra hyx
    have hcard : 2 ≤ (nbrC x).card := (hnbrC x).1
    have hne : ((nbrC x).erase a).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hem
      have h1 : (nbrC x).card ≤ 1 := by
        have := Finset.card_erase_of_mem ha
        rw [hem] at this; simp at this; omega
      omega
    rcases hne with ⟨b, hb⟩
    rcases Finset.mem_erase.mp hb with ⟨hba, hbN⟩
    have hbR : b ∈ R := hB0_sub_R x hx hbN
    have hax : G a x = true := (Finset.mem_filter.mp ha).2
    have hbx : G b x = true := (Finset.mem_filter.mp hbN).2
    have hby : G b y = true := hrect b hbR a haR x hxB y hy hbx hax hay
    have hsub : ({a, b} : Finset (Fin n)) ⊆ nbrC x ∩ nbrC y := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      simp only [nbrC, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hr with rfl | rfl
      · exact ⟨hax, hay⟩
      · exact ⟨hbx, hby⟩
    have hpair : ({a, b} : Finset (Fin n)).card = 2 := Finset.card_pair (Ne.symm hba)
    have h1 := hc4C x y (Ne.symm hyx)
    have hle := Finset.card_le_card hsub
    omega
  let Rused := B0.biUnion (fun x => nbrC x)
  have hRused_sub : Rused ⊆ R := by
    intro a ha
    rcases Finset.mem_biUnion.mp ha with ⟨x, hx, hax⟩
    exact hB0_sub_R x hx hax
  have hRused_disj : Set.PairwiseDisjoint (B0 : Set (Fin m)) (fun x => nbrC x) := by
    intro x hx y hy hxy
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a hax hay
    have hyB : y ∈ B := (Finset.mem_filter.mp hy).1
    have hgay : G a y = true := (Finset.mem_filter.mp hay).2
    exact hxy (hstar_B0 x hx a hax y hyB hgay).symm
  have h2B0_le_Rused : 2 * B0.card ≤ Rused.card := by
    rw [Finset.card_biUnion hRused_disj]
    calc 2 * B0.card = ∑ _x ∈ B0, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ B0, (nbrC x).card := Finset.sum_le_sum (fun x _ => (hnbrC x).1)
  have hRused_le_R : Rused.card ≤ R.card := Finset.card_le_card hRused_sub
  have hB1_im_le : (B1.image extC).card ≤ t - 1 := by
    have hmem0 : (∅ : Finset (Fin n)) ∈ B.image extC := by
      rcases hB0_ne with ⟨x, hx⟩
      exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    have hsub : B1.image extC ⊆ (B.image extC).erase ∅ := by
      intro P hP
      rcases Finset.mem_image.mp hP with ⟨c, hc, rfl⟩
      rcases Finset.mem_filter.mp hc with ⟨hcB, hne⟩
      exact Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem extC hcB⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hmem0] at hle
    omega
  by_cases hB1_empty : B1 = ∅
  · have hB1c : B1.card = 0 := Finset.card_eq_zero.mpr hB1_empty
    have hcap1 : 2 * d * t ≤ max (2 * d * t) (2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2)) := le_max_left _ _
    omega
  · have hB1ne : (B1.image extC).Nonempty :=
      Finset.Nonempty.image (Finset.nonempty_iff_ne_empty.mpr hB1_empty) extC
    rcases Finset.exists_max_image (B1.image extC) (fun P => (B1.filter (fun c => extC c = P)).card) hB1ne
      with ⟨Pmax, hPmax_mem, hPmax_max⟩
    let Dmax := B1.filter (fun c => extC c = Pmax)
    let h := Dmax.card
    have hB1_le_th : B1.card ≤ (t - 1) * h :=
      card_le_mul_of_fiber_bound B1 extC (t - 1) h hB1_im_le hPmax_max
    have hh_le_d : h ≤ d := by
      rcases Finset.mem_image.mp hPmax_mem with ⟨c0, hc0, rfl⟩
      have hPne : (extC c0).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hc0).2
      calc Dmax.card ≤ (B.filter (fun c => extC c = extC c0)).card := by
            apply Finset.card_le_card
            intro c hc
            simp only [Dmax, B1, Finset.mem_filter] at hc ⊢
            exact ⟨hc.1.1, hc.2⟩
        _ ≤ d := hfibB (extC c0) hPne
    by_cases hh1 : h ≤ 1
    · have hB1_le : B1.card ≤ t - 1 := by
        calc B1.card ≤ (t - 1) * h := hB1_le_th
          _ ≤ (t - 1) * 1 := Nat.mul_le_mul_left (t - 1) hh1
          _ = t - 1 := Nat.mul_one _
      have hdt_ge : 2 * (t - 1) ≤ d * t := by
        have h1 : 2 * (t - 1) ≤ 2 * t := by omega
        have h2 : 2 * t ≤ d * t := Nat.mul_le_mul_right t hd
        omega
      have hcap1 : 2 * d * t ≤ max (2 * d * t) (2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2)) := le_max_left _ _
      omega
    · have hh2 : 2 ≤ h := by omega
      rcases Finset.one_lt_card.mp (by omega : 1 < Dmax.card) with ⟨c₁, hc₁, c₂, hc₂, hc12⟩
      have hext_eq : extC c₁ = Pmax ∧ extC c₂ = Pmax :=
        ⟨(Finset.mem_filter.mp hc₁).2, (Finset.mem_filter.mp hc₂).2⟩
      have hPmax_ne : Pmax.Nonempty := by
        rw [← hext_eq.1]
        exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hc₁).1).2
      have hPmax_card_le : Pmax.card ≤ 1 := by
        have hsub : Pmax ⊆ nbrC c₁ ∩ nbrC c₂ := by
          intro a ha
          have ha1 : a ∈ extC c₁ := hext_eq.1.symm ▸ ha
          have ha2 : a ∈ extC c₂ := hext_eq.2.symm ▸ ha
          simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_inter] at ha1 ha2 ⊢
          exact ⟨ha1.2, ha2.2⟩
        exact (Finset.card_le_card hsub).trans (hc4C c₁ c₂ hc12)
      rcases hPmax_ne with ⟨r_ext, hr_ext⟩
      have hr_ext_notR : r_ext ∉ R := by
        have hmem : r_ext ∈ extC c₁ := hext_eq.1.symm ▸ hr_ext
        simp only [extC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hmem
        exact hmem.1
      have hD_has_R : ∀ c ∈ Dmax, (nbrC c ∩ R).Nonempty := by
        intro c hc
        have hcext : extC c = Pmax := (Finset.mem_filter.mp hc).2
        have hpart : nbrC c ⊆ (nbrC c ∩ R) ∪ extC c := by
          intro a ha
          by_cases haR : a ∈ R
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, haR⟩)
          · apply Finset.mem_union_right
            simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha ⊢
            exact ⟨haR, ha⟩
        have hle := Finset.card_le_card hpart
        have hun := Finset.card_union_le (nbrC c ∩ R) (extC c)
        have h2 := (hnbrC c).1
        rw [hcext] at hle hun
        have hpos : 0 < (nbrC c ∩ R).card := by omega
        exact Finset.card_pos.mp hpos
      have hchoose : ∀ c : Fin m, ∃ a : Fin n, c ∈ Dmax → a ∈ nbrC c ∩ R := by
        intro c
        by_cases hc : c ∈ Dmax
        · rcases hD_has_R c hc with ⟨a, ha⟩
          exact ⟨a, fun _ => ha⟩
        · exact ⟨r_ext, fun h1 => absurd h1 hc⟩
      choose f hf using hchoose
      have hf_inj : Set.InjOn f (Dmax : Set (Fin m)) := by
        intro x hx y hy hfeq
        by_contra hxy
        have hfx := hf x hx
        have hfy := hf y hy
        rw [← hfeq] at hfy
        have hfxR : f x ∈ R := (Finset.mem_inter.mp hfx).2
        have hre_x : r_ext ∈ nbrC x := by
          have hm : r_ext ∈ extC x := (Finset.mem_filter.mp hx).2.symm ▸ hr_ext
          simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm ⊢
          exact hm.2
        have hre_y : r_ext ∈ nbrC y := by
          have hm : r_ext ∈ extC y := (Finset.mem_filter.mp hy).2.symm ▸ hr_ext
          simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm ⊢
          exact hm.2
        have hne_fr : f x ≠ r_ext := fun heq => hr_ext_notR (heq ▸ hfxR)
        have hsub : ({f x, r_ext} : Finset (Fin n)) ⊆ nbrC x ∩ nbrC y := by
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hfx).1, (Finset.mem_inter.mp hfy).1⟩
          · exact Finset.mem_inter.mpr ⟨hre_x, hre_y⟩
        have hpair : ({f x, r_ext} : Finset (Fin n)).card = 2 := Finset.card_pair hne_fr
        have hle := Finset.card_le_card hsub
        have h1 := hc4C x y hxy
        omega
      have hf_disj : Disjoint (Dmax.image f) Rused := by
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        rcases Finset.mem_image.mp ha1 with ⟨c, hcD, rfl⟩
        rcases Finset.mem_biUnion.mp ha2 with ⟨x, hx0, hax⟩
        have hcB1 : c ∈ B1 := (Finset.mem_filter.mp hcD).1
        have hcB : c ∈ B := (Finset.mem_filter.mp hcB1).1
        have hfc : G (f c) c = true := (Finset.mem_filter.mp (Finset.mem_inter.mp (hf c hcD)).1).2
        have hcx : c = x := hstar_B0 x hx0 (f c) hax c hcB hfc
        subst hcx
        exact (Finset.mem_filter.mp hcB1).2 (Finset.mem_filter.mp hx0).2
      have hf_sub : Dmax.image f ⊆ R := by
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨c, hcD, rfl⟩
        exact (Finset.mem_inter.mp (hf c hcD)).2
      have hR_ge : Rused.card + h ≤ R.card := by
        have h1 : (Dmax.image f ∪ Rused).card ≤ R.card :=
          Finset.card_le_card (Finset.union_subset hf_sub hRused_sub)
        rw [Finset.card_union_of_disjoint hf_disj, Finset.card_image_of_injOn hf_inj] at h1
        omega
      have h2B0_le : 2 * B0.card + h ≤ R.card := by omega
      have h2sum : 2 * (R.card + B.card) ≤ d * (5 * t - 3) := by
        have h1 : 2 * (R.card + B.card) ≤ 3 * R.card + (2 * t - 3) * h := by
          have h2 : 2 * ((t - 1) * h) = (2 * t - 2) * h := by
            cases t with
            | zero => omega
            | succ t' =>
              simp only [Nat.add_sub_cancel]
              have hEq : 2 * (t' + 1) - 2 = 2 * t' := by omega
              rw [hEq, Nat.mul_assoc]
          have h3 : (2 * t - 2) * h = (2 * t - 3) * h + h := by
            have hEq : 2 * t - 2 = (2 * t - 3) + 1 := by omega
            rw [hEq, Nat.add_mul, Nat.one_mul]
          omega
        have h2 : 3 * R.card ≤ 3 * (d * t) := Nat.mul_le_mul_left 3 hR_le_dt
        have h3 : (2 * t - 3) * h ≤ (2 * t - 3) * d := Nat.mul_le_mul_left (2 * t - 3) hh_le_d
        have h4 : 3 * (d * t) + (2 * t - 3) * d = d * (5 * t - 3) := by
          have hEq : 3 * t + (2 * t - 3) = 5 * t - 3 := by omega
          calc 3 * (d * t) + (2 * t - 3) * d
              = d * (3 * t) + d * (2 * t - 3) := by rw [Nat.mul_left_comm, Nat.mul_comm (2 * t - 3) d]
            _ = d * (3 * t + (2 * t - 3)) := by rw [← Nat.mul_add]
            _ = d * (5 * t - 3) := by rw [hEq]
        omega
      by_cases ht3 : t ≤ 3
      · have h54 : 5 * t - 3 ≤ 4 * t := by omega
        have hbound : d * (5 * t - 3) ≤ 2 * (2 * d * t) := by
          calc d * (5 * t - 3) ≤ d * (4 * t) := Nat.mul_le_mul_left d h54
            _ = 2 * (2 * d * t) := by
              rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm d 4]
              have : 4 * d = 2 * (2 * d) := by omega
              rw [this, Nat.mul_assoc]
        have hcap1 : 2 * d * t ≤ max (2 * d * t) (2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2)) := le_max_left _ _
        omega
      · have ht4 : 4 ≤ t := by omega
        let L := d * (t - 1)
        have hdiv : 2 * (L / 2) + 1 ≥ L := by omega
        have hdt_ge : 2 ≤ d * (t - 3) := by
          have h1 : 1 ≤ t - 3 := by omega
          calc 2 = 2 * 1 := by simp
            _ ≤ d * (t - 3) := Nat.mul_le_mul hd h1
        have hbound : d * (5 * t - 3) ≤ 6 * L - 2 := by
          have hEq : 6 * L = d * (6 * t - 6) := by
            have h6 : 6 * (t - 1) = 6 * t - 6 := by omega
            calc 6 * (d * (t - 1)) = d * (6 * (t - 1)) := Nat.mul_left_comm 6 d (t - 1)
              _ = d * (6 * t - 6) := by rw [h6]
          have hEq2 : d * (6 * t - 6) = d * (5 * t - 3) + d * (t - 3) := by
            rw [← Nat.mul_add]
            congr 1
            omega
          omega
        have hcap2 : 2 * L + 2 * (L / 2) ≤ max (2 * d * t) (2 * L + 2 * (L / 2)) := le_max_right _ _
        omega

private theorem upper_bound_true (d t n m : Nat) (G : Fin n → Fin m → Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m))
    (hd : 2 ≤ d) (ht : 2 ≤ t)
    (hadm : admissible d t n m G true R B) :
    R.card + B.card ≤ max (2 * d * t) (2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2)) := by
  let L := d * (t - 1)
  let cap := max (2 * d * t) (2 * L + 2 * (L / 2))
  have hcap1 : 2 * d * t ≤ cap := le_max_left _ _
  have hcap2 : 2 * L + 2 * (L / 2) ≤ cap := le_max_right _ _
  have h2dt : 2 * d * t = d * t + d * t := by rw [Nat.two_mul, Nat.add_mul]
  rcases hadm with ⟨hnbrR, hnbrC, hc4R, hrowT, hcolT, mark, hrect⟩
  let nbrR := fun a : Fin n => Finset.univ.filter (fun c : Fin m => G a c = true)
  let nbrC := fun c : Fin m => Finset.univ.filter (fun a : Fin n => G a c = true)
  let extR := fun a : Fin n => (Finset.univ \ B).filter (fun c : Fin m => G a c = true)
  let extC := fun c : Fin m => (Finset.univ \ R).filter (fun a : Fin n => G a c = true)
  change ∀ a : Fin n, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d at hnbrR
  change ∀ c : Fin m, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d at hnbrC
  change ∀ a b : Fin n, a ≠ b → (nbrR a ∩ nbrR b).card ≤ 1 at hc4R
  change (R.image extR).card ≤ t at hrowT
  change (B.image extC).card ≤ t at hcolT
  have hc4C : ∀ x y : Fin m, x ≠ y → (nbrC x ∩ nbrC y).card ≤ 1 := col_c4_of_row_c4 G hc4R
  let R0 := R.filter (fun a => extR a = ∅)
  let R1 := R.filter (fun a => extR a ≠ ∅)
  let B0 := B.filter (fun c => extC c = ∅)
  let B1 := B.filter (fun c => extC c ≠ ∅)
  have hRsum : R.card = R0.card + R1.card := card_filter_split R (fun a => extR a = ∅)
  have hBsum : B.card = B0.card + B1.card := card_filter_split B (fun c => extC c = ∅)
  have hfibR : ∀ P : Finset (Fin m), P.Nonempty → (R.filter (fun a => extR a = P)).card ≤ d := by
    rintro P ⟨c0, hc0⟩
    have hsub : R.filter (fun a => extR a = P) ⊆ nbrC c0 := by
      intro a ha
      rcases Finset.mem_filter.mp ha with ⟨_, hP⟩
      have hc0' : c0 ∈ extR a := hP ▸ hc0
      simp only [extR, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc0' ⊢
      exact hc0'.2
    exact (Finset.card_le_card hsub).trans (hnbrC c0).2
  have hfibB : ∀ P : Finset (Fin n), P.Nonempty → (B.filter (fun c => extC c = P)).card ≤ d := by
    rintro P ⟨a0, ha0⟩
    have hsub : B.filter (fun c => extC c = P) ⊆ nbrR a0 := by
      intro c hc
      rcases Finset.mem_filter.mp hc with ⟨_, hP⟩
      have ha0' : a0 ∈ extC c := hP ▸ ha0
      simp only [extC, nbrR, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha0' ⊢
      exact ha0'.2
    exact (Finset.card_le_card hsub).trans (hnbrR a0).2
  have hR_le_dt : R0.card ≤ d → R.card ≤ d * t :=
    fun h => card_le_dt_of_empty_le_d R extR d t hrowT hfibR h
  have hB_le_dt : B0.card ≤ d → B.card ≤ d * t :=
    fun h => card_le_dt_of_empty_le_d B extC d t hcolT hfibB h
  have hR0_sub_B : ∀ a ∈ R0, nbrR a ⊆ B := by
    intro a ha c hc
    have hae : extR a = ∅ := (Finset.mem_filter.mp ha).2
    by_contra hcB
    have hmem : c ∈ extR a := by
      simp only [extR, nbrR, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc ⊢
      exact ⟨hcB, hc⟩
    rw [hae] at hmem; simp at hmem
  have hB0_sub_R : ∀ c ∈ B0, nbrC c ⊆ R := by
    intro c hc a ha
    have hce : extC c = ∅ := (Finset.mem_filter.mp hc).2
    by_contra haR
    have hmem : a ∈ extC c := by
      simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha ⊢
      exact ⟨haR, ha⟩
    rw [hce] at hmem; simp at hmem
  cases mark
  · let cR := R.filter (fun a => ∃ x ∈ B, G a x ≠ false)
    let cB := B.filter (fun x => ∃ a ∈ R, G a x ≠ false)
    have hR0_sub_cR : R0 ⊆ cR := by
      intro a ha
      have haR : a ∈ R := (Finset.mem_filter.mp ha).1
      have hne : (nbrR a).Nonempty := Finset.card_pos.mp (by have := (hnbrR a).1; omega)
      rcases hne with ⟨x, hx⟩
      refine Finset.mem_filter.mpr ⟨haR, x, hR0_sub_B a ha hx, ?_⟩
      have hG : G a x = true := (Finset.mem_filter.mp hx).2
      rw [hG]; decide
    have hB0_sub_cB : B0 ⊆ cB := by
      intro x hx
      have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
      have hne : (nbrC x).Nonempty := Finset.card_pos.mp (by have := (hnbrC x).1; omega)
      rcases hne with ⟨a, ha⟩
      refine Finset.mem_filter.mpr ⟨hxB, a, hB0_sub_R x hx ha, ?_⟩
      have hG : G a x = true := (Finset.mem_filter.mp ha).2
      rw [hG]; decide
    have hnonedge_eq : ∀ a ∈ cR, ∀ b ∈ cR,
        (∃ x ∈ cB, G a x = false ∧ G b x = false) → nbrR a ∩ cB = nbrR b ∩ cB := by
      intro a ha b hb ⟨x, hx, hax, hbx⟩
      ext y
      simp only [nbrR, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> rintro ⟨hG, hy⟩ <;> refine ⟨?_, hy⟩
      · cases hby : G b y
        · have hay := hrect a ha b hb x hx y hy hax hbx hby
          rw [hay] at hG; cases hG
        · rfl
      · cases hay : G a y
        · have hby := hrect b hb a ha x hx y hy hbx hax hay
          rw [hby] at hG; cases hG
        · rfl
    have hB0_le1_of_cR_le2 : cR.card ≤ 2 → B0.card ≤ 1 := by
      intro hcR2
      rw [Finset.card_le_one]
      intro x hx y hy
      by_contra hxy
      have hxsub : nbrC x ⊆ cR := by
        intro a ha
        have haR := hB0_sub_R x hx ha
        have hG : G a x = true := (Finset.mem_filter.mp ha).2
        exact Finset.mem_filter.mpr ⟨haR, x, (Finset.mem_filter.mp hx).1, by rw [hG]; decide⟩
      have hysub : nbrC y ⊆ cR := by
        intro a ha
        have haR := hB0_sub_R y hy ha
        have hG : G a y = true := (Finset.mem_filter.mp ha).2
        exact Finset.mem_filter.mpr ⟨haR, y, (Finset.mem_filter.mp hy).1, by rw [hG]; decide⟩
      have hxeq : nbrC x = cR := Finset.eq_of_subset_of_card_le hxsub (by have := (hnbrC x).1; omega)
      have hyeq : nbrC y = cR := Finset.eq_of_subset_of_card_le hysub (by have := (hnbrC y).1; omega)
      have hinter : (nbrC x ∩ nbrC y).card = cR.card := by rw [hxeq, hyeq, Finset.inter_self]
      have h1 := hc4C x y hxy
      have h2 := (hnbrC x).1
      rw [hxeq] at h2
      omega
    have hR0_le1_of_cB_le2 : cB.card ≤ 2 → R0.card ≤ 1 := by
      intro hcB2
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      have hasub : nbrR a ⊆ cB := by
        intro x hx
        have hxB := hR0_sub_B a ha hx
        have hG : G a x = true := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨hxB, a, (Finset.mem_filter.mp ha).1, by rw [hG]; decide⟩
      have hbsub : nbrR b ⊆ cB := by
        intro x hx
        have hxB := hR0_sub_B b hb hx
        have hG : G b x = true := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨hxB, b, (Finset.mem_filter.mp hb).1, by rw [hG]; decide⟩
      have haeq : nbrR a = cB := Finset.eq_of_subset_of_card_le hasub (by have := (hnbrR a).1; omega)
      have hbeq : nbrR b = cB := Finset.eq_of_subset_of_card_le hbsub (by have := (hnbrR b).1; omega)
      have hinter : (nbrR a ∩ nbrR b).card = cB.card := by rw [haeq, hbeq, Finset.inter_self]
      have h1 := hc4R a b hab
      have h2 := (hnbrR a).1
      rw [haeq] at h2
      omega
    by_cases hcR2 : cR.card ≤ 2
    · have hR0le : R0.card ≤ d := (Finset.card_le_card hR0_sub_cR).trans (by omega)
      have hB0le : B0.card ≤ d := (hB0_le1_of_cR_le2 hcR2).trans (by omega)
      have h1 := hR_le_dt hR0le
      have h2 := hB_le_dt hB0le
      omega
    · have hcR3 : 3 ≤ cR.card := by omega
      by_cases hexV : ∃ a ∈ cR, 2 ≤ (cB \ nbrR a).card
      · rcases hexV with ⟨a0, ha0, hV2⟩
        let V := cB \ nbrR a0
        change 2 ≤ V.card at hV2
        let U := cR.filter (fun b => nbrR b ∩ cB = nbrR a0 ∩ cB)
        have hV_sub : ∀ b ∈ cR \ U, V ⊆ nbrR b := by
          intro b hb x hx
          rcases Finset.mem_sdiff.mp hb with ⟨hbcR, hbnU⟩
          rcases Finset.mem_sdiff.mp hx with ⟨hxcB, hxna0⟩
          have ha0x : G a0 x = false := by
            cases hG : G a0 x
            · rfl
            · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hG⟩) hxna0
          cases hbx : G b x
          · exfalso
            apply hbnU
            exact Finset.mem_filter.mpr ⟨hbcR, hnonedge_eq b hbcR a0 ha0 ⟨x, hxcB, hbx, ha0x⟩⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx⟩
        have hrest_le1 : (cR \ U).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro b₁ hb₁ b₂ hb₂
          by_contra h12
          have hsub : V ⊆ nbrR b₁ ∩ nbrR b₂ :=
            Finset.subset_inter (hV_sub b₁ hb₁) (hV_sub b₂ hb₂)
          have hle := Finset.card_le_card hsub
          have h1 := hc4R b₁ b₂ h12
          omega
        have hU_ge2 : 2 ≤ U.card := by
          have hsub : U ⊆ cR := Finset.filter_subset _ _
          have hsd := Finset.card_sdiff_add_card_eq_card hsub
          omega
        rcases Finset.one_lt_card.mp (by omega : 1 < U.card) with ⟨a₁, ha₁, a₂, ha₂, ha12⟩
        have ha1eq : nbrR a₁ ∩ cB = nbrR a0 ∩ cB := (Finset.mem_filter.mp ha₁).2
        have ha2eq : nbrR a₂ ∩ cB = nbrR a0 ∩ cB := (Finset.mem_filter.mp ha₂).2
        have hN_le1 : (nbrR a0 ∩ cB).card ≤ 1 := by
          have hsub : nbrR a0 ∩ cB ⊆ nbrR a₁ ∩ nbrR a₂ := by
            intro x hx
            have h1 : x ∈ nbrR a₁ ∩ cB := ha1eq.symm ▸ hx
            have h2 : x ∈ nbrR a₂ ∩ cB := ha2eq.symm ▸ hx
            exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
          exact (Finset.card_le_card hsub).trans (hc4R a₁ a₂ ha12)
        have hR0_le1 : R0.card ≤ 1 := by
          have hsub : R0 ⊆ cR \ U := by
            intro r hr
            have hrcR : r ∈ cR := hR0_sub_cR hr
            refine Finset.mem_sdiff.mpr ⟨hrcR, ?_⟩
            intro hrU
            have hreq : nbrR r ∩ cB = nbrR a0 ∩ cB := (Finset.mem_filter.mp hrU).2
            have hsub2 : nbrR r ⊆ nbrR r ∩ cB := by
              intro x hx
              have hxB : x ∈ B := hR0_sub_B r hr hx
              have hG : G r x = true := (Finset.mem_filter.mp hx).2
              exact Finset.mem_inter.mpr ⟨hx, Finset.mem_filter.mpr ⟨hxB, r, (Finset.mem_filter.mp hr).1, by rw [hG]; decide⟩⟩
            have hle := Finset.card_le_card hsub2
            rw [hreq] at hle
            have h2 := (hnbrR r).1
            omega
          exact (Finset.card_le_card hsub).trans hrest_le1
        have hB0_le1 : B0.card ≤ 1 := by
          have hsub : B0 ⊆ nbrR a0 ∩ cB := by
            intro x hx
            have hxcB : x ∈ cB := hB0_sub_cB hx
            by_contra hxn
            have hxV : x ∈ V := by
              refine Finset.mem_sdiff.mpr ⟨hxcB, ?_⟩
              intro hxna
              exact hxn (Finset.mem_inter.mpr ⟨hxna, hxcB⟩)
            have hnx_sub : nbrC x ⊆ cR \ U := by
              intro r hr
              have hrR : r ∈ R := hB0_sub_R x hx hr
              have hG : G r x = true := (Finset.mem_filter.mp hr).2
              have hrcR : r ∈ cR := Finset.mem_filter.mpr ⟨hrR, x, (Finset.mem_filter.mp hx).1, by rw [hG]; decide⟩
              refine Finset.mem_sdiff.mpr ⟨hrcR, ?_⟩
              intro hrU
              have hreq : nbrR r ∩ cB = nbrR a0 ∩ cB := (Finset.mem_filter.mp hrU).2
              have hmem : x ∈ nbrR a0 ∩ cB := by
                rw [← hreq]
                exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩, hxcB⟩
              exact hxn hmem
            have hle := (Finset.card_le_card hnx_sub).trans hrest_le1
            have h2 := (hnbrC x).1
            omega
          exact (Finset.card_le_card hsub).trans hN_le1
        have h1 := hR_le_dt (by omega)
        have h2 := hB_le_dt (by omega)
        omega
      · have hallV : ∀ a ∈ cR, (cB \ nbrR a).card ≤ 1 := by
          intro a ha
          by_contra hgt
          exact hexV ⟨a, ha, by omega⟩
        rcases Finset.one_lt_card.mp (by omega : 1 < cR.card) with ⟨a₁, ha₁, a₂, ha₂, ha12⟩
        have hcB_le3 : cB.card ≤ 3 := by
          have hsub : cB ⊆ (cB \ nbrR a₁) ∪ (cB \ nbrR a₂) ∪ (nbrR a₁ ∩ nbrR a₂) := by
            intro x hx
            by_cases h1 : x ∈ nbrR a₁
            · by_cases h2 : x ∈ nbrR a₂
              · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h1, h2⟩)
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, h2⟩))
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h1⟩))
          have hle := Finset.card_le_card hsub
          have hu1 := Finset.card_union_le ((cB \ nbrR a₁) ∪ (cB \ nbrR a₂)) (nbrR a₁ ∩ nbrR a₂)
          have hu2 := Finset.card_union_le (cB \ nbrR a₁) (cB \ nbrR a₂)
          have hv1 := hallV a₁ ha₁
          have hv2 := hallV a₂ ha₂
          have hi := hc4R a₁ a₂ ha12
          omega
        by_cases hcB2 : cB.card ≤ 2
        · have hR0le : R0.card ≤ d := (hR0_le1_of_cB_le2 hcB2).trans (by omega)
          have hB0le : B0.card ≤ d := (Finset.card_le_card hB0_sub_cB).trans (by omega)
          have h1 := hR_le_dt hR0le
          have h2 := hB_le_dt hB0le
          omega
        · have hcB3 : cB.card = 3 := by omega
          have hdeg_cR : ∀ a ∈ cR, (nbrR a ∩ cB).card = 2 := by
            intro a ha
            have hpart : (nbrR a ∩ cB).card + (cB \ nbrR a).card = cB.card := by
              have h := Finset.card_sdiff_add_card_inter cB (nbrR a)
              rw [Finset.inter_comm] at h
              exact Nat.add_comm _ _ ▸ h
            have hv := hallV a ha
            have hge2 : 2 ≤ (nbrR a ∩ cB).card := by omega
            have hle2 : (nbrR a ∩ cB).card ≤ 2 := by
              by_contra h3
              have hfull : nbrR a ∩ cB = cB :=
                Finset.eq_of_subset_of_card_le (Finset.inter_subset_right) (by omega)
              have hne : (cR.erase a).Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro hem
                have h1 := Finset.card_erase_of_mem ha
                rw [hem] at h1; simp at h1; omega
              rcases hne with ⟨b, hb⟩
              rcases Finset.mem_erase.mp hb with ⟨hba, hbcR⟩
              have hbpart : (nbrR b ∩ cB).card + (cB \ nbrR b).card = cB.card := by
                have h := Finset.card_sdiff_add_card_inter cB (nbrR b)
                rw [Finset.inter_comm] at h
                exact Nat.add_comm _ _ ▸ h
              have hvb := hallV b hbcR
              have hsub : nbrR b ∩ cB ⊆ nbrR a ∩ nbrR b := by
                intro x hx
                have hxcB : x ∈ cB := (Finset.mem_inter.mp hx).2
                have hxa : x ∈ nbrR a := (Finset.mem_inter.mp (hfull.symm ▸ hxcB)).1
                exact Finset.mem_inter.mpr ⟨hxa, (Finset.mem_inter.mp hx).1⟩
              have hle := Finset.card_le_card hsub
              have hi := hc4R a b (Ne.symm hba)
              omega
            omega
          have hcR_le3 : cR.card ≤ 3 := by
            have hmiss_card : ∀ a ∈ cR, (cB \ nbrR a).card = 1 := by
              intro a ha
              have hpart : (nbrR a ∩ cB).card + (cB \ nbrR a).card = cB.card := by
                have h := Finset.card_sdiff_add_card_inter cB (nbrR a)
                rw [Finset.inter_comm] at h
                exact Nat.add_comm _ _ ▸ h
              have h2 := hdeg_cR a ha
              omega
            have hchoose : ∀ a : Fin n, ∃ x : Fin m, a ∈ cR → cB \ nbrR a = {x} := by
              intro a
              by_cases ha : a ∈ cR
              · rcases Finset.card_eq_one.mp (hmiss_card a ha) with ⟨x, hx⟩
                exact ⟨x, fun _ => hx⟩
              · rcases Finset.card_pos.mp (by omega : 0 < cB.card) with ⟨x0, _⟩
                exact ⟨x0, fun h1 => absurd h1 ha⟩
            choose miss hmiss using hchoose
            have hmiss_mem : ∀ a ∈ cR, miss a ∈ cB := by
              intro a ha
              have hm : miss a ∈ cB \ nbrR a := by rw [hmiss a ha]; simp
              exact (Finset.mem_sdiff.mp hm).1
            have hmiss_inj : Set.InjOn miss (cR : Set (Fin n)) := by
              intro a ha b hb heq
              by_contra hab
              have hsdiff_eq : cB \ nbrR a = cB \ nbrR b := by rw [hmiss a ha, hmiss b hb, heq]
              have hinter_eq : nbrR a ∩ cB = nbrR b ∩ cB := by
                ext x
                have h1 := Finset.ext_iff.mp hsdiff_eq x
                simp only [Finset.mem_inter, Finset.mem_sdiff] at h1 ⊢
                constructor <;> rintro ⟨hx1, hx2⟩ <;> refine ⟨?_, hx2⟩
                · by_contra hnb
                  have := h1.mpr ⟨hx2, hnb⟩
                  exact this.2 hx1
                · by_contra hna
                  have := h1.mp ⟨hx2, hna⟩
                  exact this.2 hx1
              have hsub : nbrR a ∩ cB ⊆ nbrR a ∩ nbrR b := by
                intro x hx
                exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp (hinter_eq ▸ hx)).1⟩
              have hle := Finset.card_le_card hsub
              have h2 := hdeg_cR a ha
              have hi := hc4R a b hab
              omega
            calc cR.card ≤ cB.card := Finset.card_le_card_of_injOn miss hmiss_mem hmiss_inj
              _ = 3 := hcB3
          by_cases hd3 : 3 ≤ d
          · have hR0le : R0.card ≤ d := (Finset.card_le_card hR0_sub_cR).trans (by omega)
            have hB0le : B0.card ≤ d := (Finset.card_le_card hB0_sub_cB).trans (by omega)
            have h1 := hR_le_dt hR0le
            have h2 := hB_le_dt hB0le
            omega
          · have hd2 : d = 2 := by omega
            have hcR3_eq : cR.card = 3 := by omega
            have hR0_eq_cR : R0 = cR := by
              apply Finset.Subset.antisymm hR0_sub_cR
              intro a ha
              refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, ?_⟩
              have hsub : nbrR a ∩ cB ⊆ nbrR a := Finset.inter_subset_left
              have heq : nbrR a ∩ cB = nbrR a :=
                Finset.eq_of_subset_of_card_le hsub (by have := (hnbrR a).2; have := hdeg_cR a ha; omega)
              rw [Finset.eq_empty_iff_forall_notMem]
              intro c hc
              simp only [extR, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc
              have hcin : c ∈ nbrR a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.2⟩
              rw [← heq] at hcin
              exact hc.1 (Finset.mem_filter.mp (Finset.mem_inter.mp hcin).2).1
            have hdeg_cB : ∀ x ∈ cB, (nbrC x ∩ cR).card = 2 := by
              have hsum_eq : ∑ a ∈ cR, (nbrR a ∩ cB).card = ∑ x ∈ cB, (nbrC x ∩ cR).card := by
                have hL : ∑ a ∈ cR, (nbrR a ∩ cB).card =
                    ∑ a ∈ cR, ∑ x ∈ cB, if G a x = true then 1 else 0 := by
                  apply Finset.sum_congr rfl
                  intro a _
                  rw [← Finset.card_filter]
                  congr 1
                  ext x
                  simp only [nbrR, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
                  tauto
                have hR : ∑ x ∈ cB, (nbrC x ∩ cR).card =
                    ∑ x ∈ cB, ∑ a ∈ cR, if G a x = true then 1 else 0 := by
                  apply Finset.sum_congr rfl
                  intro x _
                  rw [← Finset.card_filter]
                  congr 1
                  ext a
                  simp only [nbrC, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
                  tauto
                rw [hL, hR, Finset.sum_comm]
              have hsum6 : ∑ x ∈ cB, (nbrC x ∩ cR).card = 6 := by
                rw [← hsum_eq]
                calc ∑ a ∈ cR, (nbrR a ∩ cB).card = ∑ _a ∈ cR, 2 := Finset.sum_congr rfl hdeg_cR
                  _ = cR.card * 2 := by simp
                  _ = 6 := by omega
              intro x hx
              have hle2 : ∀ y ∈ cB, (nbrC y ∩ cR).card ≤ 2 := fun y _ =>
                (Finset.card_le_card Finset.inter_subset_left).trans (by have := (hnbrC y).2; omega)
              by_contra hne2
              have hlt2 : (nbrC x ∩ cR).card ≤ 1 := by have := hle2 x hx; omega
              have hsum_lt : ∑ y ∈ cB, (nbrC y ∩ cR).card ≤ 5 := by
                rw [← Finset.add_sum_erase _ _ hx]
                have hrest : ∑ y ∈ cB.erase x, (nbrC y ∩ cR).card ≤ (cB.erase x).card * 2 := by
                  calc ∑ y ∈ cB.erase x, (nbrC y ∩ cR).card
                      ≤ ∑ _y ∈ cB.erase x, 2 := Finset.sum_le_sum (fun y hy => hle2 y (Finset.mem_of_mem_erase hy))
                    _ = (cB.erase x).card * 2 := by simp
                have her : (cB.erase x).card = 2 := by rw [Finset.card_erase_of_mem hx, hcB3]
                omega
              omega
            have hB0_eq_cB : B0 = cB := by
              apply Finset.Subset.antisymm hB0_sub_cB
              intro x hx
              refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, ?_⟩
              have hsub : nbrC x ∩ cR ⊆ nbrC x := Finset.inter_subset_left
              have heq : nbrC x ∩ cR = nbrC x :=
                Finset.eq_of_subset_of_card_le hsub (by have := (hnbrC x).2; have := hdeg_cB x hx; omega)
              rw [Finset.eq_empty_iff_forall_notMem]
              intro a ha
              simp only [extC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha
              have hain : a ∈ nbrC x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.2⟩
              rw [← heq] at hain
              exact ha.1 (Finset.mem_filter.mp (Finset.mem_inter.mp hain).2).1
            have hR1_le : R1.card ≤ t - 1 := by
              have hinj : Set.InjOn extR (R1 : Set (Fin n)) := by
                intro a ha b hb heq
                by_contra hab
                have han0 : a ∉ cR := by
                  rw [← hR0_eq_cR]
                  intro ha0
                  exact (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp ha0).2
                have ha_sub : nbrR a ⊆ extR a := by
                  intro c hc
                  have hcB : c ∉ B := by
                    intro hcB
                    exact han0 (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, c, hcB, by rw [(Finset.mem_filter.mp hc).2]; decide⟩)
                  exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcB⟩, (Finset.mem_filter.mp hc).2⟩
                have hsub : extR a ⊆ nbrR a ∩ nbrR b := by
                  intro c hc
                  have hcb : c ∈ extR b := heq ▸ hc
                  exact Finset.mem_inter.mpr ⟨
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩,
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hcb).2⟩⟩
                have hle := (Finset.card_le_card ha_sub).trans ((Finset.card_le_card hsub).trans (hc4R a b hab))
                have h2 := (hnbrR a).1
                omega
              have hmem0 : (∅ : Finset (Fin m)) ∈ R.image extR := by
                rcases Finset.card_pos.mp (by rw [hR0_eq_cR]; omega : 0 < R0.card) with ⟨a, ha⟩
                exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩
              have hsub : R1.image extR ⊆ (R.image extR).erase ∅ := by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
                exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp ha).2,
                  Finset.mem_image_of_mem extR (Finset.mem_filter.mp ha).1⟩
              rw [← Finset.card_image_of_injOn hinj]
              have hle := Finset.card_le_card hsub
              rw [Finset.card_erase_of_mem hmem0] at hle
              omega
            have hB1_le : B1.card ≤ t - 1 := by
              have hinj : Set.InjOn extC (B1 : Set (Fin m)) := by
                intro x hx y hy heq
                by_contra hxy
                have hxn0 : x ∉ cB := by
                  rw [← hB0_eq_cB]
                  intro hx0
                  exact (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx0).2
                have hx_sub : nbrC x ⊆ extC x := by
                  intro a ha
                  have haR : a ∉ R := by
                    intro haR
                    exact hxn0 (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, a, haR, by rw [(Finset.mem_filter.mp ha).2]; decide⟩)
                  exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haR⟩, (Finset.mem_filter.mp ha).2⟩
                have hsub : extC x ⊆ nbrC x ∩ nbrC y := by
                  intro a ha
                  have hay : a ∈ extC y := heq ▸ ha
                  exact Finset.mem_inter.mpr ⟨
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩,
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hay).2⟩⟩
                have hle := (Finset.card_le_card hx_sub).trans ((Finset.card_le_card hsub).trans (hc4C x y hxy))
                have h2 := (hnbrC x).1
                omega
              have hmem0 : (∅ : Finset (Fin n)) ∈ B.image extC := by
                rcases Finset.card_pos.mp (by rw [hB0_eq_cB]; omega : 0 < B0.card) with ⟨x, hx⟩
                exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
              have hsub : B1.image extC ⊆ (B.image extC).erase ∅ := by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨x, hx, rfl⟩
                exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hx).2,
                  Finset.mem_image_of_mem extC (Finset.mem_filter.mp hx).1⟩
              rw [← Finset.card_image_of_injOn hinj]
              have hle := Finset.card_le_card hsub
              rw [Finset.card_erase_of_mem hmem0] at hle
              omega
            rw [hR0_eq_cR, hcR3_eq] at hRsum
            rw [hB0_eq_cB, hcB3] at hBsum
            have h4t : 2 * d * t = 4 * t := by rw [hd2]
            omega
  · by_cases hfullR : ∃ a0 ∈ R, ∀ x ∈ B, G a0 x = true
    · rcases hfullR with ⟨a0, _, ha0⟩
      have hB_le_d : B.card ≤ d := by
        have hsub : B ⊆ nbrR a0 := fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha0 x hx⟩
        exact (Finset.card_le_card hsub).trans (hnbrR a0).2
      have hR0_le1 : R0.card ≤ 1 := by
        have hsub : R0 ⊆ {a0} := by
          intro a ha
          simp only [Finset.mem_singleton]
          by_contra ha0ne
          have hsub2 : nbrR a ⊆ nbrR a ∩ nbrR a0 := by
            intro x hx
            exact Finset.mem_inter.mpr ⟨hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha0 x (hR0_sub_B a ha hx)⟩⟩
          have hle := (Finset.card_le_card hsub2).trans (hc4R a a0 ha0ne)
          have h2 := (hnbrR a).1
          omega
        exact (Finset.card_le_card hsub).trans (by simp)
      have hRle := hR_le_dt (by omega)
      have hdt_ge : d ≤ d * t := by
        calc d = d * 1 := (Nat.mul_one d).symm
          _ ≤ d * t := Nat.mul_le_mul_left d (by omega)
      omega
    · by_cases hfullB : ∃ c0 ∈ B, ∀ a ∈ R, G a c0 = true
      · rcases hfullB with ⟨c0, _, hc0⟩
        have hR_le_d : R.card ≤ d := by
          have hsub : R ⊆ nbrC c0 := fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0 a ha⟩
          exact (Finset.card_le_card hsub).trans (hnbrC c0).2
        have hB0_le1 : B0.card ≤ 1 := by
          have hsub : B0 ⊆ {c0} := by
            intro c hc
            simp only [Finset.mem_singleton]
            by_contra hc0ne
            have hsub2 : nbrC c ⊆ nbrC c ∩ nbrC c0 := by
              intro a ha
              exact Finset.mem_inter.mpr ⟨ha, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0 a (hB0_sub_R c hc ha)⟩⟩
            have hle := (Finset.card_le_card hsub2).trans (hc4C c c0 hc0ne)
            have h2 := (hnbrC c).1
            omega
          exact (Finset.card_le_card hsub).trans (by simp)
        have hBle := hB_le_dt (by omega)
        have hdt_ge : d ≤ d * t := by
          calc d = d * 1 := (Nat.mul_one d).symm
            _ ≤ d * t := Nat.mul_le_mul_left d (by omega)
        omega
      · have hrect_all : ∀ a ∈ R, ∀ b ∈ R, ∀ x ∈ B, ∀ y ∈ B,
            G a x = true → G b x = true → G b y = true → G a y = true := by
          intro a ha b hb x hx y hy hax hbx hby
          have hcoreR : ∀ r ∈ R, r ∈ R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ true) := by
            intro r hr
            refine Finset.mem_filter.mpr ⟨hr, ?_⟩
            by_contra hno
            apply hfullR
            refine ⟨r, hr, fun w hw => ?_⟩
            cases hG : G r w
            · exact absurd ⟨w, hw, by rw [hG]; decide⟩ hno
            · rfl
          have hcoreC : ∀ c ∈ B, c ∈ B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ true) := by
            intro c hc
            refine Finset.mem_filter.mpr ⟨hc, ?_⟩
            by_contra hno
            apply hfullB
            refine ⟨c, hc, fun w hw => ?_⟩
            cases hG : G w c
            · exact absurd ⟨w, hw, by rw [hG]; decide⟩ hno
            · rfl
          exact hrect a (hcoreR a ha) b (hcoreR b hb) x (hcoreC x hx) y (hcoreC y hy) hax hbx hby
        by_cases hR0ne : R0.Nonempty
        · by_cases hB0ne : B0.Nonempty
          · have hR1_le_L : R1.card ≤ L := by
              have hmem0 : (∅ : Finset (Fin m)) ∈ R.image extR := by
                rcases hR0ne with ⟨a, ha⟩
                exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩
              have hsub : R1.image extR ⊆ (R.image extR).erase ∅ := by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
                exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp ha).2,
                  Finset.mem_image_of_mem extR (Finset.mem_filter.mp ha).1⟩
              have him1 : (R1.image extR).card ≤ t - 1 := by
                have h1 := Finset.card_le_card hsub
                rw [Finset.card_erase_of_mem hmem0] at h1
                omega
              have hle := card_le_mul_of_fiber_bound R1 extR (t - 1) d him1 (by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
                have hPne : (extR a).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp ha).2
                calc (R1.filter (fun r => extR r = extR a)).card
                    ≤ (R.filter (fun r => extR r = extR a)).card := by
                      apply Finset.card_le_card
                      intro r hr
                      simp only [R1, Finset.mem_filter] at hr ⊢
                      exact ⟨hr.1.1, hr.2⟩
                  _ ≤ d := hfibR (extR a) hPne)
              rw [Nat.mul_comm] at hle
              exact hle
            have hB1_le_L : B1.card ≤ L := by
              have hmem0 : (∅ : Finset (Fin n)) ∈ B.image extC := by
                rcases hB0ne with ⟨c, hc⟩
                exact Finset.mem_image.mpr ⟨c, (Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2⟩
              have hsub : B1.image extC ⊆ (B.image extC).erase ∅ := by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨c, hc, rfl⟩
                exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hc).2,
                  Finset.mem_image_of_mem extC (Finset.mem_filter.mp hc).1⟩
              have him1 : (B1.image extC).card ≤ t - 1 := by
                have h1 := Finset.card_le_card hsub
                rw [Finset.card_erase_of_mem hmem0] at h1
                omega
              have hle := card_le_mul_of_fiber_bound B1 extC (t - 1) d him1 (by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨c, hc, rfl⟩
                have hPne : (extC c).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hc).2
                calc (B1.filter (fun x => extC x = extC c)).card
                    ≤ (B.filter (fun x => extC x = extC c)).card := by
                      apply Finset.card_le_card
                      intro x hx
                      simp only [B1, Finset.mem_filter] at hx ⊢
                      exact ⟨hx.1.1, hx.2⟩
                  _ ≤ d := hfibB (extC c) hPne)
              rw [Nat.mul_comm] at hle
              exact hle
            have hstar_R0 : ∀ a ∈ R0, ∀ x ∈ nbrR a, ∀ b ∈ R, G b x = true → b = a := by
              intro a ha x hx b hb hbx
              have haR : a ∈ R := (Finset.mem_filter.mp ha).1
              have hxB : x ∈ B := hR0_sub_B a ha hx
              by_contra hba
              have hne : ((nbrR a).erase x).Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro hem
                have h1 := Finset.card_erase_of_mem hx
                rw [hem] at h1; simp at h1
                have h2 := (hnbrR a).1
                omega
              rcases hne with ⟨y, hy⟩
              rcases Finset.mem_erase.mp hy with ⟨hyx, hyN⟩
              have hyB : y ∈ B := hR0_sub_B a ha hyN
              have hax : G a x = true := (Finset.mem_filter.mp hx).2
              have hay : G a y = true := (Finset.mem_filter.mp hyN).2
              have hby : G b y = true := hrect_all b hb a haR x hxB y hyB hbx hax hay
              have hsub : ({x, y} : Finset (Fin m)) ⊆ nbrR a ∩ nbrR b := by
                intro c hc
                simp only [Finset.mem_insert, Finset.mem_singleton] at hc
                simp only [nbrR, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
                rcases hc with rfl | rfl
                · exact ⟨hax, hbx⟩
                · exact ⟨hay, hby⟩
              have hpair : ({x, y} : Finset (Fin m)).card = 2 := Finset.card_pair (Ne.symm hyx)
              have hle := Finset.card_le_card hsub
              have h1 := hc4R a b (Ne.symm hba)
              omega
            have hstar_B0 : ∀ x ∈ B0, ∀ a ∈ nbrC x, ∀ y ∈ B, G a y = true → y = x := by
              intro x hx a ha y hy hay
              have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
              have haR : a ∈ R := hB0_sub_R x hx ha
              by_contra hyx
              have hne : ((nbrC x).erase a).Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro hem
                have h1 := Finset.card_erase_of_mem ha
                rw [hem] at h1; simp at h1
                have h2 := (hnbrC x).1
                omega
              rcases hne with ⟨b, hb⟩
              rcases Finset.mem_erase.mp hb with ⟨hba, hbN⟩
              have hbR : b ∈ R := hB0_sub_R x hx hbN
              have hax : G a x = true := (Finset.mem_filter.mp ha).2
              have hbx : G b x = true := (Finset.mem_filter.mp hbN).2
              have hby : G b y = true := hrect_all b hbR a haR x hxB y hy hbx hax hay
              have hsub : ({a, b} : Finset (Fin n)) ⊆ nbrC x ∩ nbrC y := by
                intro r hr
                simp only [Finset.mem_insert, Finset.mem_singleton] at hr
                simp only [nbrC, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
                rcases hr with rfl | rfl
                · exact ⟨hax, hay⟩
                · exact ⟨hbx, hby⟩
              have hpair : ({a, b} : Finset (Fin n)).card = 2 := Finset.card_pair (Ne.symm hba)
              have hle := Finset.card_le_card hsub
              have h1 := hc4C x y (Ne.symm hyx)
              omega
            have h2R0_le_B1 : 2 * R0.card ≤ B1.card := by
              have hsub : R0.biUnion nbrR ⊆ B1 := by
                intro x hx
                rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hax⟩
                have hxB : x ∈ B := hR0_sub_B a ha hax
                refine Finset.mem_filter.mpr ⟨hxB, ?_⟩
                intro hx0
                have hne : ((nbrC x).erase a).Nonempty := by
                  rw [Finset.nonempty_iff_ne_empty]
                  intro hem
                  have haN : a ∈ nbrC x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hax).2⟩
                  have h1 := Finset.card_erase_of_mem haN
                  rw [hem] at h1; simp at h1
                  have h2 := (hnbrC x).1
                  omega
                rcases hne with ⟨b, hb⟩
                rcases Finset.mem_erase.mp hb with ⟨hba, hbN⟩
                have hbR : b ∈ R := hB0_sub_R x (Finset.mem_filter.mpr ⟨hxB, hx0⟩) hbN
                exact hba (hstar_R0 a ha x hax b hbR (Finset.mem_filter.mp hbN).2)
              have hdisj : Set.PairwiseDisjoint (R0 : Set (Fin n)) nbrR := by
                intro a ha b hb hab
                dsimp only [Function.onFun]
                rw [Finset.disjoint_left]
                intro x hax hbx
                exact hab (hstar_R0 a ha x hax b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hbx).2).symm
              calc 2 * R0.card = ∑ _a ∈ R0, 2 := by simp [Nat.mul_comm]
                _ ≤ ∑ a ∈ R0, (nbrR a).card := Finset.sum_le_sum (fun a _ => (hnbrR a).1)
                _ = (R0.biUnion nbrR).card := (Finset.card_biUnion hdisj).symm
                _ ≤ B1.card := Finset.card_le_card hsub
            have h2B0_le_R1 : 2 * B0.card ≤ R1.card := by
              have hsub : B0.biUnion nbrC ⊆ R1 := by
                intro a ha
                rcases Finset.mem_biUnion.mp ha with ⟨x, hx, hax⟩
                have haR : a ∈ R := hB0_sub_R x hx hax
                refine Finset.mem_filter.mpr ⟨haR, ?_⟩
                intro ha0
                have hne : ((nbrR a).erase x).Nonempty := by
                  rw [Finset.nonempty_iff_ne_empty]
                  intro hem
                  have hxN : x ∈ nbrR a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hax).2⟩
                  have h1 := Finset.card_erase_of_mem hxN
                  rw [hem] at h1; simp at h1
                  have h2 := (hnbrR a).1
                  omega
                rcases hne with ⟨y, hy⟩
                rcases Finset.mem_erase.mp hy with ⟨hyx, hyN⟩
                have hyB : y ∈ B := hR0_sub_B a (Finset.mem_filter.mpr ⟨haR, ha0⟩) hyN
                exact hyx (hstar_B0 x hx a hax y hyB (Finset.mem_filter.mp hyN).2)
              have hdisj : Set.PairwiseDisjoint (B0 : Set (Fin m)) nbrC := by
                intro x hx y hy hxy
                dsimp only [Function.onFun]
                rw [Finset.disjoint_left]
                intro a hax hay
                exact hxy (hstar_B0 x hx a hax y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hay).2).symm
              calc 2 * B0.card = ∑ _x ∈ B0, 2 := by simp [Nat.mul_comm]
                _ ≤ ∑ x ∈ B0, (nbrC x).card := Finset.sum_le_sum (fun x _ => (hnbrC x).1)
                _ = (B0.biUnion nbrC).card := (Finset.card_biUnion hdisj).symm
                _ ≤ R1.card := Finset.card_le_card hsub
            omega
          · have hB0em : B0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB0ne
            have hT := upper_bound_one_empty_side d t m n (fun c a => G a c) B R hd ht
              hnbrC hnbrR hc4C hcolT hrowT
              (fun x hx y hy a ha b hb hxa hya hyb => hrect_all b hb a ha y hy x hx hyb hya hxa)
              hB0em hR0ne
            omega
        · by_cases hB0ne : B0.Nonempty
          · have hR0em : R0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR0ne
            exact upper_bound_one_empty_side d t n m G R B hd ht
              hnbrR hnbrC hc4R hrowT hcolT hrect_all hR0em hB0ne
          · have hR0em : R0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR0ne
            have hB0em : B0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB0ne
            have h1 := hR_le_dt (by rw [hR0em]; simp)
            have h2 := hB_le_dt (by rw [hB0em]; simp)
            omega

theorem upper (d t n m : ℕ) (G : Fin n → Fin m → Bool) (edge : Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (hd : 2≤d) (ht : 2≤t)
    (h : admissible d t n m G edge R B) :
    R.card+B.card ≤ max (2*d*t) (2*(d*(t-1))+2*(d*(t-1)/2)) := by
  have hp := (admissible_flip d t n m G edge R B).mp h
  exact upper_bound_true d t n m (fun a c => G a c == edge) R B hd ht hp

end CutLib25855.Sparse

namespace CutLib25855
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def neigh {n m : ℕ} (G : Fin n → Fin m → Bool) (e : Bool) (a : Fin n) :=
  Finset.univ.filter (fun c => G a c=e)
def transpose {n m : ℕ} (G : Fin n → Fin m → Bool) := fun (c : Fin m) (a : Fin n) => G a c
def degree {n m : ℕ} (G : Fin n → Fin m → Bool) (e : Bool) (d : ℕ) :=
  ∀ a, 2≤(neigh G e a).card ∧ (neigh G e a).card≤d
def acyclicFour {n m : ℕ} (G : Fin n → Fin m → Bool) (e : Bool) :=
  ∀ a b, a≠b → ((neigh G e a) ∩ (neigh G e b)).card≤1

theorem acyclic_transpose {n m : ℕ} (G : Fin n → Fin m → Bool) (e : Bool) (hr : acyclicFour G e) :
    acyclicFour (transpose G) e := by
  classical
  intro c d neq
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra ab
  have sub : ({c,d} : Finset (Fin m))⊆(neigh G e a) ∩ (neigh G e b) := by
    have atA := Finset.mem_inter.mp ha
    have atB := Finset.mem_inter.mp hb
    have ac : G a c=e := (Finset.mem_filter.mp atA.1).2
    have ad : G a d=e := (Finset.mem_filter.mp atA.2).2
    have bc : G b c=e := (Finset.mem_filter.mp atB.1).2
    have bd : G b d=e := (Finset.mem_filter.mp atB.2).2
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    simp only [Finset.mem_inter,neigh,Finset.mem_filter,Finset.mem_univ,true_and]
    rcases hz with rfl|rfl
    · exact ⟨ac,bc⟩
    · exact ⟨ad,bd⟩
  have le := Finset.card_le_card sub
  rw [Finset.card_pair neq] at le
  have one := hr a b ab
  omega

theorem sparse_data {n m d : ℕ} (G : Fin n → Fin m → Bool) (e : Bool) (large : 3<n+m)
    (rdeg : degree G e d) (cdeg : degree (transpose G) e d) (fourFree : acyclicFour G e) :
    DifferentRows G ∧ DifferentCols G ∧ (∃ a c k, G a c≠G a k) ∧ (∃ a b c, G a c≠G b c) := by
  classical
  have diff {i j : ℕ} (H : Fin i → Fin j → Bool) (deg : degree H e d) (noFour : acyclicFour H e) :
      DifferentRows H := by
    intro a b neq
    by_contra! equal
    have same : neigh H e a=neigh H e b := by ext c; simp [neigh,equal c]
    have h := noFour a b neq
    rw [same,Finset.inter_self] at h
    have two := (deg b).1
    omega
  have dr := diff G rdeg fourFree
  have dc := diff (transpose G) cdeg (acyclic_transpose G e fourFree)
  have dim {i j : ℕ} (H : Fin i → Fin j → Bool) (deg : degree H e d) (pos : 0 < i) : 2≤j := by
    let a : Fin i := ⟨0,pos⟩
    have small := (deg a).1
    have bound := (neigh H e a).card_le_univ
    simp only [Fintype.card_fin] at bound
    omega
  have nr : 2≤n := by by_contra! small; have h := dim (transpose G) cdeg (by omega); omega
  have nc := dim G rdeg (by omega)
  have pair {i : ℕ} (large : 2 ≤ i) : ∃ a b : Fin i, a≠b := by
    refine ⟨⟨0,by omega⟩,⟨1,by omega⟩,?_⟩
    intro eq; have h := congrArg Fin.val eq; change 0=1 at h; omega
  obtain ⟨a,b,ab⟩ := pair nr
  obtain ⟨c,k,ck⟩ := pair nc
  obtain ⟨row,x⟩ := dc c k ck
  obtain ⟨col,y⟩ := dr a b ab
  exact ⟨dr,dc,⟨row,c,k,x⟩,⟨a,b,col,y⟩⟩

theorem tree_cap {n m d : ℕ} (G : Fin n → Fin m → Bool) (e : Bool) (hd : 2≤d)
    (rdeg : degree G e d) (cdeg : degree (transpose G) e d) (fourFree : acyclicFour G e)
    (D : Circuit) (back : ReadsBack (n+m) D) (rep : Represents G D)
    (S E : Finset ℕ) (sub : S⊆Finset.range (n+m)) (one : E.card≤1)
    (tree : Partition.tree69 (n+m) D S E) :
    S.card ≤ max (2*d*(2+E.card)) (2*(d*((2+E.card)-1))+2*(d*((2+E.card)-1)/2)) := by
  classical
  obtain ⟨R,B,join,card⟩ := raw_parts S sub
  obtain ⟨region,root,h⟩ := tree
  dsimp only at h
  obtain ⟨inside,member,last,ports,gates,uses⟩ := h
  have t := rectangle n m G D R B region E root
  dsimp only at t
  rw [join] at t
  obtain ⟨profilesR,profilesC,rectangles⟩ := t back rep
    (fun _ hi => Finset.mem_range.mpr (Partition.ordinary_index69 (inside hi))) member one ports gates last uses
  rw [card]
  exact Sparse.upper d (2+E.card) n m G e R B hd (by omega)
    ⟨rdeg,cdeg,fourFree,profilesR,profilesC,rectangles⟩

theorem stronger {n m d : ℕ} (G : Fin n → Fin m → Bool) (e : Bool) (hd : 2≤d)
    (rdeg : degree G e d) (cdeg : degree (transpose G) e d) (fourFree : acyclicFour G e)
    (C : Circuit) (fan : FanInTwo C) (rep : Represents G C) :
    n+m≤C.size+3 ∧ (32*d+2)*(n+m)≤(32*d+1)*C.size+100*d+5 := by
  by_cases small : n+m≤3
  · have lim := Nat.mul_le_mul_left (32*d+2) small
    exact ⟨by omega,by nlinarith only [lim,hd,Nat.zero_le ((32*d+1)*C.size)]⟩
  obtain ⟨dr,dc,across,down⟩ := sparse_data G e (by omega) rdeg cdeg fourFree
  obtain ⟨D,smaller,repD,back,shape,pos,last,live⟩ := normalized C fan rep across down
  have missing := few_missing G D back repD (output_not_raw repD across down) dr dc
  change n+m≤used (n+m) D+2 at missing
  have balance := budget_eq D shape back pos live
  have caps := tree_cap G e hd rdeg cdeg fourFree D back repD
  have pureBound (S) (sub : S⊆Finset.range (n+m)) (tree : Partition.tree69 (n+m) D S ∅) : S.card≤4*d := by
    have bound := caps S ∅ sub (by simp) tree
    simp only [Finset.card_empty,Nat.add_zero] at bound
    omega
  have oneBound (S b) (sub : S⊆Finset.range (n+m)) (tree : Partition.tree69 (n+m) D S {b}) : S.card≤6*d := by
    have bound := caps S {b} sub (by simp) tree
    simp only [Finset.card_singleton] at bound
    omega
  have cap := account (n+m) D (4*d) (6*d) shape back pos last live pureBound oneBound
  have scaled := Nat.mul_le_mul_left (32*d+2) missing
  have total := congrArg (fun x => (32*d+1)*x) balance
  have order := Nat.mul_le_mul_left (32*d+1) smaller
  exact ⟨by omega,by nlinarith only [cap,scaled,total,order]⟩

end CutLib25855

namespace CutLib25855.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
noncomputable def price (op : GateOp) : Nat := if op=.not then 0 else 1
noncomputable def listed (gs : List Gate) : Nat := (gs.map (fun g=>price g.op)).sum
noncomputable def remaining (C : Circuit) (F : Finset Nat) (k : Nat) : Nat :=
  ∑ j∈Finset.range k, if j∈F then 0 else price (gateAt C j).op

theorem full_price (C : Circuit) : remaining C ∅ C.size=listed C.gates := by
  have appendOne (l : List Gate) (g : Gate) : listed (l++[g])=listed l+price g.op := by
    simp [listed]
  have below (k : Nat) (h : k≤C.gates.length) : remaining C ∅ k=listed (C.gates.take k) := by
    induction k with
    | zero => simp [remaining,listed]
    | succ k ih =>
      have low : k<C.gates.length:=by omega
      rw [List.take_succ_eq_append_getElem low]
      change (∑j∈Finset.range (k+1),if j∈(∅ : Finset Nat) then 0 else price (gateAt C j).op)=_
      rw [Finset.sum_range_succ]
      change remaining C ∅ k+_=_
      rw [ih (by omega)]
      rw [show gateAt C k=C.gates[k] from List.getD_eq_getElem _ _ low,appendOne] <;> simp
  simpa [Circuit.size] using below C.gates.length le_rfl

theorem blank_price (C : Circuit) (i : Fin C.gates.length) :
    let E : Circuit:=⟨C.gates.set i.val ⟨GateOp.or,[]⟩,C.output⟩
    remaining E {i.val} E.size≤listed C.gates := by
  intro E
  rw [←full_price C]
  have sizes : E.size=C.size := by simp [E,Circuit.size]
  unfold remaining; rw [sizes]; apply Finset.sum_le_sum
  intro j hj
  have low : j<C.gates.length:=Finset.mem_range.mp hj
  have newer : j<E.gates.length := by simpa [E] using low
  by_cases same : j=i.val
  · simp [same]
  · have ne : i.val≠j:=Ne.symm same
    simp [E,gateAt,List.getD_eq_getElem _ _ low,List.getD_eq_getElem _ _ newer,low,same,ne,List.getElem_set]

theorem emission_price (e : List Gate) (op : GateOp) (len : e.length≤1) (same : ∀g∈e,g.op=op) :
    listed e≤price op := by
  cases e with
  | nil => simp [listed]
  | cons g tail =>
    have h:=same g List.mem_cons_self
    have empty : tail=[] := List.length_eq_zero_iff.mp (by change tail.length+1≤1 at len;omega)
    subst tail; simp [listed,h]

theorem emitWeighted (P : Prop) (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hmon : P → op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
      (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, g.op=op → Good P g → (∀ t ∈ g.inputs, t < N + hs.length) →
      (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g same h1 h1' h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using same, by simpa using h1, by simpa using h1', ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  by_cases hn : op = GateOp.not
  · subst op
    rcases rs with _ | ⟨r, rs⟩
    · exact keep (.inl true) (by simp) (by intro y hy; rfl)
    · have hr := hv r (by simp)
      rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y hy; rfl)
      · exact add ⟨.not,[t]⟩ rfl ⟨Or.inl ⟨rfl,t,rfl⟩,hmon⟩ (by simpa using hr t rfl)
          (by intro y hy; rfl)
  have hop' : op = GateOp.and ∨ op = GateOp.or := by tauto
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop' with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop' with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop' with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.and,[t,q]⟩ rfl ⟨Or.inr ⟨Or.inl rfl,t,q,same,rfl⟩,fun _ => Or.inl rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.or,[t,q]⟩ rfl ⟨Or.inr ⟨Or.inr rfl,t,q,same,rfl⟩,fun _ => Or.inr rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
  · simp at hl

theorem engineWeighted {X : Type} (P : Prop) (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : FanInTwo C) (hmon : P → Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size + F.card ≤ C.size ∧ listed D.gates≤remaining C F C.size ∧
      ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k).card ≤ k ∧
      listed hs≤remaining C F (k) ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, by simp, by simp [listed,remaining], ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h5, h2, spent, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, Good P g) → (∀ g ∈ e, ∀ t ∈ g.inputs, t < M + hs.length) →
          (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          listed e≤(if k∈F then 0 else price (gateAt C k).op) →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      listed hs≤remaining C F (k + 1) ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he he' hr hlen charge hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · intro i hi t ht
          rw [List.getElem_append] at ht
          split_ifs at ht with hih
          · exact h5 i hih t ht
          · have hmem : e[i - hs.length]'(by simp at hi; omega) ∈ e := List.mem_iff_getElem.mpr ⟨_, _, rfl⟩
            have := he' _ hmem t ht
            omega
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · change listed (hs++e)≤remaining C F (k+1)
          have lhs : listed (hs++e)=listed hs+listed e := by simp [listed]
          rw [lhs,remaining,Finset.sum_range_succ]
          exact Nat.add_le_add spent charge
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp) (by simp [hkF]) (by simp [listed,hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (by simp [listed,hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, sameOps, e2, e2', e3, e4⟩ := emitWeighted P M hs C.gates[k].op hop (fun p => by simpa using (hmon p _ (List.getElem_mem hk')).1) (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e2' e3 (by simp [hkF]; exact e1) (by rw [if_neg hkF,show gateAt C k=C.gates[k] from List.getD_eq_getElem _ _ hk']; exact emission_price e C.gates[k].op e1 sameOps) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h5, h2, spent, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, ?_, h2, spent, fun x => ?_⟩
    · exact h1
    · intro j hj i hi
      have hj' : j < hs.length := hj
      have he : gateAt ⟨hs, t⟩ j = hs[j] := List.getD_eq_getElem _ _ hj'
      rw [he] at hi
      exact h5 j hj' i hi
    · have := hev x
      rw [hm] at this
      exact this.symm

theorem finishWeighted {X : Type} (P : Prop) (M : ℕ) (y : X → List Bool)
    (hy : ∀ x, (y x).length = M) (f : X → Bool)
    (hnc : ¬ ∃ b : Bool, ∀ x, f x = b) (C : Circuit)
    (hg : ∀ g ∈ C.gates, Good P g) (hb : ReadsBack M C) (hf : ∀ x, C.eval (y x) = f x) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size ≤ C.size ∧ listed D.gates≤listed C.gates ∧
      (∀ x, D.eval (y x) = f x) ∧
      ∀ i : Fin D.gates.length, M + i.val ≠ D.output →
        ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (M + i.val) := by
  classical
  have hex : ∃ k, ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧
      D.size ≤ k ∧ listed D.gates≤listed C.gates ∧ ∀ x, D.eval (y x) = f x := ⟨C.size, C, hg, hb, le_rfl, le_rfl, hf⟩
  obtain ⟨D, hgood, hback, hsize, hprice, hval⟩ := Nat.find_spec hex
  have hmin0 : Nat.find hex ≤ C.size := Nat.find_min' hex ⟨C, hg, hb, le_rfl, le_rfl, hf⟩
  refine ⟨D, hgood, hback, hsize.trans hmin0, hprice, hval, ?_⟩
  intro i hout
  by_contra hn
  have dead : ∀ k < D.gates.length, M + i.val ∉ (gateAt D k).inputs := by
    intro k hk hpin
    have hh := hback k hk _ hpin
    have later : i < (⟨k, hk⟩ : Fin D.gates.length) := by
      change i.val < k
      omega
    have eqg : D.gates.get ⟨k, hk⟩ = gateAt D k := (List.getD_eq_getElem _ _ hk).symm
    have hgk : Good P (D.gates.get ⟨k, hk⟩) := hgood _ (List.getElem_mem hk)
    have hread : reads (D.gates.get ⟨k, hk⟩) (M + i.val) ↔
        M + i.val ∈ (D.gates.get ⟨k, hk⟩).inputs := by
      apply good_read
      exact hgk
    exact hn ⟨⟨k, hk⟩, later, hread.2 (by rwa [eqg])⟩
  let E : Circuit := ⟨D.gates.set i.val ⟨GateOp.or, []⟩, D.output⟩
  have hdf : FanInTwo D := by apply good_fan; exact hgood
  have hdm : P → Monotone2 D := by
    intro hP
    apply good_mono <;> assumption
  obtain ⟨hef, hem, _, hes, heq, hzero⟩ :=
    blank_dead_signed P M D hdf hdm hback i.val i.isLt dead hout.symm
  have heval (x : X) : E.eval (y x) = f x := (heq _ (hy x)).trans (hval x)
  have hmarked : ∀ j ∈ ({i.val} : Finset ℕ), j < E.gates.length ∧
      ((∃ b, ∀ x, (run E.gates (y x)).getD (M + j) false = b) ∨
       ∃ w < M + j, ∀ x, (run E.gates (y x)).getD (M + j) false =
         (run E.gates (y x)).getD w false) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst j
    exact ⟨by simpa [E] using i.isLt, Or.inl ⟨false, fun x => hzero _ (hy x)⟩⟩
  obtain ⟨J, hJg, hJb, hJs, hpriceJ, hJv⟩ := engineWeighted P M M E y y hy hy {i.val} hef hem
    (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩)
    (fun ⟨b, h⟩ => hnc ⟨b, fun x => (heval x).symm.trans (h x)⟩) hmarked
  have lower : Nat.find hex ≤ J.size :=
    Nat.find_min' hex ⟨J, hJg, hJb, le_rfl, hpriceJ.trans ((blank_price D i).trans hprice), fun x => (hJv x).trans (heval x)⟩
  rw [Finset.card_singleton] at hJs
  change E.size = D.size at hes
  omega

end CutLib25855.Normalize

namespace CutLib25855
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
theorem normalizedCosts {n m : ℕ} {G : Fin n → Fin m → Bool} (C : Circuit) (fan : FanInTwo C)
    (rep : Represents G C) (horizontal : ∃ a c d, G a c ≠ G a d) (vertical : ∃ a b c, G a c ≠ G b c) :
    ∃ D : Circuit, D.size≤C.size ∧ Normalize.listed D.gates≤Normalize.listed C.gates ∧ Represents G D ∧ ReadsBack (n+m) D ∧
      (∀ g∈D.gates, ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1)) ∧
      0<D.size ∧ D.output+1=n+m+D.size ∧ (∀ j<D.size, j+1<D.size → 0<Active D (n+m+j)) := by
  classical
  let N := n+m
  let y (p : Fin n × Fin m) := oneEach p.1 p.2
  let f (p : Fin n × Fin m) := G p.1 p.2
  have len (p) : (y p).length=N := Normalize.oneEach_length _ _
  have nc : ¬∃ b : Bool, ∀ p, f p=b := by
    rintro ⟨z,h⟩
    obtain ⟨a,b,c,ne⟩ := vertical
    exact ne ((h (a,c)).trans (h (b,c)).symm)
  obtain ⟨E,shape,back,sz,ecost,values⟩ := Normalize.engineWeighted False N N C y y len len ∅ fan False.elim
    (fun w hw => Or.inr ⟨w,hw,fun _ => rfl⟩)
    (fun ⟨z,h⟩ => nc ⟨z,fun p => (rep p.1 p.2).symm.trans (h p)⟩) (by simp)
  have esize : E.size≤C.size := by simpa only [Finset.card_empty,Nat.add_zero] using sz
  obtain ⟨D,dshape,db,ds,dcost,dv,live⟩ := Normalize.finishWeighted False N y len f nc E shape back
    (fun p => (values p).trans (rep p.1 p.2))
  have dr : Represents G D := fun a c => dv (a,c)
  have out := output_not_raw dr horizontal vertical
  have bound : D.output<N+D.size := by
    by_contra! high
    apply nc; refine ⟨false,?_⟩; intro p
    rw [←dv p]
    change (Normalize.run D.gates (y p)).getD D.output false=false
    exact Normalize.past _ _ _ (by rw [len]; exact high)
  have pos : 0<D.size := by dsimp [N] at bound; omega
  let last : Fin D.gates.length := ⟨D.size-1,by change D.size-1<D.size; omega⟩
  have final : N+last.val=D.output := by
    by_contra no
    obtain ⟨j,lt,_⟩ := live last no
    have hj := j.isLt
    change D.size-1<j.val at lt
    change j.val<D.size at hj
    omega
  have lastEq : D.output+1=N+D.size := by change N+(D.size-1)=D.output at final; omega
  refine ⟨D,ds.trans esize,dcost.trans (ecost.trans_eq (Normalize.full_price C)),dr,db,?_,pos,lastEq,?_⟩
  · intro g hg
    rcases (dshape g hg).1 with ⟨op,a,h⟩|⟨op,a,b,_,h⟩
    · exact Or.inr ⟨op,by simp [h]⟩
    · exact Or.inl ⟨op,by simp [h]⟩
  · intro j hj nonfinal
    have ne : N+j≠D.output := by omega
    obtain ⟨p,_,usage⟩ := live ⟨j,hj⟩ ne
    have ray : (D.gates.get p)=gateAt D p.val := (List.getD_eq_getElem _ _ p.isLt).symm
    change Normalize.reads (D.gates.get p) (N+j) at usage
    rw [ray] at usage
    apply wire_positive p.isLt
    rcases usage with ⟨_,h⟩|⟨_,h⟩
    · cases l : (gateAt D p.val).inputs with
      | nil => simp [l] at h
      | cons a tail =>
        simp [l] at h
        exact List.mem_cons.mpr (Or.inl h.symm)
    · exact h

end CutLib25855

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def gates69 (C : Circuit) := Finset.range C.size
def reads69 (C : Circuit) (w : Nat) := readsIn C (gates69 C) w
noncomputable def neg69 (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>(gateAt C k).op=.not)
noncomputable def special (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact ((Finset.range (N+C.size)).filter (fun w=>2≤reads69 C w)) ∪
    (neg69 C).image (fun k=>N+k)
noncomputable def ordinary (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>N+k∉special N C)
noncomputable def exits69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈gates69 C \ ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∉special N C))
noncomputable def entries69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∈special N C))
def once69 (N : Nat) (C : Circuit) := (Finset.range N).filter (fun w=>reads69 C w=1)
def shapes69 (C : Circuit) : Prop := ∀g∈C.gates,
  ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1)

def tree69 (N : Nat) (C : Circuit) (S E : Finset Nat) : Prop := ∃ region : Finset Nat, ∃ root : Nat,
  let wires := S ∪ region.image (fun k=>N+k)
  let localReads := readsIn C region
  region ⊆ ordinary N C ∧ root∈wires ∧ localReads root=0 ∧
  (∀b∈E,b∉wires ∧ b<root ∧ localReads b=1) ∧
  (∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀w∈(gateAt C j).inputs, w∈wires ∨ w∈E) ∧
  (∀w∈wires,w≠root → localReads w=1 ∧ reads69 C w=1 ∧ C.output≠w)

theorem ordinary_reads69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    reads69 C (N+k)≤1 := by
  classical
  obtain ⟨hk,hn⟩:=Finset.mem_filter.mp h
  have lt : k<C.size := Finset.mem_range.mp hk
  by_contra! many
  exact hn (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩))

theorem ordinary_index69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    k<C.size := Finset.mem_range.mp (Finset.mem_filter.mp h).1

end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

noncomputable def color69 (N : Nat) (C : Circuit) (w : Nat) : Bool :=
  if w∈special N C then true else if w<N then false else
    (gateAt C (w-N)).inputs.any (fun v => if hv : v<w then color69 N C v else false)
termination_by w

noncomputable def split69 (N : Nat) (C : Circuit) :=
  (ordinary N C).filter (fun j=>2≤((gateAt C j).inputs.filter (color69 N C)).length)

noncomputable def keep69 (N : Nat) (C : Circuit) := ordinary N C \ split69 N C

theorem color_special {N w : Nat} {C : Circuit} (h : w∈special N C) : color69 N C w=true := by
  rw [color69,ite_eq_left h]

theorem color_raw {N w : Nat} {C : Circuit} (hw : w<N) (h : w∉special N C) :
    color69 N C w=false := by rw [color69,ite_eq_right h,ite_eq_left hw]

theorem color_ordinary_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈ordinary N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true := by
  have ns := (Finset.mem_filter.mp hj).2
  rw [color69,ite_eq_right ns,ite_eq_right (by omega : ¬N+j<N),Nat.add_sub_cancel_left,List.any_eq_true]
  apply exists_congr
  intro w
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩

theorem color_keep_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈keep69 N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true :=
  color_ordinary_iff back (Finset.mem_sdiff.mp hj).1

theorem marked_keep_slots {N j : Nat} {C : Circuit} (hj : j∈keep69 N C) :
    ((gateAt C j).inputs.filter (color69 N C)).length≤1 := by
  obtain ⟨ord,no⟩ := Finset.mem_sdiff.mp hj
  by_contra! two
  exact no (Finset.mem_filter.mpr ⟨ord,two⟩)

theorem color_split_all {N j : Nat} {C : Circuit} (sh : shapes69 C) (hj : j∈split69 N C) :
    ∀ w∈(gateAt C j).inputs,color69 N C w=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  have jlt : j<C.gates.length := ordinary_index69 ord
  have mem : gateAt C j∈C.gates := by simp [gateAt,jlt]
  have len : (gateAt C j).inputs.length≤2 := by rcases sh _ mem with h|h <;> omega
  apply List.length_filter_eq_length_iff.mp
  have hl := List.length_filter_le (p:=color69 N C) (l:=(gateAt C j).inputs)
  omega

theorem color_split_self {N j : Nat} {C : Circuit} (back : ReadsBack N C) (hj : j∈split69 N C) :
    color69 N C (N+j)=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  apply (color_ordinary_iff back ord).2
  rw [←List.countP_pos_iff,List.countP_eq_length_filter]
  omega

lemma maskedCount69 (l : List Nat) (A : Finset Nat) :
    l.countP (fun w=>decide (w∈A)) = ∑w∈A,l.count w := by
  classical
  let f := l.filter (fun w=>decide (w∈A))
  have sub : f.toFinset ⊆ A := by
    intro w hw
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change f.length=_
  calc
    _ = ∑w∈f.toFinset,f.count w := (List.sum_toFinset_count_eq_length f).symm
    _ = ∑w∈A,f.count w := Finset.sum_subset sub (fun _ _ h =>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))
    _ = _ := Finset.sum_congr rfl (fun w hw=>List.count_filter (by simpa using hw))

lemma countCover69 (l : List Nat) (p s a : Nat→Bool)
    (cover : ∀w∈l,p w=true → s w=true ∨ a w=true) : l.countP p≤l.countP s+l.countP a := by
  induction l with
  | nil => simp
  | cons w ws ih =>
    have tail := ih (fun v hv=>cover v (List.mem_cons_of_mem _ hv))
    have head := cover w List.mem_cons_self
    cases hp : p w <;> cases hs : s w <;> cases ha : a w <;> simp_all [List.countP_cons] <;> omega

theorem countedSlots69 {N : Nat} {C : Circuit} (P A : Finset Nat)
    (p : Nat→Bool) (pg : P⊆ordinary N C) (ag : A⊆ordinary N C)
    (cover : ∀ j∈P, ∀w∈(gateAt C j).inputs,p w=true →
      w∈special N C ∨ w∈A.image (fun t=>N+t)) :
    (∑j∈P,(gateAt C j).inputs.countP p)≤entries69 N C+A.card := by
  classical
  let I := A.image (fun j=>N+j)
  let specialSlot := fun w=>decide (w∈special N C)
  have each (j : Nat) (hj : j∈P) : (gateAt C j).inputs.countP p ≤
      (gateAt C j).inputs.countP specialSlot + ∑w∈I,(gateAt C j).inputs.count w := by
    rw [←maskedCount69]
    apply countCover69
    intro w hw hp
    exact (cover j hj w hw hp).imp (fun h=>by simpa [specialSlot] using h) (fun h=>by simpa [I] using h)
  have sl : (∑ j∈P,(gateAt C j).inputs.countP specialSlot) ≤ entries69 N C :=
    Finset.sum_le_sum_of_subset_of_nonneg pg (fun _ _ _ => Nat.zero_le _)
  have rest (w : Nat) (hw : w∈I) : (∑ j∈P,(gateAt C j).inputs.count w) ≤ 1 := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    apply le_trans (b:=reads69 C (N+j)) _ (ordinary_reads69 (ag hj))
    unfold reads69 readsIn
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
    exact fun q hq=>(Finset.mem_filter.mp (pg hq)).1
  have total := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,Finset.sum_comm (s:=P) (t:=I)] at total
  have pool := Finset.sum_le_sum rest
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at pool
  have cap : I.card≤A.card := Finset.card_image_le
  omega

theorem splitCard69 {N : Nat} {C : Circuit} (_sh : shapes69 C) (back : ReadsBack N C) :
    (split69 N C).card≤entries69 N C := by
  classical
  let A := (ordinary N C).filter (fun j=>color69 N C (N+j)=true)
  have cover (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (hl : color69 N C w=true) : w∈special N C ∨ w∈A.image (fun t=>N+t) := by
    by_cases sp : w∈special N C
    · exact Or.inl sp
    right
    have wire : w<N+j := back j (ordinary_index69 hj) w hw
    have mid : N≤w := by by_contra! z;rw [color_raw z sp] at hl;contradiction
    have eq : N+(w-N)=w := by omega
    have idx : w-N<C.size := by have := ordinary_index69 hj;omega
    have good : w-N∈ordinary N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,by simpa only [eq] using sp⟩
    exact Finset.mem_image.mpr ⟨w-N,Finset.mem_filter.mpr ⟨good,by simpa only [eq] using hl⟩,eq⟩
  have account := countedSlots69 (ordinary N C) A (color69 N C) (fun _ h=>h)
    (fun _ h=>(Finset.mem_filter.mp h).1) cover
  have pay (j : Nat) (hj : j∈ordinary N C) :
      (if color69 N C (N+j)=true then 1 else 0) +
      (if 2≤((gateAt C j).inputs.filter (color69 N C)).length then 1 else 0) ≤
      (gateAt C j).inputs.countP (color69 N C) := by
    rw [List.countP_eq_length_filter]
    by_cases many : 2≤((gateAt C j).inputs.filter (color69 N C)).length
    · rw [ite_eq_left many];split <;> omega
    rw [ite_eq_right many]
    split
    · next hc =>
      have has := (color_ordinary_iff back hj).1 hc
      have pos := List.countP_pos_iff.mpr has
      rw [List.countP_eq_length_filter] at pos
      omega
    · omega
  have total := Finset.sum_le_sum pay
  rw [Finset.sum_add_distrib,←Finset.card_filter,←Finset.card_filter] at total
  change A.card+(split69 N C).card≤_ at total
  omega

theorem entrySlotsBound69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) :
    (∑j∈keep69 N C,(gateAt C j).inputs.countP
      (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))) ≤ 2*entries69 N C := by
  classical
  have cap := countedSlots69 (keep69 N C) (split69 N C)
    (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
    (fun _ h=>(Finset.mem_sdiff.mp h).1) (fun _ h=>(Finset.mem_filter.mp h).1) (by
      intro j hj w hw h
      rcases of_decide_eq_true h with s|⟨low,idx⟩
      · exact Or.inl s
      · exact Or.inr (Finset.mem_image.mpr ⟨w-N,idx,by omega⟩))
  have splitBound := splitCard69 sh back
  omega

end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def pool69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  once69 N C ∪ P.image (fun k=>N+k)

def branch69 (N : Nat) (C : Circuit) (P : Finset Nat) (x y : Nat) : Prop :=
  x∈pool69 N C P ∧ ∃k∈P, y=N+k ∧ x∈(gateAt C k).inputs

abbrev walk69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  Relation.ReflTransGen (branch69 N C P)

def sink69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Prop :=
  ∀ y, ¬ branch69 N C P x y

noncomputable def owner69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Nat := by
  classical exact if h : ∃y,walk69 N C P x y ∧ sink69 N C P y then h.choose else x

noncomputable def roots69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  (once69 N C).image (owner69 N C P)

noncomputable def src69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (once69 N C).filter (fun w=>owner69 N C P w=z)

noncomputable def reg69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact P.filter (fun k=>owner69 N C P (N+k)=z)

noncomputable def outside69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (reg69 N C P z).biUnion fun k =>
    (gateAt C k).inputs.toFinset.filter (fun w=>w∉pool69 N C P)

noncomputable def slots69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Nat := by
  classical exact ∑ k∈reg69 N C P z,(gateAt C k).inputs.countP (fun w=>decide (w∉pool69 N C P))

variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem reads_le_one69 (hp : P⊆ordinary N C) {w : Nat} (hw : w∈pool69 N C P) : reads69 C w≤1 := by
  rcases Finset.mem_union.mp hw with h | h
  · exact (Finset.mem_filter.mp h).2.le
  · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp h;exact ordinary_reads69 (hp hk)

theorem reader69 {w i j : Nat} (one : reads69 C w≤1) (hi : i<C.size) (hj : j<C.size)
    (a : w∈(gateAt C i).inputs) (b : w∈(gateAt C j).inputs) : i=j := by
  by_contra ne
  have h:=Finset.add_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _)
    (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) ne
  have ai:=List.count_pos_iff.mpr a
  have bj:=List.count_pos_iff.mpr b
  change _ ≤ reads69 C w at h
  omega

theorem next_unique69 (hp : P⊆ordinary N C) : Relator.RightUnique (branch69 N C P) := by
  rintro w x y ⟨hw,i,hi,rfl,a⟩ ⟨_,j,hj,rfl,b⟩
  rw [reader69 (reads_le_one69 hp hw) (ordinary_index69 (hp hi)) (ordinary_index69 (hp hj)) a b]

theorem next_lt69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (h : branch69 N C P x y) : x<y ∧ y<N+C.size := by
  obtain ⟨_,k,hk,rfl,inp⟩:=h
  have lt:=ordinary_index69 (hp hk)
  exact ⟨back k lt x inp,by omega⟩

theorem walk_in69 {x y : Nat} (h : walk69 N C P x y) (hx : x∈pool69 N C P) :
    y∈pool69 N C P := by
  induction h with
  | refl => exact hx
  | tail _ e _ =>
    obtain ⟨_,k,hk,rfl,_⟩ := e
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)

theorem owner_spec69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (w : Nat) :
    walk69 N C P w (owner69 N C P w) ∧ sink69 N C P (owner69 N C P w) := by
  classical
  have exists' (i : Nat) : ∀x,N+C.size-x=i → ∃y,walk69 N C P x y ∧ sink69 N C P y := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro x eq
      by_cases e : ∃y,branch69 N C P x y
      · obtain ⟨y,hy⟩:=e
        obtain ⟨lt,bound⟩:=next_lt69 hp back hy
        obtain ⟨v,path,sink⟩:=ih (N+C.size-y) (by omega) y rfl
        exact ⟨v,path.head hy,sink⟩
      · exact ⟨x,.refl,fun y h=> e ⟨y,h⟩⟩
  have h:=exists' _ w rfl
  simpa only [owner69,dif_pos h] using h.choose_spec

theorem owner_same69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (e : branch69 N C P x y) : owner69 N C P x = owner69 N C P y := by
  have a := owner_spec69 hp back x
  have b := owner_spec69 hp back y
  have term {u v : Nat} (s : sink69 N C P u) (path : walk69 N C P u v) : u=v := by
    rcases path.cases_head with eq|⟨z,e,_⟩
    · exact eq
    · exact (s z e).elim
  rcases Relation.ReflTransGen.total_of_right_unique (next_unique69 hp)
    a.1 (b.1.head e) with h|h
  · exact term a.2 h
  · exact (term b.2 h).symm

theorem fiber69 (z w : Nat) :
    w∈src69 N C P z ∪ (reg69 N C P z).image (fun k=>N+k) ↔
      w∈pool69 N C P ∧ owner69 N C P w=z := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.mp h with a|b
    · obtain ⟨h,e⟩:=Finset.mem_filter.mp a;exact ⟨Finset.mem_union_left _ h,e⟩
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      obtain ⟨h,e⟩:=Finset.mem_filter.mp hk;exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ h),e⟩
  · rintro ⟨pool,e⟩
    rcases Finset.mem_union.mp pool with a|b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨a,e⟩)
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hk,e⟩))

theorem root_info69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    z∈pool69 N C P ∧ sink69 N C P z ∧ owner69 N C P z=z ∧ (src69 N C P z).Nonempty := by
  obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
  have sp:=owner_spec69 hp back u
  refine ⟨walk_in69 sp.1 (Finset.mem_union_left _ hu),sp.2,?_,⟨u,Finset.mem_filter.mpr ⟨hu,rfl⟩⟩⟩
  have p:=(owner_spec69 hp back (owner69 N C P u)).1
  rcases p.cases_head with eq|⟨x,step,_⟩
  · exact eq.symm
  · exact (sp.2 x step).elim

end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem root_zero69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    readsIn C (reg69 N C P z) z=0 := by
  obtain ⟨pool,sink,_,_⟩:=root_info69 hp back hz
  apply Finset.sum_eq_zero
  intro j hj;apply List.count_eq_zero.mpr
  intro h;exact sink (N+j) ⟨pool,j,(Finset.mem_filter.mp hj).1,rfl,h⟩

theorem local_read69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z w : Nat}
    (pool : w∈pool69 N C P) (ow : owner69 N C P w=z) (other : w≠z) :
    readsIn C (reg69 N C P z) w=1 ∧ reads69 C w=1 := by
  obtain ⟨way,_⟩:=owner_spec69 hp back w
  rw [ow] at way
  obtain ⟨_,⟨_,k,hk,rfl,hit⟩,_⟩:=way.cases_head.resolve_left other
  have eq := owner_same69 hp back (show branch69 N C P w (N+k) from ⟨pool,k,hk,rfl,hit⟩)
  have mem : k∈reg69 N C P z := Finset.mem_filter.mpr ⟨hk,eq.symm.trans ow⟩
  have le : (gateAt C k).inputs.count w ≤ readsIn C (reg69 N C P z) w :=
    Finset.single_le_sum (fun l _=>Nat.zero_le ((gateAt C l).inputs.count w)) mem
  have bound : readsIn C (reg69 N C P z) w ≤ reads69 C w :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun j hj =>
      Finset.mem_range.mpr (ordinary_index69 (hp (Finset.mem_filter.mp hj).1))) (fun _ _ _=>Nat.zero_le _)
  have counted:=List.count_pos_iff.mpr hit;have all:=reads_le_one69 hp pool
  omega

theorem pool_bound69 (hp : P⊆ordinary N C) {w : Nat} (pool : w∈pool69 N C P) : w<N+C.size := by
  rcases Finset.mem_union.mp pool with h|h
  · have lt:=Finset.mem_range.mp (Finset.mem_filter.mp h).1;omega
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h;have:=ordinary_index69 (hp hj);omega

theorem walk_le69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat} (path : walk69 N C P x y) :
    x≤y := by
  induction path with
  | refl => exact le_rfl
  | tail _ e ih => exact ih.trans (next_lt69 hp back e).1.le

theorem outside_mem69 {z w : Nat} :
    w∈outside69 N C P z ↔ w∉pool69 N C P ∧ ∃k∈reg69 N C P z,w∈(gateAt C k).inputs := by
  classical
  simp only [outside69,Finset.mem_biUnion,Finset.mem_filter,List.mem_toFinset]
  grind

theorem read_le_slots69 {z w : Nat} (out : w∉pool69 N C P) :
    readsIn C (reg69 N C P z) w ≤ slots69 N C P z := by
  classical
  apply Finset.sum_le_sum
  intro k _
  induction (gateAt C k).inputs with
  | nil => simp
  | cons a l ih =>
    simp only [decide_not] at ih
    by_cases eq : a=w
    · subst a;simp [List.count_cons,List.countP_cons,out,ih]
    · by_cases pa:a∈pool69 N C P <;> simp [List.count_cons,List.countP_cons,eq,pa,ih] <;> omega

theorem out_pos69 {z w : Nat} (h : w∈outside69 N C P z) :
    0<readsIn C (reg69 N C P z) w ∧ readsIn C (reg69 N C P z) w≤ slots69 N C P z := by
  obtain ⟨no,k,hk,hx⟩:=outside_mem69.mp h
  exact ⟨(List.count_pos_iff.mpr hx).trans_le
    (Finset.single_le_sum (fun j _=>Nat.zero_le ((gateAt C j).inputs.count w)) hk),read_le_slots69 no⟩

theorem outside_card69 {z : Nat} : (outside69 N C P z).card ≤ slots69 N C P z := by
  classical
  unfold outside69 slots69
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
  intro k _
  have h (l : List Nat) : (l.toFinset.filter (fun w=>w∉pool69 N C P)).card ≤
      l.countP (fun w=>decide (w∉pool69 N C P)) := by
    induction l with
    | nil => simp
    | cons w l ih =>
      simp only [decide_not] at ih
      by_cases hw:w∈pool69 N C P
      · simpa [Finset.filter_insert,hw,List.countP_cons] using ih
      · simp [Finset.filter_insert,hw,List.countP_cons]
        exact (Finset.card_insert_le _ _).trans (by omega)
  exact h _

theorem outside_empty69 {z : Nat} : outside69 N C P z=∅ ↔ slots69 N C P z=0 := by
  classical
  constructor
  · intro empty;apply Finset.sum_eq_zero;intro k hk
    apply List.countP_eq_zero.mpr
    intro w hw
    simp only [Bool.not_eq_true,decide_eq_false_iff_not,not_not]
    by_contra out
    have h : w∈outside69 N C P z := outside_mem69.mpr ⟨out,k,hk,hw⟩
    simp [empty] at h
  · intro z0;apply Finset.card_eq_zero.mp;have le:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z);omega

theorem subtree69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (sh : shapes69 C)
    (last : C.output+1=N+C.size) {z : Nat} (hz : z∈roots69 N C P)
    (slot : slots69 N C P z≤1) : tree69 N C (src69 N C P z) (outside69 N C P z) := by
  classical
  obtain ⟨zp,sink,zown,nonempty⟩:=root_info69 hp back hz
  have bound:=pool_bound69 hp zp
  refine ⟨reg69 N C P z,z,fun j hj=>hp (Finset.mem_filter.mp hj).1,
    (fiber69 z z).mpr ⟨zp,zown⟩,root_zero69 hp back hz,?_,?_,?_⟩
  · intro w hw
    obtain ⟨out,k,hk,read⟩:=outside_mem69.mp hw
    have lt:=back k (ordinary_index69 (hp (Finset.mem_filter.mp hk).1)) w read
    have path:=(owner_spec69 hp back (N+k)).1
    rw [(Finset.mem_filter.mp hk).2] at path
    have cmp:=walk_le69 hp back path
    obtain ⟨pos,le⟩:=out_pos69 hw
    exact ⟨fun h=>out ((fiber69 z w).mp h).1,by omega,by omega⟩
  · intro j hj
    obtain ⟨keep,own⟩:=Finset.mem_filter.mp hj
    have ord:=hp keep;have jl:=ordinary_index69 ord
    have mem : gateAt C j∈C.gates := by have h:j<C.gates.length:=jl;simp [gateAt,h]
    rcases sh _ mem with ao | no
    · refine ⟨ao.1,ao.2,?_⟩
      intro w wh
      by_cases pooled:w∈pool69 N C P
      · exact Or.inl ((fiber69 z w).mpr ⟨pooled,(owner_same69 hp back ⟨pooled,j,keep,rfl,wh⟩).trans own⟩)
      · exact Or.inr (outside_mem69.mpr ⟨pooled,j,hj,wh⟩)
    · have ns: N+j∉special N C := (Finset.mem_filter.mp ord).2
      apply (ns (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (show j∈neg69 C from Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jl,no.1⟩)))).elim
  · intro w hw diff
    obtain ⟨pool,own⟩:=(fiber69 z w).mp hw
    obtain ⟨loc,all⟩:=local_read69 hp back pool own diff
    have path:=(owner_spec69 hp back w).1
    rw [own] at path
    have le:=walk_le69 hp back path
    exact ⟨loc,all,by omega⟩

end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C:Circuit}
lemma keepSub69 : keep69 N C ⊆ ordinary N C := Finset.sdiff_subset
lemma colorOnce69 {w:Nat} (h:w∈once69 N C) : color69 N C w=false := by
  obtain ⟨hw,one⟩:=Finset.mem_filter.mp h
  have lo:=Finset.mem_range.mp hw
  apply color_raw lo
  intro hs
  rcases Finset.mem_union.mp hs with rep|notw
  · have high:2≤reads69 C w := (Finset.mem_filter.mp rep).2
    omega
  · obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp notw;omega
lemma colorOuter69 (back:ReadsBack N C) {j w:Nat} (hp:j∈keep69 N C) (hit:w∈(gateAt C j).inputs)
    (out:w∉pool69 N C (keep69 N C)) : color69 N C w=true := by
  classical
  have jj:=ordinary_index69 (keepSub69 hp)
  have wr:=back j jj w hit
  by_cases hs:w∈special N C
  · exact color_special hs
  by_cases low:w<N
  · have used:0<reads69 C w := by
      have h:=Finset.single_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr jj)
      have count:=List.count_pos_iff.mpr hit
      change _≤reads69 C w at h
      omega
    have one:reads69 C w=1 := by
      by_contra! ne
      apply hs
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩)
    exact (out (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr low,one⟩))).elim
  · let k:=w-N
    have eq:N+k=w := by dsimp [k];omega
    have ord:k∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [k];omega),by rwa [eq]⟩
    by_cases sp:k∈split69 N C
    · exact eq ▸ color_split_self back sp
    · have kkeep:k∈keep69 N C:=Finset.mem_sdiff.mpr ⟨ord,sp⟩
      exact (out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,kkeep,eq⟩))).elim

lemma markedInputs69 (back:ReadsBack N C) {j:Nat} (h:j∈keep69 N C) :
    (gateAt C j).inputs.countP (color69 N C) = if color69 N C (N+j) then 1 else 0 := by
  have le:=marked_keep_slots h
  rw [←List.countP_eq_length_filter] at le
  have pos := color_keep_iff back h
  rw [←List.countP_pos_iff] at pos
  cases hx:color69 N C (N+j)
  · change (gateAt C j).inputs.countP (color69 N C)=0
    by_contra! ne
    have eq:=pos.mpr (by omega)
    rw [hx] at eq;contradiction
  · change (gateAt C j).inputs.countP (color69 N C)=1
    have hp:=pos.mp hx
    omega

lemma splitInputCount69 (L:List Nat) (p:Nat→Bool) (pool A:Finset Nat)
    (spec:∀w∈L, (p w=true ↔ w∉pool ∨ w∈A) ∧ (w∈A → w∈pool)) :
    L.countP p = L.countP (fun w=>decide (w∉pool)) + ∑w∈A,L.count w := by
  classical
  induction L with
  | nil => simp
  | cons x xs ih =>
    have t:=ih (fun w hw=>spec w (List.mem_cons_of_mem _ hw))
    simp only [List.countP_cons,List.count_cons,Finset.sum_add_distrib]
    have a:=spec x (by simp)
    by_cases xA:x∈A <;> by_cases xp:x∈pool <;> cases xx:p x <;>
      simp_all <;> omega
end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem conserved69 {N z:Nat} {C:Circuit} (back:ReadsBack N C)
    (hz:z∈roots69 N C (keep69 N C))
    (lr:∀ j∈reg69 N C (keep69 N C) z,
      readsIn C (reg69 N C (keep69 N C) z) (N+j)=if N+j=z then 0 else 1) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  classical
  let P:=keep69 N C
  let pool:=pool69 N C P
  let rg:=reg69 N C P z
  let hot:=rg.filter (fun j=>color69 N C (N+j)=true)
  let A:=hot.image (fun j=>N+j)
  have acard:A.card=hot.card:=Finset.card_image_of_injective _ (fun _ _ e=>Nat.add_left_cancel e)
  have rgKeep (j:Nat) (hj:j∈rg):j∈P:=(Finset.mem_filter.mp hj).1
  have memA {w:Nat} : w∈A ↔ w∈pool ∧ owner69 N C P w=z ∧ color69 N C w=true := by
    constructor
    · intro h;obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h
      obtain ⟨jr,marked⟩:=Finset.mem_filter.mp hj
      exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (rgKeep _ jr)),(Finset.mem_filter.mp jr).2,marked⟩
    · rintro ⟨h,o,t⟩
      rcases Finset.mem_union.mp h with raw|gate
      · exact (by rw [colorOnce69 raw] at t; contradiction : False).elim
      · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp gate
        exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hj,o⟩,t⟩,rfl⟩
  have inEq (j:Nat) (hj:j∈rg) :
      (gateAt C j).inputs.countP (color69 N C) =
        (gateAt C j).inputs.countP (fun w=>decide (w∉pool)) + ∑w∈A,(gateAt C j).inputs.count w := by
    apply splitInputCount69
    intro w hit
    have memPool (h:w∈pool) : owner69 N C P w=z := by
      have p:=owner_same69 (P:=P) keepSub69 back (show branch69 N C P w (N+j) from ⟨h,j,rgKeep _ hj,rfl,hit⟩)
      exact p.trans (Finset.mem_filter.mp hj).2
    refine ⟨⟨fun t=>?_,?_⟩,fun h=>(memA.mp h).1⟩
    · by_cases pw:w∈pool
      · exact Or.inr (memA.mpr ⟨pw,memPool pw,t⟩)
      · exact Or.inl pw
    · rintro (out|inside)
      · exact colorOuter69 back (rgKeep _ hj) hit out
      · exact (memA.mp inside).2.2
  have calcAll : hot.card=slots69 N C P z+∑w∈A,readsIn C rg w := by
    calc
      hot.card = ∑j∈rg, if color69 N C (N+j) then 1 else 0 := by simp only [hot,Finset.card_filter]
      _ = ∑j∈rg,(gateAt C j).inputs.countP (color69 N C) :=
        Finset.sum_congr rfl (fun j hj=>(markedInputs69 back (rgKeep _ hj)).symm)
      _ = _ := by
        rw [Finset.sum_congr rfl inEq,Finset.sum_add_distrib]
        congr 1;exact Finset.sum_comm
  have lower : (∑w∈A,readsIn C rg w)+(if z∈A then 1 else 0)=A.card := by
    calc
      _ = (∑w∈A,if w=z then 0 else 1) + (∑w∈A,if w=z then 1 else 0) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro w hw;obtain ⟨j,m,rfl⟩:=Finset.mem_image.mp hw
          exact lr _ (Finset.mem_filter.mp m).1
        · simp
      _ = ∑_w∈A,1 := by
        rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro w _;split <;> simp_all
      _ = _ := by simp
  have root:=root_info69 (P:=P) keepSub69 back hz
  have za : z∈A ↔ color69 N C z=true := ⟨fun h=>(memA.mp h).2.2,fun h=>memA.mpr ⟨root.1,root.2.2.1,h⟩⟩
  change slots69 N C P z=_
  simp only [za] at lower
  omega
end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem fiberSlots69 {N z:Nat} {C:Circuit} (back:ReadsBack N C) (hz:z∈roots69 N C (keep69 N C)) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  apply conserved69 back hz
  intro j hj
  by_cases eq:N+j=z
  · rw [eq,ite_eq_left rfl]
    exact root_zero69 keepSub69 back hz
  · rw [ite_eq_right eq]
    obtain ⟨m,e⟩:=Finset.mem_filter.mp hj
    have pool:N+j∈pool69 N C (keep69 N C):=Finset.mem_union_right _ (Finset.mem_image_of_mem _ m)
    exact (local_read69 keepSub69 back pool e eq).1
end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem sum_reads_mask69 (l : List Nat) (A : Finset Nat) :
    (∑w∈A,l.count w) = l.countP (fun w=>decide (w∈A)) := by
  classical
  let f:=l.filter (fun w=>decide (w∈A))
  have sub:f.toFinset⊆A := fun _ hw=>of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change _=f.length
  calc
    _ = ∑w∈A,f.count w := Finset.sum_congr rfl (fun w hw=>(List.count_filter (by simpa using hw)).symm)
    _ = ∑w∈f.toFinset,f.count w := (Finset.sum_subset sub (fun _ _ h=>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))).symm
    _ = _ := List.sum_toFinset_count_eq_length f

theorem pure_sink69 {N z : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j))
    (hz : z∈roots69 N C (keep69 N C)) (zero : slots69 N C (keep69 N C) z=0) (out : z≠C.output) :
    z∉special N C ∧ ∃k∈gates69 C \ ordinary N C, z∈(gateAt C k).inputs := by
  classical
  obtain ⟨pool,sink,_,_⟩:=root_info69 keepSub69 back hz
  have slot:=fiberSlots69 back hz
  have off : color69 N C z=false := by cases h:color69 N C z <;> simp_all
  have ns : z∉special N C := fun h => by have a:=color_special h;rw [off] at a;contradiction
  have pos : 0<reads69 C z := by
    rcases Finset.mem_union.mp pool with raw|internal
    · have one : reads69 C z=1 := (Finset.mem_filter.mp raw).2;omega
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp internal
      have lt:=ordinary_index69 (keepSub69 hj)
      exact live j lt (by omega)
  have seek : ∃ k∈gates69 C, z∈(gateAt C k).inputs := by
    by_contra! no
    have none : reads69 C z=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
    omega
  obtain ⟨k,hk,hit⟩:=seek
  refine ⟨ns,k,Finset.mem_sdiff.mpr ⟨hk,?_⟩,hit⟩
  intro ord
  by_cases split:k∈split69 N C
  · have on:=color_split_all sh split z hit
    rw [off] at on;contradiction
  · exact sink (N+k) ⟨pool,k,Finset.mem_sdiff.mpr ⟨ord,split⟩,rfl,hit⟩

theorem pure_count69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)).card ≤ exits69 N C+1 := by
  classical
  let T:=(roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)
  let A:=T.erase C.output
  let gs:=gates69 C \ ordinary N C
  have obs (w : Nat) (hw:w∈A) : w∉special N C ∧ ∃k∈gs, w∈(gateAt C k).inputs := by
    obtain ⟨different,hh⟩:=Finset.mem_erase.mp hw
    obtain ⟨inR,zero⟩:=Finset.mem_filter.mp hh
    exact pure_sink69 sh back last live inR zero different
  have each (w:Nat) (hw:w∈A) : 1 ≤ ∑k∈gs,(gateAt C k).inputs.count w := by
    obtain ⟨k,hk,hit⟩:=(obs w hw).2
    exact (List.count_pos_iff.mpr hit).trans_le
      (Finset.single_le_sum (fun t _=>Nat.zero_le ((gateAt C t).inputs.count w)) hk)
  have bound : A.card≤exits69 N C := by
    calc
      _ = ∑ _∈A,1 := by simp
      _ ≤ ∑w∈A,∑k∈gs,(gateAt C k).inputs.count w := Finset.sum_le_sum each
      _ = ∑k∈gs,∑w∈A,(gateAt C k).inputs.count w := Finset.sum_comm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        rw [sum_reads_mask69]
        exact List.countP_mono_left (fun w _ h => decide_eq_true ((obs w (of_decide_eq_true h)).1))
  change T.card≤exits69 N C+1
  have incl : T⊆insert C.output A := by
    intro z mem;by_cases e:z=C.output
    · exact Finset.mem_insert.mpr (Or.inl e)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨e,mem⟩))
  have step:=Finset.card_le_card incl
  have cap:=Finset.card_insert_le C.output A
  change T.card≤(insert C.output A).card at step
  omega
end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem mixed_count69 {N:Nat} {C:Circuit} (sh:shapes69 C) (back:ReadsBack N C) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)).card≤2*entries69 N C := by
  classical
  let P:=keep69 N C
  let R:=(roots69 N C P).filter (fun z=>slots69 N C P z≠0)
  let f:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∉pool69 N C P))
  let g:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
  have per (j:Nat) (hj:j∈P): f j≤g j := by
    apply List.countP_mono_left
    intro w hw out'
    have out:w∉pool69 N C P:=of_decide_eq_true out'
    apply decide_eq_true
    by_cases sp:w∈special N C
    · exact Or.inl sp
    · have color:=colorOuter69 back hj hw out
      have nle : N≤w:=by by_contra! h;rw [color_raw h sp] at color;contradiction
      have eq:N+(w-N)=w:=by omega
      have ji:=ordinary_index69 (keepSub69 hj)
      have wi:=back j ji w hw
      have ord:w-N∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [eq]⟩
      refine Or.inr ⟨nle,?_⟩
      by_contra ns
      have inside:w-N∈P:=Finset.mem_sdiff.mpr ⟨ord,ns⟩
      exact out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,inside,eq⟩))
  have lower (z:Nat) (hz:z∈R) : 1≤ slots69 N C P z := by
    have neq:slots69 N C P z≠0:=(Finset.mem_filter.mp hz).2
    omega
  change R.card≤_
  calc
    R.card = ∑_z∈R,1 := by simp
    _ ≤ ∑z∈R,slots69 N C P z := Finset.sum_le_sum lower
    _ = ∑j∈P.filter (fun i=>owner69 N C P (N+i)∈R), f j :=
      Finset.sum_fiberwise_eq_sum_filter P R (fun j=>owner69 N C P (N+j)) f
    _ ≤ ∑j∈P,f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>Nat.zero_le _)
    _ ≤ ∑j∈P,g j := Finset.sum_le_sum per
    _ ≤ _ := entrySlotsBound69 sh back
end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem finish69 (N : Nat) (C : Circuit) (sh : shapes69 C) (back : ReadsBack N C)
    (_pos : 0<C.size) (last : C.output+1=N+C.size)
    (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ∃ pure chains : List (Finset Nat),
      pure.length≤exits69 N C+1 ∧ chains.length≤2*entries69 N C ∧
      (pure++chains).Pairwise (fun A B=>Disjoint A B) ∧
      (pure++chains).toFinset.biUnion (fun S=>S)=once69 N C ∧
      (∀S∈pure,S.Nonempty ∧ tree69 N C S ∅) ∧
      (∀S∈chains,S.Nonempty ∧ ∃b : Nat,tree69 N C S {b}) := by
  classical
  let P:=keep69 N C
  let roots:=roots69 N C P
  let Q:=roots.filter (fun z=>slots69 N C P z=0)
  let M:=roots.filter (fun z=>slots69 N C P z≠0)
  let leaf:=src69 N C P
  let qr:=Q.toList
  let mr:=M.toList
  have qmem (z:Nat) : z∈qr ↔ z∈roots ∧ slots69 N C P z=0 := by simp [qr,Q]
  have mmem (z:Nat) : z∈mr ↔ z∈roots ∧ slots69 N C P z≠0 := by simp [mr,M]
  have covered (z:Nat) : z∈qr++mr ↔ z∈roots := by
    rw [List.mem_append,qmem,mmem];tauto
  have nd : (qr++mr).Nodup := by
    refine List.nodup_append.mpr ⟨Q.nodup_toList,M.nodup_toList,?_⟩
    intro x hx y hy e;subst y;exact (mmem x|>.mp hy).2 ((qmem x|>.mp hx).2)
  have fiber {w z:Nat}: w∈leaf z ↔ w∈once69 N C ∧ owner69 N C P w=z := Finset.mem_filter
  have facts {z:Nat} (hz:z∈roots) : (leaf z).Nonempty ∧
      tree69 N C (leaf z) (outside69 N C P z) := by
    have count:=fiberSlots69 back hz
    have le : slots69 N C P z≤1 := by rw [count];split <;> decide
    exact ⟨(root_info69 keepSub69 back hz).2.2.2,subtree69 keepSub69 back sh last hz le⟩
  refine ⟨qr.map leaf,mr.map leaf,?_,?_,?_,?_,?_,?_⟩
  · simpa only [qr,List.length_map,Finset.length_toList] using pure_count69 sh back last live
  · simpa only [mr,List.length_map,Finset.length_toList] using mixed_count69 sh back
  · rw [←List.map_append,List.pairwise_map]
    apply nd.imp
    intro a b diff
    apply Finset.disjoint_left.mpr
    intro w ha hb;exact diff ((fiber.mp ha).2.symm.trans (fiber.mp hb).2)
  · rw [←List.map_append]
    ext w
    simp only [Finset.mem_biUnion,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨_,⟨z,_,rfl⟩,hit⟩;exact (fiber.mp hit).1
    · intro raw
      let z:=owner69 N C P w
      have root:z∈roots:=Finset.mem_image_of_mem _ raw
      exact ⟨leaf z,⟨z,(covered z).mpr root,rfl⟩,fiber.mpr ⟨raw,rfl⟩⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,zero⟩:=(qmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    rw [outside_empty69.mpr zero] at tree
    exact ⟨ne,tree⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,nz⟩:=(mmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    have card : (outside69 N C P z).card=1 := by
      have cap:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z)
      have count:=fiberSlots69 back rt
      have nonempty : (outside69 N C P z).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (fun h=>nz (outside_empty69.mp h))
      have pos:=Finset.card_pos.mpr nonempty
      change slots69 N C P z=_ at count
      split at count <;> omega
    obtain ⟨b,eq⟩:=Finset.card_eq_one.mp card
    exact ⟨ne,b,eq ▸ tree⟩
end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem splitStrict44 {N : Nat} {C : Circuit} (_sh : shapes69 C) (back : ReadsBack N C) (pos : 0<entries69 N C) :
    (split69 N C).card<entries69 N C := by
  classical
  let A := (ordinary N C).filter (fun j=>color69 N C (N+j)=true)
  have cover (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (hl : color69 N C w=true) : w∈special N C ∨ w∈A.image (fun t=>N+t) := by
    by_cases sp : w∈special N C
    · exact Or.inl sp
    right
    have wire : w<N+j := back j (ordinary_index69 hj) w hw
    have mid : N≤w := by by_contra! z;rw [color_raw z sp] at hl;contradiction
    have eq : N+(w-N)=w := by omega
    have idx : w-N<C.size := by have := ordinary_index69 hj;omega
    have good : w-N∈ordinary N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,by simpa only [eq] using sp⟩
    exact Finset.mem_image.mpr ⟨w-N,Finset.mem_filter.mpr ⟨good,by simpa only [eq] using hl⟩,eq⟩
  by_cases ne : A.Nonempty
  case neg =>
    have emp : split69 N C=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun j hj =>
      ne ⟨j,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,color_split_self back hj⟩⟩)
    simpa [emp] using pos
  let top := A.max' ne
  have incl : A.erase top⊆ordinary N C := fun j hj=>(Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).1
  have cover' (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (on : color69 N C w=true) : w∈special N C ∨ w∈(A.erase top).image (fun t=>N+t) := by
    rcases cover j hj w hw on with h|h
    · exact Or.inl h
    · obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp h
      have later : N+t<N+j := back j (ordinary_index69 hj) _ hw
      have marked : j∈A:=Finset.mem_filter.mpr ⟨hj,(color_ordinary_iff back hj).mpr ⟨N+t,hw,on⟩⟩
      have limit : j≤top := Finset.le_max' _ _ marked
      exact Or.inr (Finset.mem_image.mpr ⟨t,Finset.mem_erase.mpr ⟨by omega,ht⟩,rfl⟩)
  have account := countedSlots69 (ordinary N C) (A.erase top) (color69 N C) (fun _ h=>h) incl cover'
  rw [Finset.card_erase_of_mem (Finset.max'_mem A ne)] at account
  have nonzero:=Finset.card_pos.mpr ne

  have pay (j : Nat) (hj : j∈ordinary N C) :
      (if color69 N C (N+j)=true then 1 else 0) +
      (if 2≤((gateAt C j).inputs.filter (color69 N C)).length then 1 else 0) ≤
      (gateAt C j).inputs.countP (color69 N C) := by
    rw [List.countP_eq_length_filter]
    by_cases many : 2≤((gateAt C j).inputs.filter (color69 N C)).length
    · rw [ite_eq_left many];split <;> omega
    rw [ite_eq_right many]
    split
    · next hc =>
      have has := (color_ordinary_iff back hj).1 hc
      have pos := List.countP_pos_iff.mpr has
      rw [List.countP_eq_length_filter] at pos
      omega
    · omega
  have total := Finset.sum_le_sum pay
  rw [Finset.sum_add_distrib,←Finset.card_filter,←Finset.card_filter] at total
  change A.card+(split69 N C).card≤_ at total
  omega

theorem entryStrict44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) (pos : 0<entries69 N C) :
    (∑j∈keep69 N C,(gateAt C j).inputs.countP
      (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))) < 2*entries69 N C := by
  classical
  have cap := countedSlots69 (keep69 N C) (split69 N C)
    (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
    (fun _ h=>(Finset.mem_sdiff.mp h).1) (fun _ h=>(Finset.mem_filter.mp h).1) (by
      intro j hj w hw h
      rcases of_decide_eq_true h with s|⟨low,idx⟩
      · exact Or.inl s
      · exact Or.inr (Finset.mem_image.mpr ⟨w-N,idx,by omega⟩))
  have splitBound := splitStrict44 sh back pos
  omega

theorem mixedStrict44 {N:Nat} {C:Circuit} (sh:shapes69 C) (back:ReadsBack N C) (pos : 0<entries69 N C) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)).card<2*entries69 N C := by
  classical
  let P:=keep69 N C
  let R:=(roots69 N C P).filter (fun z=>slots69 N C P z≠0)
  let f:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∉pool69 N C P))
  let g:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
  have per (j:Nat) (hj:j∈P): f j≤g j := by
    apply List.countP_mono_left
    intro w hw out'
    have out:w∉pool69 N C P:=of_decide_eq_true out'
    apply decide_eq_true
    by_cases sp:w∈special N C
    · exact Or.inl sp
    · have color:=colorOuter69 back hj hw out
      have nle : N≤w:=by by_contra! h;rw [color_raw h sp] at color;contradiction
      have eq:N+(w-N)=w:=by omega
      have ji:=ordinary_index69 (keepSub69 hj)
      have wi:=back j ji w hw
      have ord:w-N∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [eq]⟩
      refine Or.inr ⟨nle,?_⟩
      by_contra ns
      have inside:w-N∈P:=Finset.mem_sdiff.mpr ⟨ord,ns⟩
      exact out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,inside,eq⟩))
  have lower (z:Nat) (hz:z∈R) : 1≤ slots69 N C P z := by
    have neq:slots69 N C P z≠0:=(Finset.mem_filter.mp hz).2
    omega
  change R.card<_
  calc
    R.card = ∑_z∈R,1 := by simp
    _ ≤ ∑z∈R,slots69 N C P z := Finset.sum_le_sum lower
    _ = ∑j∈P.filter (fun i=>owner69 N C P (N+i)∈R), f j :=
      Finset.sum_fiberwise_eq_sum_filter P R (fun j=>owner69 N C P (N+j)) f
    _ ≤ ∑j∈P,f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>Nat.zero_le _)
    _ ≤ ∑j∈P,g j := Finset.sum_le_sum per
    _ < _ := entryStrict44 sh back pos

end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def shared44 (N : Nat) (C : Circuit) :=
  (Finset.range (N+C.size)).filter (fun w=>2≤reads69 C w)
def sharedG44 (N : Nat) (C : Circuit) :=
  (gates69 C).filter (fun j=>2≤reads69 C (N+j))
def marked44 (N : Nat) (C : Circuit) := ∑ w∈shared44 N C,reads69 C w
def lift44 (N : Nat) (C : Circuit) (w : Nat) :=
  if w<N ∨ w∈shared44 N C then w else w+C.size
def down44 (N : Nat) (C : Circuit) (w : Nat) :=
  if w<N+C.size then w else w-C.size
def exposed44 (N : Nat) (C : Circuit) (g : Gate) : Gate := ⟨g.op,g.inputs.map (lift44 N C)⟩
def splitC (N : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (exposed44 N C),C.output+C.size⟩

@[simp] theorem split_size {N : Nat} {C : Circuit} : (splitC N C).size=C.size := by
  simp [splitC,Circuit.size]
theorem project44 {N : Nat} {C : Circuit} (w : Nat) : down44 N C (lift44 N C w)=w := by
  unfold lift44 down44
  by_cases h : w<N ∨ w∈shared44 N C
  · rw [if_pos h,if_pos]; rcases h with h|h
    · omega
    · exact Finset.mem_range.mp (Finset.mem_filter.mp h).1
  · rw [if_neg h,if_neg] <;> omega
theorem inj44 (N : Nat) (C : Circuit) : Function.Injective (lift44 N C) := by
  intro x y e; simpa only [project44] using congrArg (down44 N C) e
theorem at44 {N : Nat} {C : Circuit} {j : Nat} (h : j<C.size) :
    gateAt (splitC N C) j=exposed44 N C (gateAt C j) := by
  have a : j<C.gates.length := h
  simp [gateAt,splitC,List.getD_eq_getElem,a]
theorem shapes44 {N : Nat} {C : Circuit} (sh : shapes69 C) : shapes69 (splitC N C) := by
  intro g hg
  obtain ⟨old,mem,rfl⟩:=List.mem_map.mp hg
  simpa [exposed44] using sh old mem
theorem back44 {N : Nat} {C : Circuit} (back : ReadsBack N C) : ReadsBack (N+C.size) (splitC N C) := by
  intro j hj w hw
  have ji : j<C.size := by simpa [splitC,Circuit.size] using hj
  rw [at44 ji] at hw
  obtain ⟨x,hit,rfl⟩ := List.mem_map.mp hw
  have lt := back j ji x hit
  unfold lift44; split <;> omega
theorem op_count44 {N : Nat} {C : Circuit} (l : List Nat) (w : Nat) :
    (l.map (lift44 N C)).count (lift44 N C w)=l.count w := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases e : x=w
    · subst x; simp [List.count_cons,ih]
    · have ne : lift44 N C x≠lift44 N C w := fun h=>e (inj44 N C h)
      simp [List.count_cons,ih,ne,e]
theorem local44 {N : Nat} {C : Circuit} {T : Finset Nat} (sub : T⊆gates69 C) (w : Nat) :
    readsIn (splitC N C) T (lift44 N C w)=readsIn C T w := by
  apply Finset.sum_congr rfl
  intro j hj; rw [at44 (Finset.mem_range.mp (sub hj))]
  exact op_count44 _ _
theorem reads44 {N : Nat} {C : Circuit} (w : Nat) :
    reads69 (splitC N C) (lift44 N C w)=reads69 C w := by
  unfold reads69 gates69; rw [split_size]; exact local44 (fun _ h=>h) _
theorem absent44 {N : Nat} {C : Circuit} {w : Nat} (never : ∀x,lift44 N C x≠w) :
    reads69 (splitC N C) w=0 := by
  unfold reads69 readsIn gates69
  rw [split_size]
  apply Finset.sum_eq_zero
  intro j hj
  have ji : j<C.size := Finset.mem_range.mp hj
  rw [at44 ji]
  apply List.count_eq_zero.mpr
  intro hit
  obtain ⟨x,_,e⟩ := List.mem_map.mp hit
  exact never x e
theorem dead44 {N : Nat} {C : Circuit} {j : Nat} (hj : j∈sharedG44 N C) :
    reads69 (splitC N C) (N+C.size+j)=0 := by
  obtain ⟨bound,many⟩:=Finset.mem_filter.mp hj
  have ji : j<C.size := Finset.mem_range.mp bound
  have mem : N+j∈shared44 N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩
  apply absent44; intro x e
  have orig := congrArg (down44 N C) e
  rw [project44,down44,if_neg (by omega)] at orig
  have eq : x=N+j := by omega
  rw [eq,lift44,if_pos (Or.inr mem)] at e; omega
theorem gate_reads44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    reads69 (splitC N C) (N+C.size+j)=(if j∈sharedG44 N C then 0 else reads69 C (N+j)) := by
  by_cases g : j∈sharedG44 N C
  · rw [if_pos g]; exact dead44 g
  · rw [if_neg g]
    have h : N+j∉shared44 N C := fun mem=>g (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ji,(Finset.mem_filter.mp mem).2⟩)
    simpa [lift44,h,Nat.add_right_comm] using (reads44 (N:=N) (C:=C) (N+j))
theorem gate_one44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    reads69 (splitC N C) (N+C.size+j)≤1 := by
  rw [gate_reads44 ji]; split
  · omega
  · next h => by_contra! many; exact h (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ji,many⟩)

theorem raw_reads44 {N : Nat} {C : Circuit} {w : Nat} (hw : w<N+C.size) :
    reads69 (splitC N C) w=(if w<N ∨ w∈shared44 N C then reads69 C w else 0) := by
  by_cases h : w<N ∨ w∈shared44 N C
  · simpa [lift44,h] using (reads44 (N:=N) (C:=C) w)
  · rw [if_neg h]
    apply absent44; intro x e
    have p:=congrArg (down44 N C) e
    rw [project44,down44,if_pos hw] at p
    subst x; rw [lift44,if_neg h] at e
    have ge : N≤w := by omega
    omega
theorem once44 (N : Nat) (C : Circuit) : once69 (N+C.size) (splitC N C)=once69 N C := by
  ext w
  constructor
  · intro mem
    obtain ⟨lt,one⟩ := Finset.mem_filter.mp mem
    have range:=Finset.mem_range.mp lt
    rw [raw_reads44 range] at one
    by_cases low : w<N
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr low,by simpa [low] using one⟩
    · by_cases shared : w∈shared44 N C
      · have many := (Finset.mem_filter.mp shared).2
        simp [low,shared] at one; omega
      · simp [low,shared] at one
  · intro mem
    obtain ⟨lt,one⟩ := Finset.mem_filter.mp mem
    have low:=Finset.mem_range.mp lt
    have wide : w<N+C.size:=by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr wide,by simpa [raw_reads44 wide,low] using one⟩
theorem neg44 (N : Nat) (C : Circuit) : neg69 (splitC N C)=neg69 C := by
  ext j
  simp only [neg69,gates69,split_size,Finset.mem_filter,Finset.mem_range]
  by_cases h : j<C.size
  · simp [h,at44 h,exposed44]
  · simp [h]
theorem flagged44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    N+C.size+j∈special (N+C.size) (splitC N C) ↔ j∈neg69 C := by
  constructor
  · intro m
    rcases Finset.mem_union.mp m with hi|hn
    · have l := gate_one44 (N:=N) ji; have b := (Finset.mem_filter.mp hi).2; omega
    · obtain ⟨k,hk,e⟩:=Finset.mem_image.mp hn
      have eq : k=j:=Nat.add_left_cancel e
      subst k; rwa [neg44] at hk
  · intro hn; apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨j,by rwa [neg44],rfl⟩
theorem ord44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    j∈ordinary (N+C.size) (splitC N C) ↔ j∉neg69 C := by
  change (_∈(gates69 _).filter _) ↔ _
  simp [gates69,ji,flagged44 ji]
theorem special_wire44 {N : Nat} {C : Circuit} {w : Nat} (hw : w<N+C.size) :
    lift44 N C w∈special (N+C.size) (splitC N C) → w∈shared44 N C ∨ w∈(neg69 C).image (fun k=>N+k) := by
  intro h
  rcases Finset.mem_union.mp h with many|neg
  · have b : 2≤reads69 (splitC N C) (lift44 N C w):=(Finset.mem_filter.mp many).2
    rw [reads44] at b
    exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw,b⟩)
  · obtain ⟨j,hj,e⟩:=Finset.mem_image.mp neg
    rw [neg44] at hj
    have k:=congrArg (down44 N C) e
    change down44 N C (N+C.size+j)=down44 N C (lift44 N C w) at k
    rw [project44,down44,if_neg (by omega)] at k
    exact Or.inr (Finset.mem_image.mpr ⟨j,hj,by omega⟩)

end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
theorem entries44 {N : Nat} {C : Circuit} (back : ReadsBack N C) :
    entries69 (N+C.size) (splitC N C)≤ marked44 N C+(neg69 C).card := by
  classical
  let D:=splitC N C
  let O:=ordinary (N+C.size) D
  let S:=shared44 N C
  let I:=(neg69 C).image (fun k=>N+k) \ S
  let X:=S∪I
  have each (j : Nat) (hj : j∈O) :
      (gateAt D j).inputs.countP (fun w=>decide (w∈special (N+C.size) D)) ≤
        (gateAt C j).inputs.countP (fun x=>decide (x∈X)) := by
    have ji : j<C.size := by simpa only [D,split_size] using ordinary_index69 hj
    rw [show gateAt D j=exposed44 N C (gateAt C j) from at44 ji]
    change ((gateAt C j).inputs.map (lift44 N C)).countP _≤_
    rw [List.countP_map]
    apply List.countP_mono_left
    intro x hx use
    have low:=back j ji x hx
    have mark : lift44 N C x∈special (N+C.size) D:=of_decide_eq_true use
    rcases special_wire44 (by omega : x<N+C.size) mark with s|n
    · exact decide_eq_true (Finset.mem_union_left _ s)
    · apply decide_eq_true
      by_cases hit : x∈S
      · exact Finset.mem_union_left _ hit
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨n,hit⟩)
  have subO : O⊆gates69 C := by
    intro j hj
    have lt := ordinary_index69 hj
    exact Finset.mem_range.mpr (by simpa only [D,split_size] using lt)
  have mass : (∑ w∈I,reads69 C w)≤(neg69 C).card := by
    have per (w : Nat) (mem : w∈I) : reads69 C w≤1 := by
      obtain ⟨im,out⟩:=Finset.mem_sdiff.mp mem
      obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp im
      have ki : k<C.size := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      by_contra! many; exact out (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩)
    have total:=Finset.sum_le_sum per
    simp only [Finset.sum_const,smul_eq_mul,mul_one] at total
    exact total.trans ((Finset.card_le_card Finset.sdiff_subset).trans Finset.card_image_le)
  have dis : Disjoint S I := Finset.disjoint_left.mpr (fun _ hw hx=>(Finset.mem_sdiff.mp hx).2 hw)
  calc
    _ ≤ ∑j∈O,(gateAt C j).inputs.countP (fun x=>decide (x∈X)) := Finset.sum_le_sum each
    _ ≤ ∑j∈gates69 C,(gateAt C j).inputs.countP (fun x=>decide (x∈X)) :=
      Finset.sum_le_sum_of_subset_of_nonneg subO (fun _ _ _=>Nat.zero_le _)
    _ = ∑w∈X,reads69 C w := by simp_rw [maskedCount69];exact Finset.sum_comm
    _ ≤ _ := by rw [Finset.sum_union dis]; exact Nat.add_le_add_left mass _

noncomputable def rootsPure (N : Nat) (C : Circuit) := (roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)
noncomputable def rootsMixed (N : Nat) (C : Circuit) := (roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)
noncomputable def correction (N : Nat) (C : Circuit) := if 0< marked44 N C+(neg69 C).card then 1 else 0
theorem mixed44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) :
    (rootsMixed (N+C.size) (splitC N C)).card+correction N C≤2*(marked44 N C+(neg69 C).card) := by
  classical
  have cap := entries44 back
  have old:=mixed_count69 (shapes44 sh) (back44 back)
  by_cases pos : 0<entries69 (N+C.size) (splitC N C)
  · have gain := mixedStrict44 (shapes44 sh) (back44 back) pos
    unfold rootsMixed correction; split <;> omega
  · unfold rootsMixed correction; split <;> omega

end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
noncomputable def places44 (N : Nat) (C : Circuit) :=
  insert (splitC N C).output
    (((sharedG44 N C).image (fun j=>N+C.size+j)) ∪
      ((neg69 C).image (fun j=>(gateAt (splitC N C) j).inputs.headD 0)))

theorem stop44 {N : Nat} {C : Circuit} (sh : shapes69 C) (last : C.output+1=N+C.size)
    (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j))
    {z : Nat} (bounded : z<N+C.size+(splitC N C).size)
    (realRaw : z<N+C.size → 0<reads69 (splitC N C) z)
    (stopped : ∀j∈ordinary (N+C.size) (splitC N C),z∉(gateAt (splitC N C) j).inputs) :
    z∈places44 N C := by
  classical
  let D:=splitC N C
  by_cases read : 0<reads69 D z
  · have hit : ∃j∈gates69 D,z∈(gateAt D j).inputs := by
      by_contra! no
      have zero : reads69 D z=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
      omega
    obtain ⟨j,hj,pin⟩:=hit
    have ji : j<C.size := by simpa only [D,split_size] using Finset.mem_range.mp hj
    have neg : j∈neg69 C := by
      by_contra notNeg
      exact stopped j ((ord44 ji).mpr notNeg) pin
    have valid : j<D.gates.length := by simpa [D,splitC,Circuit.size] using ji
    have gm : gateAt D j∈D.gates := by rw [gateAt,List.getD_eq_getElem _ _ valid];exact List.getElem_mem valid
    have nn : j∈neg69 D := by simpa only [D,neg44] using neg
    have op : (gateAt D j).op=.not := (Finset.mem_filter.mp nn).2
    have len : (gateAt D j).inputs.length=1 := by
      rcases shapes44 sh _ gm with ⟨ops,_⟩|⟨_,one⟩
      · rw [op] at ops; simp at ops
      · exact one
    have head {l : List Nat} (len : l.length=1) (mem : z∈l) : l.headD 0=z := by
      cases l with
      | nil => simp at mem
      | cons a tail =>
        cases tail with
        | nil => simpa using (List.mem_singleton.mp mem).symm
        | cons b rest => simp at len
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,neg,head len pin⟩))
  · have lo : N+C.size≤z := by by_contra! h; exact read (realRaw h)
    let j:=z-(N+C.size)
    have ident : N+C.size+j=z := by dsimp [j]; omega
    have ji : j<C.size := by rw [split_size] at bounded; omega
    by_cases share : j∈sharedG44 N C
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,share,ident⟩))
    · have h:=gate_reads44 (N:=N) (C:=C) ji
      rw [if_neg share,ident] at h
      have endGate : j+1=C.size := by
        by_contra ne
        have pos:=live j ji (by omega)
        change ¬0<reads69 (splitC N C) z at read; omega
      have out : z=(splitC N C).output := by change z=C.output+C.size;omega
      exact Finset.mem_insert.mpr (Or.inl out)

theorem silent44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    {z : Nat} (hz : z∈rootsPure N C) :
    color69 N C z=false ∧ (∀j∈ordinary N C,z∉(gateAt C j).inputs) := by
  obtain ⟨rt,zero⟩:=Finset.mem_filter.mp hz
  have off : color69 N C z=false := by
    have slot:=fiberSlots69 back rt
    cases h:color69 N C z <;> simp_all
  obtain ⟨pool,sink,_,_⟩:=root_info69 keepSub69 back rt
  refine ⟨off,?_⟩
  intro j hj pin
  by_cases join : j∈split69 N C
  · have yes:=color_split_all sh join z pin
    rw [off] at yes;contradiction
  · exact sink (N+j) ⟨pool,j,Finset.mem_sdiff.mpr ⟨hj,join⟩,rfl,pin⟩

theorem places_card (N : Nat) (C : Circuit) : (places44 N C).card≤(sharedG44 N C).card+(neg69 C).card+1 :=
  (Finset.card_insert_le ..).trans (Nat.add_le_add_right
    ((Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)) 1)

theorem pure_subset44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    rootsPure (N+C.size) (splitC N C)⊆places44 N C := by
  intro z hz
  have b:=back44 back
  have rt:=(Finset.mem_filter.mp hz).1
  have pool:=(root_info69 keepSub69 b rt).1
  apply stop44 sh last live (pool_bound69 keepSub69 pool) _ (silent44 (shapes44 sh) b hz).2
  intro raw
  rcases Finset.mem_union.mp pool with src|gate
  · have one:=(Finset.mem_filter.mp src).2;omega
  · obtain ⟨j,_,e⟩:=Finset.mem_image.mp gate
    change N+C.size+j=z at e; omega

theorem pure44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    (rootsPure (N+C.size) (splitC N C)).card+correction N C≤(sharedG44 N C).card+(neg69 C).card+1 := by
  classical
  let M:=N+C.size
  let D:=splitC N C
  let R:=rootsPure M D
  let A:=(Finset.range (M+D.size)).filter (fun w=>color69 M D w=true)
  have sub : R⊆places44 N C := pure_subset44 sh back last live
  have cap:=places_card N C
  by_cases active : 0< marked44 N C+(neg69 C).card
  case neg =>
    have c:=Finset.card_le_card sub
    simpa [correction,active] using c.trans cap
  have existsMark : A.Nonempty := by
    by_cases ne : (neg69 C).Nonempty
    · obtain ⟨j,hj⟩:=ne
      have ji : j<C.size := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have specialJ:=(flagged44 (N:=N) ji).mpr hj
      refine ⟨M+j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,color_special specialJ⟩⟩
      change M+j<M+(splitC N C).size;rw [split_size];omega
    · have full : (shared44 N C).Nonempty := by
        by_contra none
        have a:=Finset.not_nonempty_iff_eq_empty.mp ne
        have b:=Finset.not_nonempty_iff_eq_empty.mp none
        simp [marked44,a,b] at active
      obtain ⟨w,hw⟩:=full
      have lo : w<M := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
      have many : 2≤reads69 D w := by
        change 2≤reads69 (splitC N C) w
        rw [raw_reads44 lo,if_pos (Or.inr hw)]
        exact (Finset.mem_filter.mp hw).2
      have wr : w<M+D.size := by omega
      have mark : w∈special M D := Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr wr,many⟩)
      exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr wr,color_special mark⟩⟩
  let z:=A.max' existsMark
  have mz : z∈A := Finset.max'_mem _ _
  obtain ⟨rz,on⟩:=Finset.mem_filter.mp mz
  have bounded : z<M+D.size:=Finset.mem_range.mp rz
  have noOrd : ∀j∈ordinary M D,z∉(gateAt D j).inputs := by
    intro j hj use
    have ji:=ordinary_index69 hj
    have lit:=(color_ordinary_iff (back44 back) hj).mpr ⟨z,use,on⟩
    have marked : M+j∈A:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),lit⟩
    have greatest : M+j≤z:=Finset.le_max' _ _ marked
    have prior : z<M+j:=back44 back j ji z use
    omega
  have raw (low : z<M) : 0<reads69 D z := by
    have flag : z∈special M D := by
      by_contra no
      have off:=color_raw low no
      change color69 M D z=true at on
      rw [off] at on;contradiction
    rcases Finset.mem_union.mp flag with many|gate
    · have h:=(Finset.mem_filter.mp many).2;omega
    · obtain ⟨j,_,eq⟩:=Finset.mem_image.mp gate
      change M+j=z at eq;omega
  have allocation : z∈places44 N C := stop44 sh last live bounded raw noOrd
  have separate : z∉R := by
    intro hz
    have off:=(silent44 (shapes44 sh) (back44 back) hz).1
    change color69 M D z=false at off
    change color69 M D z=true at on
    rw [off] at on;contradiction
  have enlargement:=Finset.card_le_card (Finset.insert_subset allocation sub)
  rw [Finset.card_insert_of_notMem separate] at enlargement
  simpa [correction,active] using enlargement.trans cap

end CutLib25855.Cut

namespace CutLib25855.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def tree44 (N : Nat) (C : Circuit) (S E : Finset Nat) : Prop := ∃ region : Finset Nat, ∃ root : Nat,
  let wires := S ∪ region.image (fun k=>N+k)
  let localReads := readsIn C region
  region ⊆ gates69 C ∧ root∈wires ∧ localReads root=0 ∧
  (∀b∈E,b∉wires ∧ b<root ∧ localReads b=1) ∧
  (∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀w∈(gateAt C j).inputs, w∈wires ∨ w∈E) ∧
  (∀w∈wires,w≠root → localReads w=1 ∧ reads69 C w=1 ∧ C.output≠w)

def up44 (N : Nat) (C : Circuit) (w : Nat) := if w<N then w else w+C.size
theorem up_order44 {N : Nat} {C : Circuit} {w v : Nat} : up44 N C w≤up44 N C v ↔ w≤v := by
  unfold up44; split <;> split <;> omega
theorem undo44 {N : Nat} {C : Circuit} (w : Nat) : down44 N C (up44 N C w)=w := by
  unfold up44 down44; split <;> split <;> omega
theorem raw_gate44 {N j : Nat} {C : Circuit} : up44 N C (N+j)=N+C.size+j := by
  unfold up44;rw [if_neg (by omega)];omega
theorem mapped44 {N : Nat} {C : Circuit} {S T : Finset Nat} (sub : S⊆Finset.range N) :
    (S∪T.image (fun k=>N+k)).image (up44 N C)=S∪T.image (fun k=>N+C.size+k) := by
  ext y
  constructor
  · intro h
    obtain ⟨w,mem,rfl⟩:=Finset.mem_image.mp h
    rcases Finset.mem_union.mp mem with r|g
    · have low:=Finset.mem_range.mp (sub r); rw [up44,if_pos low];exact Finset.mem_union_left _ r
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp g; rw [raw_gate44]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
  · intro h;rcases Finset.mem_union.mp h with r|g
    · exact Finset.mem_image.mpr ⟨y,Finset.mem_union_left _ r,if_pos (Finset.mem_range.mp (sub r))⟩
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp g
      exact Finset.mem_image.mpr ⟨N+j,Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj),raw_gate44⟩
theorem find_pin44 {C : Circuit} {T : Finset Nat} {w : Nat} (pos : 0<readsIn C T w) :
    ∃ j∈T,w∈(gateAt C j).inputs := by
  by_contra! no
  have zero : readsIn C T w=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
  omega

theorem projectTree44 {N : Nat} {C : Circuit} (back : ReadsBack N C) (size : 0<C.size)
    (last : C.output+1=N+C.size) {S E : Finset Nat} (sub : S⊆Finset.range N)
    (t : tree69 (N+C.size) (splitC N C) S E) : tree44 N C S (E.image (down44 N C)) := by
  classical
  let M:=N+C.size
  let D:=splitC N C
  obtain ⟨T,z,info⟩:=t
  dsimp only at info
  obtain ⟨ordinary,root,_,ports,gates,inside⟩:=info
  let W:=S∪T.image (fun k=>N+k)
  let V:=S∪T.image (fun k=>M+k)
  have idx : T⊆gates69 C := fun j hj => by
    have g:=ordinary_index69 (ordinary hj)
    exact Finset.mem_range.mpr (by simpa only [split_size] using g)
  have mapping : W.image (up44 N C)=V := mapped44 sub
  have phys {w : Nat} (mem : w∈W) : up44 N C w∈V := mapping ▸ Finset.mem_image_of_mem _ mem
  have pre {v : Nat} (mem : v∈V) : ∃w∈W,up44 N C w=v := Finset.mem_image.mp (mapping.symm ▸ mem)
  obtain ⟨r,hr,hrz⟩:=pre root
  have maxRoot : ∀w∈V,w≤z := by
    let v:=V.max' ⟨z,root⟩
    have mv : v∈V := Finset.max'_mem _ _
    have top (w : Nat) (hw : w∈V) : w≤v := Finset.le_max' _ _ hw
    have equals : v=z := by
      by_contra ne
      have pc : readsIn D T v=1 := (inside v mv ne).1
      obtain ⟨j,hj,use⟩:=find_pin44 (by omega : 0<readsIn D T v)
      have prior : v<M+j := back44 back j (ordinary_index69 (ordinary hj)) v use
      have limit:=top (M+j) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
      omega
    intro w hw; exact (top w hw).trans_eq equals
  have oldBound {j w : Nat} (hj : j∈T) (pin : w∈(gateAt C j).inputs) : w<r := by
    have above:=maxRoot (M+j) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
    rw [←hrz,show M+j=up44 N C (N+j) from raw_gate44.symm] at above
    exact (back j (Finset.mem_range.mp (idx hj)) w pin).trans_le (up_order44.mp above)
  have entryPin {v : Nat} (one : readsIn D T v=1) : lift44 N C (down44 N C v)=v ∧ down44 N C v<r := by
    obtain ⟨j,hj,pin⟩:=find_pin44 (by omega : 0<readsIn D T v)
    have e : gateAt D j=exposed44 N C (gateAt C j) := at44 (Finset.mem_range.mp (idx hj))
    rw [e] at pin
    obtain ⟨w,use,rfl⟩:=List.mem_map.mp pin
    exact ⟨by rw [project44],by rw [project44];exact oldBound hj use⟩
  have coincide {w : Nat} (hw : w∈W) (diff : w≠r) : lift44 N C w=up44 N C w := by
    have ne : up44 N C w≠z := by intro eq;exact diff (by simpa only [undo44] using congrArg (down44 N C) (eq.trans hrz.symm))
    have on:=(inside _ (phys hw) ne).1
    have hit:=(entryPin on).1
    rwa [undo44] at hit
  refine ⟨T,r,idx,hr,?_,?_,?_,?_⟩
  · exact Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (fun pin=>(Nat.lt_irrefl r) (oldBound hj pin)))
  · intro b hb;obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hb
    obtain ⟨out,_,one⟩:=ports v hv
    obtain ⟨eq,lt⟩:=entryPin one
    refine ⟨?_,lt,?_⟩
    · intro hw
      have u:=coincide hw (Nat.ne_of_lt lt)
      exact out ((eq.symm.trans u).symm ▸ phys hw)
    · rw [←local44 (N:=N) idx,eq];exact one
  · intro j hj
    obtain ⟨op,len,pins⟩:=gates j hj
    have e : gateAt (splitC N C) j=exposed44 N C (gateAt C j) := at44 (Finset.mem_range.mp (idx hj))
    rw [e] at op len pins
    refine ⟨op,by simpa [exposed44] using len,?_⟩
    intro w use
    have choices:=pins (lift44 N C w) (List.mem_map.mpr ⟨w,use,rfl⟩)
    rcases choices with isWire|port
    · obtain ⟨a,ha,eq⟩:=pre isWire
      have same:=congrArg (down44 N C) eq
      rw [undo44,project44] at same
      exact Or.inl (same ▸ ha)
    · exact Or.inr (Finset.mem_image.mpr ⟨_,port,project44 w⟩)
  · intro w hw diff
    have eq:=coincide hw diff
    have ne : up44 N C w≠z := fun h=>diff (by simpa only [undo44] using congrArg (down44 N C) (h.trans hrz.symm))
    obtain ⟨one,all,other⟩:=inside _ (phys hw) ne
    rw [←eq] at one all
    refine ⟨(local44 idx w).symm.trans one,(reads44 w).symm.trans all,?_⟩
    intro o;apply other
    change C.output+C.size=up44 N C w
    rw [←o,up44,if_neg (by omega)]

end CutLib25855.Cut
namespace CutLib25855
open CutLib25855.Cut in
theorem provedCut : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let gates := Finset.range C.size
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)) gates
  let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
  let sharedGates := gates.filter (fun k => 2 ≤ reads (n + k))
  let markedReads := ∑ w ∈ shared, reads w
  let once := (Finset.range n).filter (fun w => reads w = 1)
  let tree := fun (S E : Finset ℕ) => ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
    region ⊆ gates ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      ((gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gate j).inputs.length = 2 ∧ ∀ w ∈ (gate j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ reads w = 1 ∧ C.output ≠ w)
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  0 < C.size → C.output + 1 = n + C.size →
  (∀ j < C.size, j + 1 < C.size → 0 < reads (n + j)) →
  ∃ (pure chains : List (Finset ℕ)) (markedComponents : ℕ),
    pure.length + markedComponents ≤ sharedGates.card + neg.card + 1 ∧
    chains.length + markedComponents ≤ 2 * (markedReads + neg.card) ∧
    (0 < markedReads + neg.card → 0 < markedComponents) ∧
    (pure ++ chains).Pairwise (fun A B => Disjoint A B) ∧
    (pure ++ chains).toFinset.biUnion (fun S => S) = once ∧
    (∀ S ∈ pure, S.Nonempty ∧ tree S ∅) ∧
    (∀ S ∈ chains, S.Nonempty ∧ ∃ b : ℕ, tree S {b}) := by
  intro N C
  dsimp only
  intro sh back size last live
  classical
  let M:=N+C.size
  let D:=splitC N C
  have shape : shapes69 D:=shapes44 sh
  have earlier : PEqualNP.MetaComplexity.NestedCover.ReadsBack M D:=back44 back
  have lastD : D.output+1=M+D.size := by
    change C.output+C.size+1=N+C.size+(splitC N C).size
    rw [split_size];omega

  let P:=keep69 M D
  let roots:=roots69 M D P
  let Q:=roots.filter (fun z=>slots69 M D P z=0)
  let mixedRoots:=roots.filter (fun z=>slots69 M D P z≠0)
  let leaf:=src69 M D P
  let qr:=Q.toList
  let mr:=mixedRoots.toList
  have qmem (z:Nat) : z∈qr ↔ z∈roots ∧ slots69 M D P z=0 := by simp [qr,Q]
  have mmem (z:Nat) : z∈mr ↔ z∈roots ∧ slots69 M D P z≠0 := by simp [mr,mixedRoots]
  have covered (z:Nat) : z∈qr++mr ↔ z∈roots := by
    rw [List.mem_append,qmem,mmem];tauto
  have nd : (qr++mr).Nodup := by
    refine List.nodup_append.mpr ⟨Q.nodup_toList,mixedRoots.nodup_toList,?_⟩
    intro x hx y hy e;subst y;exact (mmem x|>.mp hy).2 ((qmem x|>.mp hx).2)
  have fiber {w z:Nat}: w∈leaf z ↔ w∈once69 M D ∧ owner69 M D P w=z := Finset.mem_filter
  have facts {z:Nat} (hz:z∈roots) : (leaf z).Nonempty ∧
      tree69 M D (leaf z) (outside69 M D P z) := by
    have count:=fiberSlots69 earlier hz
    have le : slots69 M D P z≤1 := by rw [count];split <;> decide
    exact ⟨(root_info69 keepSub69 earlier hz).2.2.2,subtree69 keepSub69 earlier shape lastD hz le⟩
  have raw (z : Nat) : leaf z⊆Finset.range N := by
    intro w hw
    have once : w∈once69 M D := (fiber.mp hw).1
    rw [show once69 M D=once69 N C from once44 N C] at once
    exact (Finset.mem_filter.mp once).1
  refine ⟨qr.map leaf,mr.map leaf,correction N C,?_,?_,?_,?_,?_,?_,?_⟩
  · change (Q.toList.map leaf).length+correction N C≤(sharedG44 N C).card+(neg69 C).card+1
    rw [List.length_map,Finset.length_toList]; exact pure44 sh back last live
  · change (mixedRoots.toList.map leaf).length+correction N C≤2*(marked44 N C+(neg69 C).card)
    rw [List.length_map,Finset.length_toList]; exact mixed44 sh back
  · intro pos
    change 0< marked44 N C+(neg69 C).card at pos
    simp [correction,pos]
  · rw [←List.map_append,List.pairwise_map]
    apply nd.imp
    intro a b diff
    apply Finset.disjoint_left.mpr
    intro w ha hb;exact diff ((fiber.mp ha).2.symm.trans (fiber.mp hb).2)
  · change ((qr.map leaf)++(mr.map leaf)).toFinset.biUnion id=once69 N C
    rw [←once44 N C,←List.map_append]
    ext w
    simp only [Finset.mem_biUnion,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨_,⟨z,_,rfl⟩,hit⟩;exact (fiber.mp hit).1
    · intro raw
      let z:=owner69 M D P w
      have root:z∈roots:=Finset.mem_image_of_mem _ raw
      exact ⟨leaf z,⟨z,(covered z).mpr root,rfl⟩,fiber.mpr ⟨raw,rfl⟩⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,zero⟩:=(qmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    rw [outside_empty69.mpr zero] at tree
    refine ⟨ne,?_⟩
    change tree44 N C (leaf z) ∅
    simpa only [Finset.image_empty] using projectTree44 back size last (raw z) tree
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,nz⟩:=(mmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    have card : (outside69 M D P z).card=1 := by
      have cap:=outside_card69 (N:=M) (C:=D) (P:=P) (z:=z)
      have count:=fiberSlots69 earlier rt
      have nonempty : (outside69 M D P z).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (fun h=>nz (outside_empty69.mp h))
      have pos:=Finset.card_pos.mpr nonempty
      change slots69 M D P z=_ at count
      split at count <;> omega
    obtain ⟨b,eq⟩:=Finset.card_eq_one.mp card
    rw [eq] at tree
    refine ⟨ne,down44 N C b,?_⟩
    change tree44 N C (leaf z) {down44 N C b}
    simpa only [Finset.image_singleton] using projectTree44 back size last (raw z) tree

end CutLib25855

namespace CutLib25855
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
theorem cut_cap {n m d : ℕ} (G : Fin n → Fin m → Bool) (e : Bool) (hd : 2≤d)
    (rdeg : degree G e d) (cdeg : degree (transpose G) e d) (fourFree : acyclicFour G e)
    (D : Circuit) (back : ReadsBack (n+m) D) (rep : Represents G D)
    (S E : Finset ℕ) (sub : S⊆Finset.range (n+m)) (one : E.card≤1)
    (tree : Cut.tree44 (n+m) D S E) :
    S.card ≤ max (2*d*(2+E.card)) (2*(d*((2+E.card)-1))+2*(d*((2+E.card)-1)/2)) := by
  classical
  obtain ⟨R,B,join,card⟩ := raw_parts S sub
  obtain ⟨region,root,h⟩ := tree
  dsimp only at h
  obtain ⟨inside,member,last,ports,gates,uses⟩ := h
  have t := rectangle n m G D R B region E root
  dsimp only at t
  rw [join] at t
  obtain ⟨profilesR,profilesC,rectangles⟩ := t back rep
    inside member one ports gates last uses
  rw [card]
  exact Sparse.upper d (2+E.card) n m G e R B hd (by omega)
    ⟨rdeg,cdeg,fourFree,profilesR,profilesC,rectangles⟩

end CutLib25855

namespace CutLib25855.Tree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
def bits (N : ℕ) (U : Finset ℕ) := sample N (Finset.range N) U
def value (N : ℕ) (C : Circuit) (w : ℕ) (U : Finset ℕ) := Cut.V C (bits N U) w

theorem pair_in {s : Finset ℕ} {a b : ℕ} (ha : a∈s) (hb : b∈s) : ({a,b} : Finset ℕ)⊆s := by
  intro i hi
  rcases Finset.mem_insert.mp hi with h|h
  · exact h ▸ ha
  · exact (Finset.mem_singleton.mp h) ▸ hb

theorem raw_value {N : ℕ} (C : Circuit) {i : ℕ} (low : i<N) (U : Finset ℕ) :
    value N C i U=decide (i∈U) := by
  change sig N C (Finset.range N) i U=_
  simpa only [Finset.mem_range,low,true_and] using (sig_raw (C:=C) (s:=Finset.range N) low U)

theorem values_order {N : ℕ} (C : Circuit) (mono : Monotone2 C) (back : ReadsBack N C)
    {U W : Finset ℕ} (incl : U⊆W) : ∀ i, value N C i U=true → value N C i W=true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases low : i<N
    · rw [raw_value C low,raw_value C low,decide_eq_true_eq,decide_eq_true_eq]; exact fun h => incl h
    by_cases far : N+C.size ≤ i
    · intro hx
      have h := Cut.past C.gates (bits N U) i (by rw [show (bits N U).length=N from sample_length ..]; exact far)
      exact False.elim (Bool.false_ne_true (h.symm.trans hx))
    let j := i-N
    have eq : N+j=i := Nat.add_sub_of_le (by omega)
    have len : j<C.size := by dsimp [j]; omega
    have gm : gateAt C j∈C.gates := by
      have l : j<C.gates.length := len
      rw [gateAt,List.getD_eq_getElem _ _ l]; exact List.getElem_mem l
    change (Cut.run C.gates (bits N U)).getD i false=true → (Cut.run C.gates (bits N W)).getD i false=true
    rw [←eq,Cut.gv N C back (bits N U) (sample_length ..) j len,Cut.gv N C back (bits N W) (sample_length ..) j len]
    apply Cut.gate_mono _ (mono _ gm).1
    intro v hv; exact ih v (eq ▸ back j len v hv)

theorem matrix_read {n m : ℕ} (G : Fin n → Fin m → Bool) {C : Circuit} (rep : Represents G C)
    (a : Fin n) (c : Fin m) : value (n+m) C C.output {a.val,n+c.val}=G a c := by
  have hi : a.val∈Finset.range (n+m) := Finset.mem_range.mpr (by have := a.isLt; omega)
  have hj : n+c.val∈Finset.range (n+m) := Finset.mem_range.mpr (by have := c.isLt; omega)
  change Cut.V C (sample (n+m) (Finset.range (n+m)) _) C.output=_
  rw [one_pair a c _ hi hj]; exact rep a c

theorem single_zeros {n m : ℕ} {C : Circuit} (G : Fin n → Fin m → Bool)
    (rz : ∀ a, ∃ c, G a c=false) (cz : ∀ c, ∃ a, G a c=false)
    (mono : Monotone2 C) (back : ReadsBack (n+m) C) (rep : Represents G C) :
    (∀ a : Fin n, value (n+m) C C.output {a.val}=false) ∧
    (∀ c : Fin m, value (n+m) C C.output {n+c.val}=false) := by
  have zero (w : ℕ) (U : Finset ℕ) (hw : w∈U) (z : value (n+m) C C.output U=false) :
      value (n+m) C C.output {w}=false := by
    cases v : value (n+m) C C.output {w} with
    | false => rfl
    | true =>
      have yes := values_order C mono back (Finset.singleton_subset_iff.mpr hw) C.output v
      exact False.elim (Bool.false_ne_true (z.symm.trans yes))
  constructor
  · intro a; obtain ⟨c,h⟩ := rz a
    exact zero _ {a.val,n+c.val} (by simp) ((matrix_read G rep a c).trans h)
  · intro c; obtain ⟨a,h⟩ := cz c
    exact zero _ {a.val,n+c.val} (by simp) ((matrix_read G rep a c).trans h)

end CutLib25855.Tree

namespace CutLib25855
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
theorem all_used {n m : ℕ} (G : Fin n → Fin m → Bool) (D : Circuit)
    (mono : Monotone2 D) (back : ReadsBack (n+m) D) (rep : Represents G D) (out : n+m≤D.output)
    (r0 : ∀ a, ∃ c, G a c=false) (c0 : ∀ c, ∃ a, G a c=false)
    (r1 : ∀ a, ∃ c, G a c=true) (c1 : ∀ c, ∃ a, G a c=true) : used (n+m) D=n+m := by
  classical
  let N := n+m
  let O := Tree.value N D D.output
  obtain ⟨zR,zC⟩ := Tree.single_zeros G r0 c0 mono back rep
  have forced (w v : ℕ) (yes : O {w,v}=true) (zero : O {v}=false) : 0<Active D w := by
    by_contra! no
    have same := observed_agree back (Tree.bits N {w,v}) (Tree.bits N {v})
      (Tree.sample_length ..) (Tree.sample_length ..) (fun i low hit => by
        have ne : i≠w := by intro eq; subst i; omega
        unfold Tree.bits
        rw [Tree.sample_read _ _ _ _ low,Tree.sample_read _ _ _ _ low]
        simp [ne]) D.output out
    change O {w,v}=O {v} at same
    rw [yes,zero] at same; contradiction
  have all (w : ℕ) (hw : w∈Finset.range N) : 1≤Active D w := by
    have small : w<n+m := Finset.mem_range.mp hw
    by_cases row : w<n
    · let a : Fin n := ⟨w,row⟩
      obtain ⟨x,hx⟩ := r1 a
      exact forced w (n+x.val) ((Tree.matrix_read G rep a x).trans hx) (zC x)
    · let x : Fin m := ⟨w-n,by omega⟩
      have eq : n+x.val=w := by change n+(w-n)=w; omega
      obtain ⟨a,ha⟩ := c1 x
      rw [←eq]
      apply forced (n+x.val) a.val _ (zR a)
      rw [Finset.pair_comm]
      exact (Tree.matrix_read G rep a x).trans ha
  change ((Finset.range N).filter (fun i => 1≤Active D i)).card=N
  rw [Finset.filter_eq_self.mpr all,Finset.card_range]

end CutLib25855

namespace CutLib25855
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def sharedRaw (N : ℕ) (C : Circuit) := (Finset.range N).filter (fun w=>2≤Active C w)
theorem sharingCosts (N : ℕ) (C : Circuit) :
    (sharedRaw N C).card+(Cut.sharedG44 N C).card ≤ surplus N C ∧
    Cut.marked44 N C≤2*surplus N C ∧ surplus N C ≤ Cut.marked44 N C := by
  classical
  let R:=sharedRaw N C
  let J:=(Cut.sharedG44 N C).image (fun j=>N+j)
  have dis : Disjoint R J := by
    apply Finset.disjoint_left.mpr
    intro w hw hj; have lo:=Finset.mem_range.mp (Finset.mem_filter.mp hw).1
    obtain ⟨j,_,e⟩:=Finset.mem_image.mp hj
    change N+j=w at e;omega
  have sub : R∪J⊆Cut.shared44 N C := by
    intro w hw
    rcases Finset.mem_union.mp hw with a|b
    · obtain ⟨l,v⟩:=Finset.mem_filter.mp a
      have low:=Finset.mem_range.mp l
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),v⟩
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp b
      obtain ⟨l,v⟩:=Finset.mem_filter.mp hj
      have low:=Finset.mem_range.mp l
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),v⟩
  have count:=Finset.card_le_card sub
  have inj : Function.Injective (fun j : ℕ=>N+j) := fun _ _ e=>Nat.add_left_cancel e
  rw [Finset.card_union_of_disjoint dis,show J.card=(Cut.sharedG44 N C).card from Finset.card_image_of_injective _ inj] at count
  have high : (Cut.shared44 N C).card ≤ surplus N C:=many_count _ _
  have masked : (∑w∈Cut.shared44 N C,(Active C w-1))=surplus N C := by
    unfold Cut.shared44 surplus
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hw absent
    have low : ¬2≤Active C w:=fun h=>absent (Finset.mem_filter.mpr ⟨hw,h⟩)
    omega
  have uses : Cut.marked44 N C=(Cut.shared44 N C).card+surplus N C := by
    calc
      _ = ∑w∈Cut.shared44 N C,(1+(Active C w-1)) := by
        apply Finset.sum_congr rfl
        intro w hw
        have h : 2≤Active C w:=(Finset.mem_filter.mp hw).2
        change Active C w=1+(Active C w-1);omega
      _ = _ := by rw [Finset.sum_add_distrib,masked];simp
  change R.card+_≤_ ∧ _
  omega

end CutLib25855


namespace TreeSemantic25855
open Skeleton25855 Shape25855 Private25855 Private25855.Piece Finset
open PEqualNP.MetaComplexity.NestedCover CutLib25855.Tree

variable {N : Nat}
def input (X Y : Finset (Fin N)) := List.ofFn (fun i : Fin N => decide (i∈X)) ++
  List.ofFn (fun i : Fin N => decide (i∈Y))
def val (ds : List Node) (X Y : Finset (Fin N)) (w : Nat) := (ds.foldl Skeleton25855.step (input X Y)).getD w false
def table (ds : List Node) (r : Ref) (X Y : Finset (Fin N)) := r.act (val ds X Y r.idx)

private theorem stable (ds : List Node) (s : List Bool) {i : Nat} (hi : i<s.length) :
    (ds.foldl Skeleton25855.step s).getD i false = s.getD i false := by
  induction ds generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [Skeleton25855.step]; omega)]
    simp [Skeleton25855.step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

private theorem produced (ds : List Node) (s : List Bool) (h : ok s.length ds) (j : Nat) (hj : j<ds.length) :
    let W := fun i => (ds.foldl Skeleton25855.step s).getD i false
    W (s.length+j) = ds[j].act (W ds[j].a) (W ds[j].b) := by
  induction ds generalizing s j with
  | nil => simp at hj
  | cons g gs ih =>
    have hg : g.a<s.length ∧ g.b<s.length := h 0 (by simp)
    cases j with
    | zero =>
      change (gs.foldl Skeleton25855.step (Skeleton25855.step s g)).getD s.length false =
        g.act (((g::gs).foldl Skeleton25855.step s).getD g.a false) (((g::gs).foldl Skeleton25855.step s).getD g.b false)
      rw [stable _ _ (by simp [Skeleton25855.step]),stable _ _ hg.1,stable _ _ hg.2]
      simp [Skeleton25855.step,List.getD_eq_getElem?_getD]
    | succ j =>
      have hh : ok (Skeleton25855.step s g).length gs := by
        intro i hi
        have hp := h (i+1) (by simpa using hi)
        change gs[i].a < s.length+(i+1) ∧ gs[i].b < s.length+(i+1) at hp
        simp [Skeleton25855.step]; omega
      have eq := ih (Skeleton25855.step s g) hh j (by simpa using hj)
      simpa [Skeleton25855.step,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using eq

theorem input_length (X Y : Finset (Fin N)) : (input X Y).length = 2*N := by simp [input]; omega

theorem rawR (ds : List Node) (X Y : Finset (Fin N)) (i : Fin N) : val ds X Y i.val = decide (i∈X) := by
  rw [val,stable _ _ (by rw [input_length]; omega)]
  simp [input,List.getD_eq_getElem?_getD,List.getElem?_append_left (show i.val<(List.ofFn (fun j : Fin N => decide (j∈X))).length by simp)]

theorem rawC (ds : List Node) (X Y : Finset (Fin N)) (i : Fin N) : val ds X Y (N+i.val) = decide (i∈Y) := by
  rw [val,stable _ _ (by rw [input_length]; omega)]
  simp [input,List.getD_eq_getElem?_getD]

theorem nodeVal {ds : List Node} (ord : ok (2*N) ds) (X Y : Finset (Fin N)) (j : Nat) (hj : j<ds.length) :
    val ds X Y (2*N+j) = ds[j].act (val ds X Y ds[j].a) (val ds X Y ds[j].b) := by
  simpa only [input_length,val] using produced ds (input X Y) (by rwa [input_length]) j hj

section
open PEqualNP.CircuitLowerBounds
abbrev Values (N : Nat) := Finset (Fin N) → Finset (Fin N) → Nat → Bool
structure Laws (C : Circuit) (v : Values N) : Prop where
  row : ∀ X Y (i : Fin N), v X Y i.val = decide (i∈X)
  col : ∀ X Y (i : Fin N), v X Y (N+i.val) = decide (i∈Y)
  node : ∀ j < C.size, ∃ op : List Bool → Bool, ∀ X Y,
    v X Y (2*N+j) = op ((gateAt C j).inputs.map (v X Y))
variable {C : Circuit} {v : Values N} {s reg ext : Finset Nat} {root : Nat}

private theorem incoming {j a b} (hj : j∈reg) (hits : (gateAt C j).inputs=[a,b]) (i : Nat) (hi : i < 2*N) :
    (reach (2*N) C reg) i (2*N+j) ↔ (reach (2*N) C reg) i a ∨ (reach (2*N) C reg) i b := by
  have ea : edge (2*N) C reg a (2*N+j) := ⟨j,hj,rfl,by simp [hits]⟩
  have eb : edge (2*N) C reg b (2*N+j) := ⟨j,hj,rfl,by simp [hits]⟩
  refine ⟨fun hp => ?_,fun hp => hp.elim (fun q => q.tail ea) (fun q => q.tail eb)⟩
  obtain ⟨w,q,k,hk,eq,mem⟩ := tail_step hp (by omega)
  have : k=j := by omega
  subst k; simp [hits] at mem
  rcases mem with rfl|rfl; exact Or.inl q; exact Or.inr q

private theorem leaf_eq {z u : Nat} (h : ∀ j∈reg, z≠2*N+j) (path : (reach (2*N) C reg) u z) : u=z := by
  by_contra ne
  obtain ⟨_,_,j,hj,eq,_⟩ := tail_step path ne
  exact h j hj eq

private structure Spec (z : Nat) (t : Piece N) : Prop where
  rows : ∀ i : Fin N, i∈t.rows ↔ i.val∈s ∧ (reach (2*N) C reg) i.val z
  cols : ∀ i : Fin N, i∈t.cols ↔ N+i.val∈s ∧ (reach (2*N) C reg) (N+i.val) z
  eval : ∀ X Y b, (∀ w∈ext, (reach (2*N) C reg) w z → v X Y w=b) → t.eval X Y b = v X Y z

private theorem imply_mem {α : Type*} [DecidableEq α] {X U A : Finset α} (eq : X\A=U\A)
    {i : α} (h : i∉A) : (i∈X ↔ i∈U) := by
  have hh := Finset.ext_iff.mp eq i
  simpa [h] using hh

private theorem fact (T : (Tree (2*N) C s reg root ext)) (law : Laws C v) (ho : C.output < 2*N+C.size) (one : ext.card≤1)
    (out : Bool → Bool) {z : Nat} (hz : z∈(wireSet (2*N) s reg)) {t : Piece N}
    (sp : Spec (v:=v) (C:=C) (s:=s) (reg:=reg) (ext:=ext) z t) :
    t.Factor (fun X Y => out (v X Y C.output)) := by
  classical
  intro X Y U V hx hy he
  let D (i : Nat) := i∈(wireSet (2*N) s reg) ∧ (reach (2*N) C reg) i z ∧ i≠z
  have agree (i : Nat) : i<2*N+C.size → ¬D i → v X Y i = v U V i := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi no
      by_cases eq : i=z
      · subst i
        by_cases hp : ∃ w∈ext, (reach (2*N) C reg) w z
        · obtain ⟨w,hw,path⟩ := hp
          have outside := (T.portData w hw).1
          have ne : w≠z := by intro eq; exact outside (eq ▸ hz)
          have less : w<z := lt_of_le_of_ne (path_le T path) ne
          have vv := ih w less (by omega) (fun h => outside h.1)
          have same (j) (hj : j∈ext) : j=w := Finset.card_le_one.mp one _ hj _ hw
          rw [←sp.eval X Y (v X Y w) (by intro j hj _; rw [same j hj]),
            ←sp.eval U V (v X Y w) (by intro j hj _; rw [same j hj,vv])]
          exact he _
        · rw [←sp.eval X Y false (by intro w hw path; exact (hp ⟨w,hw,path⟩).elim),
              ←sp.eval U V false (by intro w hw path; exact (hp ⟨w,hw,path⟩).elim)]; exact he _
      · by_cases low : i<2*N
        · have noLeaf : ¬(i∈s ∧ (reach (2*N) C reg) i z) := fun h => no ⟨mem_union_left _ h.1,h.2,eq⟩
          by_cases hiN : i<N
          · let a : Fin N := ⟨i,hiN⟩
            have aout : a∉t.rows := fun h => noLeaf ((sp.rows a).mp h)
            change v X Y a.val = v U V a.val
            rw [law.row,law.row,decide_eq_decide]; exact imply_mem hx aout
          · let a : Fin N := ⟨i-N,by omega⟩
            have heq : N+a.val=i := by dsimp [a]; omega
            have aout : a∉t.cols := fun h => noLeaf (heq ▸ (sp.cols a).mp h)
            rw [← heq,law.col,law.col,decide_eq_decide]; exact imply_mem hy aout
        · let j := i-2*N
          have idx : 2*N+j=i := by dsimp [j]; omega
          have hj : j<C.size := by omega
          obtain ⟨op,opval⟩ := law.node j hj
          rw [←idx,opval,opval]
          apply congrArg op; apply List.map_congr_left
          intro w rd
          have lt : w < i := idx ▸ T.back j hj w rd
          apply ih w lt (by omega)
          rintro ⟨hw,p,ne⟩
          have mem := no_escape T hw p ne hj rd
          obtain ⟨jr,hpath⟩ := mem_filter.mp mem
          exact no ⟨idx ▸ mem_union_right s (mem_image_of_mem _ jr),idx ▸ hpath,eq⟩
  have noout : ¬D C.output := fun h => hidden T h.1 h.2.1 h.2.2 rfl
  exact congrArg out (agree _ ho noout)

private theorem build (T : (Tree (2*N) C s reg root ext)) (law : Laws C v) (ho : C.output < 2*N+C.size) (one : ext.card≤1)
    (out : Bool → Bool) (z : Nat) : z∈(wireSet (2*N) s reg) ∨ z∈ext → ∃ t : Piece N,
      Spec (v:=v) (C:=C) (s:=s) (reg:=reg) (ext:=ext) z t ∧ t.Regular (fun X Y => out (v X Y C.output)) := by
  induction z using Nat.strong_induction_on with
  | ind z ih =>
    intro hz
    rcases hz with hz|hz
    · rcases mem_union.mp hz with raw|inside
      · have low := T.rawLt z raw
        have stop : ∀ u, (reach (2*N) C reg) u z ↔ u=z := fun u => ⟨leaf_eq (by intros; omega),fun h => h ▸ .refl⟩
        by_cases lo : z<N
        · let a : Fin N := ⟨z,lo⟩
          have sp : Spec (v:=v) (C:=C) (s:=s) (reg:=reg) (ext:=ext) z (.row a) := by
            refine ⟨?_,?_,?_⟩
            · intro i; simp only [rows,mem_singleton,stop,Fin.ext_iff]; dsimp only [a]
              exact ⟨fun e => ⟨e ▸ raw,e⟩,And.right⟩
            · intro i; simp [cols,stop,show N+i.val≠z by omega]
            · intro X Y b _; exact (law.row X Y a).symm
          exact ⟨_,sp,fact T law ho one out (mem_union_left _ raw) sp⟩
        · let a : Fin N := ⟨z-N,by omega⟩
          have eq : N+a.val=z := by dsimp [a]; omega
          have sp : Spec (v:=v) (C:=C) (s:=s) (reg:=reg) (ext:=ext) z (.col a) := by
            refine ⟨?_,?_,?_⟩
            · intro i; simp [rows,stop,show i.val≠z by omega]
            · intro i; simp only [cols,mem_singleton,stop,Fin.ext_iff]
              constructor
              · intro h; have hi : N+i.val=z := by omega
                exact ⟨hi ▸ raw,hi⟩
              · rintro ⟨_,h⟩; omega
            · intro X Y b _; rw [←eq]; exact (law.col X Y a).symm
          exact ⟨_,sp,fact T law ho one out (mem_union_left _ raw) sp⟩
      · obtain ⟨j,hj,rfl⟩ := mem_image.mp inside
        have valid := mem_range.mp (T.valid hj)
        obtain ⟨a,b,hits⟩ := binary_list _ (T.gates j hj).2.1
        have ra : a∈(gateAt C j).inputs := by simp [hits]
        have rb : b∈(gateAt C j).inputs := by simp [hits]
        have ea : edge (2*N) C reg a (2*N+j) := ⟨j,hj,rfl,ra⟩
        have eb : edge (2*N) C reg b (2*N+j) := ⟨j,hj,rfl,rb⟩
        obtain ⟨ta,sa,ga⟩ := ih a (T.back j valid a ra) ((T.gates j hj).2.2 a ra)
        obtain ⟨tb,sb,gb⟩ := ih b (T.back j valid b rb) ((T.gates j hj).2.2 b rb)
        obtain ⟨op,hval⟩ := law.node j valid
        let t := Piece.gate (fun x y => op [x,y]) ta tb
        have sp : Spec (v:=v) (C:=C) (s:=s) (reg:=reg) (ext:=ext) (2*N+j) t := by
          refine ⟨?_,?_,?_⟩
          · intro i; simp only [t,rows,mem_union,sa.rows,sb.rows,incoming (N:=N) hj hits i.val (by omega),and_or_left]
          · intro i; simp only [t,cols,mem_union,sa.cols,sb.cols,incoming (N:=N) hj hits (N+i.val) (by omega),and_or_left]
          · intro X Y c port
            simp [t,eval,hval X Y,hits,sa.eval X Y c (fun w hw p => port w hw (p.tail ea)),
              sb.eval X Y c (fun w hw p => port w hw (p.tail eb))]
        exact ⟨t,sp,fact T law ho one out (mem_union_right s (mem_image_of_mem _ hj)) sp,ga,gb⟩
    · have outside := (T.portData z hz).1
      have stop : ∀ u, (reach (2*N) C reg) u z → u=z := fun _ => leaf_eq (by
        intro j hj eq; exact outside (eq ▸ mem_union_right s (mem_image_of_mem _ hj)))
      refine ⟨.port,⟨?_,?_,?_⟩,?_⟩
      · intro i; simp only [rows,notMem_empty,false_iff]; rintro ⟨hs,hp⟩
        exact outside (stop i hp ▸ mem_union_left _ hs)
      · intro i; simp only [cols,notMem_empty,false_iff]; rintro ⟨hs,hp⟩
        exact outside (stop _ hp ▸ mem_union_left _ hs)
      · intro X Y b h; exact (h z hz .refl).symm
      · intro X Y U V hx hy _; simp only [rows,cols,sdiff_empty] at hx hy; subst U; subst V; rfl


theorem transport (T : (Tree (2*N) C s reg root ext)) (law : Laws C v) (ho : C.output < 2*N+C.size) (one : ext.card≤1)
    (out : Bool → Bool) : ∃ t : Piece N,
      (∀ i : Fin N, i∈t.rows ↔ i.val∈s) ∧ (∀ i : Fin N, i∈t.cols ↔ N+i.val∈s) ∧
      t.Regular (fun X Y => out (v X Y C.output)) ∧
      (ext=∅ → ∀ X Y, t.eval X Y false = t.eval X Y true) := by
  obtain ⟨t,sp,h⟩ := build T law ho one out root (Or.inl T.rootMem)
  refine ⟨t,?_,?_,h,?_⟩
  · intro i; rw [sp.rows]; exact and_iff_left_of_imp fun hi => to_root T _ (mem_union_left _ hi)
  · intro i; rw [sp.cols]; exact and_iff_left_of_imp fun hi => to_root T _ (mem_union_left _ hi)
  · intro empty X Y; rw [sp.eval X Y false (by simp [empty]),sp.eval X Y true (by simp [empty])]

theorem piece_of_tree {ds : List Node} {r : Ref} (ord : ok (2*N) ds)
    (ho : r.idx < 2*N+ds.length) (h : Tree (2*N) (shape ds r.idx) s reg root ext) (one : ext.card≤1) :
    ∃ t : Piece N, (∀ i : Fin N, i∈t.rows ↔ i.val∈s) ∧ (∀ i : Fin N, i∈t.cols ↔ N+i.val∈s) ∧
      t.Regular (table ds r) ∧ (ext=∅ → ∀ X Y, t.eval X Y false = t.eval X Y true) := by
  have law : Laws (shape ds r.idx) (val ds (N:=N)) := by
    refine ⟨rawR ds,rawC ds,?_⟩
    intro j hj; have hlt : j<ds.length := by simpa [shape,Circuit.size] using hj
    refine ⟨fun l => ds[j].act (l.getD 0 false) (l.getD 1 false),?_⟩
    intro X Y; simpa [Shape25855.wire hlt,Shape25855.gate] using nodeVal ord X Y j hlt
  exact transport h law (by simpa [shape,Circuit.size] using ho) one r.act


def down (n : Nat) (H : List Nat) (w : Nat) :=
  if w<n then w else if w<n+H.length then H.getD (w-n) 0 else w-H.length

private theorem down_rename (n : Nat) (H : List Nat) (w : Nat) :
    down n H (if w<n then if w∈H then n+H.idxOf w else w else w+H.length) = w := by
  by_cases hr : w<n
  · by_cases hh : w∈H
    · have idx := List.idxOf_lt_length_of_mem hh
      simp [hr,hh,down,idx,List.getD_eq_getElem?_getD]
    · simp [hr,hh,down]
  · simp [hr,down,show ¬ w+H.length<n by omega,show ¬ w+H.length<n+H.length by omega]

def markedVal (ds : List Node) (H : List Nat) (X Y : Finset (Fin N)) (i : Nat) :=
  val ds X Y (down (2*N) H i)

theorem markedLaws {D : Circuit} {ds : List Node} (H : List Nat) (raw : ∀ w∈H,w<2*N)
    (ordered : ok (2*N) ds) (size : D.size=H.length+ds.length)
    (markers : ∀ j (hj : j<H.length), (gateAt D j).inputs=[H[j]])
    (nodes : ∀ j (hj : j<ds.length),
      let up := fun w => if w<2*N then if w∈H then 2*N+H.idxOf w else w else w+H.length
      (gateAt D (H.length+j)).inputs = [up ds[j].a,up ds[j].b]) :
    Laws (N:=N) D (markedVal ds H) := by
  refine ⟨?_,?_,?_⟩
  · intro X Y i
    simpa only [markedVal,down,ite_eq_left (show i.val<2*N by omega)] using rawR ds X Y i
  · intro X Y i
    simpa only [markedVal,down,ite_eq_left (show N+i.val<2*N by omega)] using rawC ds X Y i
  · intro j hj
    by_cases mark : j<H.length
    · refine ⟨fun l => l.getD 0 false,?_⟩; intro X Y
      have hraw := raw _ (List.getElem_mem mark)
      simp [markedVal,down,markers j mark,mark,hraw,List.getD_eq_getElem?_getD]
    · let k := j-H.length
      have h : k<ds.length := by dsimp [k]; omega
      have e : j=H.length+k := by dsimp [k]; omega
      refine ⟨fun l => ds[k].act (l.getD 0 false) (l.getD 1 false),?_⟩
      intro X Y
      rw [e,nodes k h]
      have dd : down (2*N) H (2*N+(H.length+k)) = 2*N+k := by simp [down]; omega
      simpa only [List.map_cons,List.map_nil,List.getD_cons_zero,List.getD_cons_succ,markedVal,dd,down_rename] using
        nodeVal ordered X Y k h

theorem marked_output {ds : List Node} (H : List Nat) (r : Ref) (ho : 2*N≤r.idx) (X Y : Finset (Fin N)) :
    r.act (markedVal ds H X Y (r.idx+H.length)) = table ds r X Y := by
  simp [markedVal,table,down,show ¬r.idx+H.length<2*N by omega,show ¬r.idx+H.length<2*N+H.length by omega]

end
end TreeSemantic25855


namespace Prune25855
open Skeleton25855


def Live (n : Nat) (gs : List Node) (r : Ref) : Prop :=
  ∀ i (_hi : i < gs.length), n+i = r.idx ∨ ∃ (j : Nat) (hj : j < gs.length),
    i < j ∧ (gs[j].a = n+i ∨ gs[j].b = n+i)

theorem last_output {n : Nat} {gs : List Node} {r : Ref} (h : Live n gs r)
    (hgs : gs ≠ []) : r.idx = n + (gs.length-1) := by
  have hlen := List.length_pos_of_ne_nil hgs
  rcases h (gs.length-1) (by omega) with he|⟨j,hj,hij,_⟩
  · exact he.symm
  · omega

theorem later_read {n : Nat} {gs : List Node} {r : Ref} (h : Live n gs r)
    (i : Nat) (hi : i+1 < gs.length) : ∃ (j : Nat) (hj : j < gs.length),
      i < j ∧ (gs[j].a = n+i ∨ gs[j].b = n+i) := by
  have hne : gs ≠ [] := by intro e; simp [e] at hi
  have ho := last_output h hne
  exact (h i (by omega)).resolve_left (by omega)

private def shift (n i : Nat) := if i < n then i else i-1
private def lower (n : Nat) (g : Node) : Node := ⟨shift n g.a, shift n g.b, g.act⟩

private theorem skip {s : List Bool} (v : Bool) (t : List Bool) {i : Nat} (hi : i ≠ s.length) :
    (s ++ v::t).getD i false = (s ++ t).getD (shift s.length i) false := by
  by_cases h : i < s.length
  · simp [shift, h, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · have h₁ : s.length ≤ i := by omega
    have h₂ : s.length ≤ i-1 := by omega
    simp only [List.getD_eq_getElem?_getD, shift, ite_eq_right h, List.getElem?_append_right h₁,
      List.getElem?_append_right h₂]
    rw [show i - s.length = (i-1-s.length)+1 by omega, List.getElem?_cons_succ]

private theorem run_lower (gs : List Node) (s : List Bool) (v : Bool) (t : List Bool)
    (avoid : ∀ g ∈ gs, g.a ≠ s.length ∧ g.b ≠ s.length) :
    ∃ t', gs.foldl step (s ++ v::t) = s ++ v::t' ∧
      (gs.map (lower s.length)).foldl step (s++t) = s++t' := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    have ha := avoid g (by simp)
    let w := g.act ((s++t).getD (shift s.length g.a) false) ((s++t).getD (shift s.length g.b) false)
    have old : step (s++v::t) g = s++v::(t++[w]) := by
      unfold step; rw [skip v t ha.1,skip v t ha.2,List.append_assoc]; rfl
    have new : step (s++t) (lower s.length g) = s++(t++[w]) := by simp [step,lower,w,List.append_assoc]
    simpa only [List.map_cons, List.foldl_cons, old, new] using
      ih (t++[w]) (fun d hd => avoid d (by simp [hd]))

private theorem down_ok {n : Nat} {gs : List Node} (hg : ok (n+1) gs)
    (avoid : ∀ g ∈ gs, g.a ≠ n ∧ g.b ≠ n) : ok n (gs.map (lower n)) := by
  intro i hi
  have hi' : i < gs.length := by simpa using hi
  have hg' := hg i hi'; have ha := avoid gs[i] (List.getElem_mem hi')
  simp only [List.getElem_map,lower,shift]
  split <;> split <;> omega

private theorem down_live {n : Nat} {gs : List Node} {r : Ref} (hl : Live (n+1) gs r) :
    Live n (gs.map (lower n)) ⟨shift n r.idx,r.act⟩ := by
  intro i hi
  rcases hl i (by simpa using hi) with ho|⟨j,hj,hij,h⟩
  · left; simp [←ho,shift]; omega
  · right; refine ⟨j,by simpa using hj,hij,?_⟩
    simp only [List.getElem_map,lower]; rcases h with h|h
    · left; simp [h,shift]; omega
    · right; simp [h,shift]; omega

private theorem up_ok {n : Nat} {g : Node} {es : List Node} (hg : g.a < n ∧ g.b < n)
    (he : ok (n+1) es) : ok n (g::es) := by
  intro i hi; cases i with
  | zero => simpa using hg
  | succ i => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he i (by simpa using hi)

private theorem up_live {n : Nat} {g : Node} {es : List Node} {r : Ref}
    (h : Live (n+1) es r)
    (used : n = r.idx ∨ ∃ (j : Nat) (hj : j < es.length), es[j].a = n ∨ es[j].b = n) :
    Live n (g::es) r := by
  intro i hi; cases i with
  | zero =>
    rcases used with ho|⟨j,hj,used⟩
    · left; simpa using ho
    · right; exact ⟨j+1,by simpa using hj,by omega,by simpa using used⟩
  | succ i =>
    obtain ho|⟨j,hj,hij,used⟩ := h i (by simpa using hi)
    · left; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ho
    · right; exact ⟨j+1,by simpa using hj,by omega,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using used⟩


theorem prune {n : Nat} (gs : List Node) (r : Ref) (ho : ok n gs) (hr : r.idx < n+gs.length) :
    ∃ (es : List Node) (r' : Ref), ok n es ∧ es.length ≤ gs.length ∧ r'.idx < n+es.length ∧
      Live n es r' ∧ ∀ s : List Bool, s.length=n → r.run (gs.foldl step s) = r'.run (es.foldl step s) := by
  classical
  induction gs generalizing n with
  | nil => exact ⟨[],r,ho,by simp,hr,by simp [Live],by simp⟩
  | cons g gs ih =>
    have hg : g.a < n ∧ g.b < n := ho 0 (by simp)
    have ht : ok (n+1) gs := fun i hi => by
      have hh := ho (i+1) (by simpa using hi)
      change gs[i].a < n + (i+1) ∧ gs[i].b < n + (i+1) at hh
      omega
    obtain ⟨es,r',he,hlen,hidx,hl,ev⟩ := ih ht (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr)
    by_cases use : n = r'.idx ∨ ∃ (j : Nat) (hj : j < es.length), es[j].a = n ∨ es[j].b = n
    · refine ⟨g::es,r',up_ok hg he,by simpa using hlen,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hidx,up_live hl use,?_⟩
      intro s hs; exact ev (step s g) (by simp [step,hs])
    · have out : r'.idx ≠ n := by intro h; exact use (Or.inl h.symm)
      have avoid : ∀ x ∈ es, x.a ≠ n ∧ x.b ≠ n := by
        intro x hx
        obtain ⟨j,hj,hx⟩ := List.getElem_of_mem hx
        subst x; exact ⟨fun h => use (Or.inr ⟨j,hj,Or.inl h⟩),fun h => use (Or.inr ⟨j,hj,Or.inr h⟩)⟩
      refine ⟨es.map (lower n),⟨shift n r'.idx,r'.act⟩,down_ok he avoid,by simp; omega,?_,down_live hl,?_⟩
      · simp [shift]; split <;> omega
      · intro s hs; subst n
        let v := g.act (s.getD g.a false) (s.getD g.b false)
        obtain ⟨t,ht₁,ht₂⟩ := run_lower es s v [] avoid
        simp only [List.append_nil] at ht₂
        change r.run (gs.foldl step (step s g)) = _
        rw [ev (step s g) (by simp [step])]
        change r'.act ((es.foldl step (s++[v])).getD r'.idx false) = r'.act (((es.map (lower s.length)).foldl step s).getD (shift s.length r'.idx) false)
        rw [ht₁,ht₂,skip v t out]

end Prune25855

namespace Partition25855
open Skeleton25855 Shape25855 Prune25855 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover CutLib25855
open scoped Classical
theorem partition {n : Nat} {ds : List Node} {o : Ref} (ordered : ok n ds) (live : Live n ds o) (pos : ds ≠ []) :
    let D := shape ds o.idx
    let K := surplus n D
    ∃ P Q : List (Finset Nat), P.length+3*Q.length ≤ 13*K+1 ∧
      (P++Q).Pairwise (fun A B => Disjoint A B) ∧ (P++Q).toFinset.biUnion id = Partition.once69 n D ∧
      (∀ S ∈ P, S.Nonempty ∧ Cut.tree44 n D S ∅) ∧ (∀ S ∈ Q, S.Nonempty ∧ ∃ b, Cut.tree44 n D S {b}) ∧
      ds.length+1 = used n D + K := by
  classical
  intro D K
  have sz : D.size = ds.length := by simp [D,shape,Circuit.size]
  have sh : Partition.shapes69 D := by intro g hg; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hg; exact Or.inl ⟨Or.inr rfl,rfl⟩
  have back := earlier ordered o.idx
  have gt : 0 < D.size := by rw [sz]; exact List.length_pos_of_ne_nil pos
  have last : D.output+1 = n+D.size := by change o.idx+1=_; rw [last_output live pos,sz]; have := List.length_pos_of_ne_nil pos; omega
  have usedLater : ∀ j < D.size, j+1 < D.size → 0 < Active D (n+j) := by
    intro j hj h; rw [sz] at h; obtain ⟨t,ht,_,rd⟩ := later_read live j h
    unfold Active; rw [sz]; exact counted ht rd
  have noNeg : (Partition.neg69 D).card = 0 := by
    apply Finset.card_eq_zero.mpr; apply Finset.eq_empty_iff_forall_notMem.mpr; intro j h
    obtain ⟨mem,hg⟩ := Finset.mem_filter.mp h
    have lt : j < ds.length := by simpa [sz] using Finset.mem_range.mp mem
    change (gateAt (shape ds o.idx) j).op = .not at hg; rw [wire lt] at hg; contradiction
  obtain ⟨P,Q,t,hp,hq,_,dis,cover,pr,ch⟩ := provedCut n D sh back gt last usedLater
  change P.length+t ≤ (Cut.sharedG44 n D).card+(Partition.neg69 D).card+1 at hp
  change Q.length+t ≤ 2*(Cut.marked44 n D+(Partition.neg69 D).card) at hq
  have hc := sharingCosts n D
  have balance := budget_eq D sh back gt usedLater
  unfold budget at balance
  exact ⟨P,Q,by dsimp [K]; omega,dis,cover,pr,ch,by rw [←sz]; dsimp [K]; omega⟩
end Partition25855

namespace Mark25855
open Skeleton25855 Prune25855 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover CutLib25855
open scoped Classical

def rename (n : Nat) (H : List Nat) (w : Nat) :=
  if w<n then if w∈H then n+H.idxOf w else w else w+H.length
def marker (w : Nat) : Gate := ⟨.not,[w]⟩
def node (n : Nat) (H : List Nat) (d : Node) : Gate := ⟨.or,[rename n H d.a,rename n H d.b]⟩
def shape (n : Nat) (H : List Nat) (ds : List Node) (o : Nat) : Circuit :=
  ⟨H.map marker ++ ds.map (node n H),o+H.length⟩
@[simp] theorem size (n H ds o) : (shape n H ds o).size=H.length+ds.length := by simp [shape,Circuit.size]
theorem markerAt {n H ds o j} (hj : j<H.length) : gateAt (shape n H ds o) j=marker H[j] := by
  simp [shape,gateAt,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa using hj : j<(H.map marker).length),hj]
theorem nodeAt {n H ds o j} (hj : j<ds.length) : gateAt (shape n H ds o) (H.length+j)=node n H ds[j] := by
  simp [shape,gateAt,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp : (H.map marker).length≤H.length+j),hj]

theorem renBound {n H w j} (h : w<n+j) : rename n H w<n+H.length+j := by
  unfold rename; split <;> rename_i hr
  · split <;> rename_i hc
    · have := List.idxOf_lt_length_of_mem hc; omega
    · omega
  · omega

theorem earlier {n H ds o} (raw : ∀ w∈H,w<n) (ordered : ok n ds) : ReadsBack n (shape n H ds o) := by
  intro j hj w hw
  change j < (shape n H ds o).size at hj
  rw [size] at hj
  by_cases first : j<H.length
  · rw [markerAt first] at hw
    obtain rfl := List.mem_singleton.mp hw
    have := raw _ (List.getElem_mem first); omega
  · let k := j-H.length
    have hk : k<ds.length := by dsimp [k]; omega
    have eq : j=H.length+k := by dsimp [k]; omega
    rw [eq,nodeAt hk] at hw
    simp only [node,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl
    · have := renBound (H:=H) (ordered k hk).1; omega
    · have := renBound (H:=H) (ordered k hk).2; omega

theorem shapeOK (n H ds o) : Partition.shapes69 (shape n H ds o) := by
  intro g hg
  change g∈_ ++ _ at hg
  rcases List.mem_append.mp hg with a|a <;> obtain ⟨w,_,rfl⟩ := List.mem_map.mp a
  · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨Or.inr rfl,rfl⟩

theorem negs (n H ds o) : (Partition.neg69 (shape n H ds o)).card=H.length := by
  classical
  have eq : Partition.neg69 (shape n H ds o)=Finset.range H.length := by
    ext j
    change (j∈(Finset.range (shape n H ds o).size).filter (fun k => (gateAt (shape n H ds o) k).op=.not)) ↔ _
    simp only [Finset.mem_filter,Finset.mem_range,size]
    by_cases first : j<H.length
    · simp [markerAt first,marker,first]; omega
    · constructor
      · rintro ⟨lt,op⟩
        have hk : j-H.length<ds.length := by omega
        rw [show j=H.length+(j-H.length) by omega,nodeAt hk] at op
        contradiction
      · exact fun h => (first h).elim
  simp [eq]

theorem counted {D : Circuit} {w j : Nat} (hj : j<D.size) (rd : w∈(gateAt D j).inputs) : 0<Active D w := by
  have hp := List.count_pos_iff.mpr rd
  exact hp.trans_le (Finset.single_le_sum (fun j _ => Nat.zero_le ((gateAt D j).inputs.count w)) (Finset.mem_range.mpr hj))

theorem live {n H ds o} (nd : H.Nodup) (raw : ∀ w∈H,w<n)
    (uses : ∀ w∈H, ∃ j : Nat, ∃ hj : j<ds.length, ds[j].a=w ∨ ds[j].b=w)
    (live : Live n ds o) : ∀ j<(shape n H ds o.idx).size, j+1<(shape n H ds o.idx).size →
      0<Active (shape n H ds o.idx) (n+j) := by
  intro j hj hn
  simp only [size] at hj hn
  by_cases first : j<H.length
  · have hm := List.getElem_mem first
    obtain ⟨k,hk,rd⟩ := uses _ hm
    have eq : rename n H H[j]=n+j := by simp [rename,raw _ hm,hm,nd.idxOf_getElem j first]
    apply counted (j:=H.length+k) (by simp; omega)
    rw [nodeAt hk]; change n+j∈[_,_]; simp only [List.mem_cons,List.not_mem_nil,or_false]
    rcases rd with e|e; exact Or.inl (e ▸ eq.symm); exact Or.inr (e ▸ eq.symm)
  · let i := j-H.length
    have hi : i+1<ds.length := by dsimp [i]; omega
    obtain ⟨k,hk,_,rd⟩ := later_read live i hi
    have eq : rename n H (n+i)=n+j := by simp [rename]; dsimp [i]; omega
    apply counted (j:=H.length+k) (by simp; omega)
    rw [nodeAt hk]; simp only [node,List.mem_cons,List.not_mem_nil,or_false]
    rcases rd with e|e; exact Or.inl (e ▸ eq.symm); exact Or.inr (e ▸ eq.symm)

end Mark25855

namespace Mark25855
open Skeleton25855 Prune25855 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover CutLib25855
open scoped Classical

theorem hits {n H w} (hw : w<n) (a : Nat) : rename n H a=w ↔ a=w ∧ w∉H := by
  unfold rename
  split <;> rename_i h
  · split <;> rename_i e <;> constructor <;> intro he <;> grind
  · omega

theorem rawReads {n H ds o w} (nd : H.Nodup) (hw : w<n) :
    Active (shape n H ds o) w = if w∈H then 1 else Active (Shape25855.shape ds o) w := by
  classical
  change (∑ j∈Finset.range (shape n H ds o).size, (gateAt _ j).inputs.count w)=_
  rw [size,Finset.sum_range_add]
  by_cases mark : w∈H
  · rw [if_pos mark]
    have no (a) : rename n H a≠w := fun h => ((hits hw a).mp h).2 mark
    have tail : (∑ j∈Finset.range ds.length, (gateAt (shape n H ds o) (H.length+j)).inputs.count w)=0 := by
      apply Finset.sum_eq_zero
      intro j hj; rw [nodeAt (Finset.mem_range.mp hj)]
      simp [node,no,List.count_cons,beq_iff_eq]
    rw [tail,Nat.add_zero]
    let j := H.idxOf w
    have hj : j<H.length := List.idxOf_lt_length_of_mem mark
    have ej : H[j]=w := List.getElem_idxOf hj
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj) (fun k hk ne => ?_)]
    · rw [markerAt hj]; simp [marker,ej]
    · have lk := Finset.mem_range.mp hk
      have neq : H[k]≠w := by
        intro e; have eq := nd.idxOf_getElem k lk
        rw [e] at eq; exact ne eq.symm
      rw [markerAt lk]; simp [marker,neq]
  · rw [if_neg mark]
    have zero : (∑ j∈Finset.range H.length, (gateAt (shape n H ds o) j).inputs.count w)=0 := by
      apply Finset.sum_eq_zero
      intro j hj; have lt := Finset.mem_range.mp hj
      have neq : H[j]≠w := fun eq => mark (eq ▸ List.getElem_mem lt)
      rw [markerAt lt]; simp [marker,neq]
    rw [zero,Nat.zero_add]
    change _ = ∑ j∈Finset.range (Shape25855.shape ds o).size, (gateAt (Shape25855.shape ds o) j).inputs.count w
    rw [show (Shape25855.shape ds o).size=ds.length by simp [Shape25855.shape,Circuit.size]]
    apply Finset.sum_congr rfl
    intro j hj; have lt := Finset.mem_range.mp hj
    rw [nodeAt lt,Shape25855.wire lt]
    simp [node,Shape25855.gate,List.count_cons,hits hw,mark,beq_iff_eq]

theorem avoids {n H ds o j w} (hw : w∈H) (raw : w<n) (hj : j<(shape n H ds o).size)
    (op : (gateAt (shape n H ds o) j).op=.and ∨ (gateAt (shape n H ds o) j).op=.or) :
    w∉(gateAt (shape n H ds o) j).inputs := by
  by_cases first : j<H.length
  · rw [markerAt first] at op; rcases op with h|h <;> contradiction
  · have sz := hj
    rw [size] at sz
    have lt : j-H.length<ds.length := by omega
    rw [show j=H.length+(j-H.length) by omega,nodeAt lt]
    have no (a) : w≠rename n H a := fun e => ((hits raw a).mp e.symm).2 hw
    simp [node,no]


theorem singleton {n H ds o S E w} (raw : w<n) (hw : w∈H) (hs : w∈S)
    (back : ReadsBack n (shape n H ds o))
    (tree : Cut.tree44 n (shape n H ds o) S E) : S={w} ∧ E=∅ := by
  classical
  obtain ⟨reg,root,sub,hr,_,boundary,ops,conn⟩ := tree
  have wz : readsIn (shape n H ds o) reg w=0 := by
    apply Finset.sum_eq_zero
    intro j hj; apply List.count_eq_zero.mpr
    exact avoids hw raw (Finset.mem_range.mp (sub hj)) (ops j hj).1
  have rootEq : w=root := by
    by_contra ne
    have := (conn w (Finset.mem_union_left _ hs) ne).1; omega
  subst root
  have empty : reg=∅ := by
    by_contra h
    have nonempty := Finset.nonempty_iff_ne_empty.mpr h
    let k := reg.max' nonempty
    have hk : k∈reg := Finset.max'_mem _ _
    have pos := (conn (n+k) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)) (by omega)).1
    obtain ⟨j,hj,pin⟩ := Cut.find_pin44 (C:=shape n H ds o) (T:=reg) (w:=n+k) (by omega)
    have earlier := back j (Finset.mem_range.mp (sub hj)) (n+k) pin
    have le : j≤k := Finset.le_max' _ _ hj
    omega
  subst reg
  have eq (v) (hv : v∈S) : v=w := by
    by_contra ne
    have z := (conn v (Finset.mem_union_left _ hv) ne).1
    simp [readsIn] at z
  refine ⟨Finset.ext fun x => by simp only [Finset.mem_singleton];exact ⟨eq x,fun e => e ▸ hs⟩,?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he; have z := (boundary e he).2.2; simp [readsIn] at z

end Mark25855

namespace Mark25855
open Skeleton25855 Prune25855 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover CutLib25855
open Finset
open scoped Classical

theorem partition {n H ds o} (nd : H.Nodup) (raw : ∀ w∈H,w<n)
    (onceH : ∀ w∈H, Active (Shape25855.shape ds o.idx) w=1)
    (ord : ok n ds) (liveD : Live n ds o) (pos : ds≠[]) :
    let D := shape n H ds o.idx
    let K := surplus n D
    ∃ P Q : List (Finset Nat), P.length+3*Q.length ≤ 13*K+1+6*H.length ∧
      (P++Q).Pairwise (fun A B => Disjoint A B) ∧
      (P++Q).toFinset.biUnion id = Partition.once69 n (Shape25855.shape ds o.idx) \ H.toFinset ∧
      (∀ S∈P,S.Nonempty ∧ Cut.tree44 n D S ∅) ∧ (∀ S∈Q,S.Nonempty ∧ ∃ b,Cut.tree44 n D S {b}) ∧
      ds.length+1=used n (Shape25855.shape ds o.idx)+K := by
  classical
  intro D K
  let O := Shape25855.shape ds o.idx
  have uses (w) (hw : w∈H) : ∃ j : Nat, ∃ hj : j<ds.length, ds[j].a=w ∨ ds[j].b=w := by
    have count : Active O w=1 := onceH w hw
    obtain ⟨j,hj,pin⟩ := Cut.find_pin44 (C:=O) (T:=range O.size) (w:=w) (by change 0<Active O w; omega)
    have lt : j<ds.length := by simpa [O,Shape25855.shape,Circuit.size] using mem_range.mp hj
    change w∈(gateAt (Shape25855.shape ds o.idx) j).inputs at pin
    rw [Shape25855.wire lt] at pin
    exact ⟨j,lt,by simpa [Shape25855.gate,eq_comm] using pin⟩
  have earlierD := earlier (ds:=ds) (o:=o.idx) raw ord
  have sz : D.size=H.length+ds.length := size ..
  have dpos := List.length_pos_of_ne_nil pos
  have last : D.output+1=n+D.size := by
    change o.idx+H.length+1=_
    rw [last_output liveD pos,sz]; omega
  have lives := live nd raw uses liveD
  have eqR {w} (hw : w<n) : Active D w=Active O w := by
    rw [show Active D w=_ from rawReads nd hw];split <;> rename_i h
    · exact (onceH w h).symm
    · rfl
  have eqU : used n D=used n O := by
    unfold used
    congr 1
    exact Finset.filter_congr fun w hw => by rw [eqR (Finset.mem_range.mp hw)]
  have eqOnce : Partition.once69 n D=Partition.once69 n O := by
    apply Finset.filter_congr
    intro w hw
    change (Active D w=1) ↔ (Active O w=1)
    rw [eqR (Finset.mem_range.mp hw)]
  have bal := budget_eq D (shapeOK n H ds o.idx) earlierD (by omega) lives
  have negsD : (Partition.neg69 D).card=H.length := negs ..
  unfold budget at bal
  obtain ⟨P,Q,c,hp,hq,_,dis,all,pr,ch⟩ := provedCut n D (shapeOK n H ds o.idx) earlierD (by omega) last lives
  change P.length+c ≤ (Cut.sharedG44 n D).card+(Partition.neg69 D).card+1 at hp
  change Q.length+c ≤ 2*(Cut.marked44 n D+(Partition.neg69 D).card) at hq
  change (P++Q).toFinset.biUnion id = Partition.once69 n D at all
  rw [eqOnce] at all
  let clean (S : Finset Nat) := decide (Disjoint S H.toFinset)
  let P' := P.filter clean
  have excludeQ {S} (inQ : S∈Q) (w) (ws : w∈S) : w∉H := by
    intro wh; obtain ⟨_,b,tree⟩ := ch S inQ
    have abs := (singleton (raw _ wh) wh ws earlierD tree).2
    simp at abs
  have markedPure (w) (wh : w∈H) : {w}∈P := by
    have hit : w∈Partition.once69 n O := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (raw _ wh),onceH w wh⟩
    rw [←all] at hit
    obtain ⟨S,hs,ws⟩ := Finset.mem_biUnion.mp hit
    rcases List.mem_append.mp (List.mem_toFinset.mp hs) with p|q
    · exact (singleton (raw _ wh) wh ws earlierD (pr S p).2).1 ▸ p
    · exact (excludeQ q w ws wh).elim
  have lost : H.length ≤ (P.filter (fun S => !(clean S))).length := by
    have sub : (H.toFinset.image (fun w => {w} : Nat → Finset Nat)) ⊆ (P.filter fun S => !(clean S)).toFinset := by
      intro S hs; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hs
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨markedPure w (List.mem_toFinset.mp hw),by simp [clean,hw]⟩)
    have cap := (Finset.card_le_card sub).trans (List.toFinset_card_le _)
    rwa [Finset.card_image_of_injective _ (fun _ _ e => Finset.singleton_injective e),List.toFinset_card_of_nodup nd] at cap
  refine ⟨P',Q,?_,?_,?_,?_,ch,?_⟩
  · have tot := List.length_eq_countP_add_countP clean (l:=P)
    have negEq : (fun a => decide (¬clean a=true)) = (fun a => !(clean a)) := by funext a;cases clean a <;> decide
    simp only [List.countP_eq_length_filter,negEq] at tot
    have hc := sharingCosts n D
    change (P.filter clean).length + _ ≤ _
    dsimp only [K]; omega
  · exact List.Pairwise.sublist (List.Sublist.append (List.filter_sublist ..) (List.Sublist.refl _)) dis
  · ext w
    simp only [Finset.mem_biUnion,List.mem_toFinset,List.mem_append,id_eq,Finset.mem_sdiff,List.mem_toFinset] at *
    constructor
    · rintro ⟨S,pq,hs⟩
      have kept : S∈P ∨ S∈Q := pq.imp (fun h => (List.mem_filter.mp h).1) id
      refine ⟨?_,?_⟩
      · rw [←all]
        exact Finset.mem_biUnion.mpr ⟨S,List.mem_toFinset.mpr (List.mem_append.mpr kept),hs⟩
      · rcases pq with p|q
        · have dx : Disjoint S H.toFinset := of_decide_eq_true (List.mem_filter.mp p).2
          exact fun wh => Finset.disjoint_left.mp dx hs (List.mem_toFinset.mpr wh)
        · exact excludeQ q w hs
    · rintro ⟨h,wh⟩
      rw [←all] at h
      obtain ⟨S,hs,ws⟩ := Finset.mem_biUnion.mp h
      rcases List.mem_append.mp (List.mem_toFinset.mp hs) with p|q
      · refine ⟨S,Or.inl (List.mem_filter.mpr ⟨p,decide_eq_true ?_⟩),ws⟩
        apply Finset.disjoint_left.mpr
        intro v vs vh
        have hv := List.mem_toFinset.mp vh
        have eq := (singleton (raw _ hv) hv vs earlierD (pr S p).2).1
        have e : w=v := Finset.mem_singleton.mp (eq ▸ ws)
        exact wh (e ▸ hv)
      · exact ⟨S,Or.inr q,ws⟩
  · intro S h; exact pr S (List.mem_filter.mp h).1
  · change ds.length+1=used n O+surplus n D; omega
end Mark25855


namespace Family25855
open Skeleton25855 Prune25855 Private25855 Private25855.Piece TreeSemantic25855 Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover CutLib25855
open scoped Classical

private theorem counts (a b : Nat) (pure : Fin (a+b) → Bool) (flag : ∀ i, pure i=true ↔ i.val<a) :
    (univ.filter fun i => pure i=true).card = a ∧ (univ.filter fun i => pure i=false).card = b := by
  have eq : (univ.filter fun i => pure i=true).card = a := by
    trans (range a).card
    · refine card_bij (fun i _ => i.val) ?_ ?_ ?_
      · intro i hi; exact mem_range.mpr ((flag i).mp (mem_filter.mp hi).2)
      · intro i hi j hj e; exact Fin.ext e
      · intro v hv; have h := mem_range.mp hv
        exact ⟨⟨v,by omega⟩,mem_filter.mpr ⟨mem_univ _,(flag _).mpr h⟩,rfl⟩
    · simp
  refine ⟨eq,?_⟩
  have f : (univ.filter fun i => pure i=false) = univ.filter (fun i => ¬pure i=true) := by ext i; simp
  rw [f]; have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (a+b)))) (fun i => pure i=true)
  simp only [card_univ,Fintype.card_fin,eq] at h; omega

private theorem tree_piece {N : Nat} {ds : List Node} {o : Ref} {H : List Nat}
    (ord : ok (2*N) ds) (raw : ∀ w∈H,w<2*N) (lo : 2*N≤o.idx) (hi : o.idx<2*N+ds.length)
    {S E : Finset Nat} (bound : ∀ i∈S, i<2*N) (small : E.card≤1)
    (tree : Cut.tree44 (2*N) (Mark25855.shape (2*N) H ds o.idx) S E) :
    ∃ t : Piece N, (∀ i : Fin N,i∈t.rows ↔ i.val∈S) ∧ (∀ i : Fin N,i∈t.cols ↔ N+i.val∈S) ∧
      Regular (table ds o) t ∧ (E=∅ → ∀ X Y, eval X Y false t=eval X Y true t) := by
  let D := Mark25855.shape (2*N) H ds o.idx
  obtain ⟨reg,root,inside,member,last,ports,gates,uses⟩ := tree
  have T : Tree.Tree (2*N) D S reg root E :=
    ⟨bound,Mark25855.earlier raw ord,inside,member,gates,ports,last,uses⟩
  have law : Laws D (markedVal (N:=N) ds H) := by
    apply markedLaws H raw ord (Mark25855.size ..)
    · intro j h; rw [Mark25855.markerAt h]; rfl
    · intro j h; rw [Mark25855.nodeAt h]; rfl
  have htop : D.output < 2*N+D.size := by
    change o.idx+H.length < 2*N+(Mark25855.shape (2*N) H ds o.idx).size
    rw [Mark25855.size]; omega
  obtain ⟨t,rr,cc,reg',flat⟩ := transport T law htop small o.act
  refine ⟨t,rr,cc,?_,flat⟩
  have eq : (fun X Y : Finset (Fin N) => o.act (markedVal ds H X Y D.output)) = table ds o :=
    funext fun X => funext fun Y => marked_output H o lo X Y
  rwa [eq] at reg'


theorem assemble {N : Nat} {ds : List Node} {o : Ref} (H : List Nat)
    (ord : ok (2*N) ds) (raw : ∀ w∈H,w<2*N) (lo : 2*N≤o.idx) (hi : o.idx<2*N+ds.length)
    (P Q : List (Finset Nat)) (dis : (P++Q).Pairwise (fun A B => Disjoint A B))
    (cover : (P++Q).toFinset.biUnion id = Partition.once69 (2*N) (Shape25855.shape ds o.idx) \ H.toFinset)
    (ps : ∀ S∈P,S.Nonempty ∧ Cut.tree44 (2*N) (Mark25855.shape (2*N) H ds o.idx) S ∅)
    (qs : ∀ S∈Q,S.Nonempty ∧ ∃ b,Cut.tree44 (2*N) (Mark25855.shape (2*N) H ds o.idx) S {b}) :
    ∃ m : Nat, ∃ t : Fin m → Piece N, ∃ pure : Fin m → Bool,
      (∀ z, Regular (table ds o) (t z)) ∧
      (∀ z w, z≠w → Disjoint (t z).rows (t w).rows) ∧
      (∀ z w, z≠w → Disjoint (t z).cols (t w).cols) ∧
      (∀ z, pure z=true → ∀ X Y, eval X Y false (t z)=eval X Y true (t z)) ∧
      (univ.biUnion fun z => (t z).rows) = univ.filter (fun i : Fin N => Active (Shape25855.shape ds o.idx) i.val=1 ∧ i.val∉H) ∧
      (univ.biUnion fun z => (t z).cols) = univ.filter (fun i : Fin N => Active (Shape25855.shape ds o.idx) (N+i.val)=1 ∧ N+i.val∉H) ∧
      (univ.filter fun i => pure i=true).card + 3*(univ.filter fun i => pure i=false).card = P.length+3*Q.length := by
  classical
  let S (i : Fin (P.length+Q.length)) := (P++Q)[i.val]'(by simp)
  let pure (i : Fin (P.length+Q.length)) := decide (i.val<P.length)
  have pool (w : Nat) : (∃ i, w∈S i) ↔ w∈Partition.once69 (2*N) (Shape25855.shape ds o.idx) \ H.toFinset := by
    rw [←cover]; simp only [mem_biUnion,List.mem_toFinset,id_eq]
    constructor
    · rintro ⟨i,h⟩; exact ⟨S i,List.getElem_mem _,h⟩
    · rintro ⟨A,hA,hw⟩; obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hA
      exact ⟨⟨j,by simpa using hj⟩,hw⟩
  have src (i) (w) (hw : w∈S i) : w<2*N := mem_range.mp (mem_filter.mp (mem_sdiff.mp ((pool w).mp ⟨i,hw⟩)).1).1
  have obtainPiece (i) : ∃ t : Piece N, (∀ j : Fin N,j∈t.rows ↔ j.val∈S i) ∧
      (∀ j : Fin N,j∈t.cols ↔ N+j.val∈S i) ∧ Regular (table ds o) t ∧
      (pure i=true → ∀ X Y, eval X Y false t=eval X Y true t) := by
    by_cases h : i.val<P.length
    · have mem : S i∈P := by simp only [S,List.getElem_append_left h]; exact List.getElem_mem _
      obtain ⟨t,a,b,c,d⟩ := tree_piece ord raw lo hi (src i) (by simp) (ps _ mem).2
      exact ⟨t,a,b,c,fun _ => d rfl⟩
    · have mem : S i∈Q := by dsimp only [S]; rw [List.getElem_append_right]; exact List.getElem_mem _; omega
      obtain ⟨_,w,ht⟩ := qs _ mem
      obtain ⟨t,a,b,c,_⟩ := tree_piece ord raw lo hi (src i) (by simp) ht
      exact ⟨t,a,b,c,by simp [pure,h]⟩
  choose t tr tc reg flat using obtainPiece
  have separate {i j : Fin (P.length+Q.length)} (diff : i≠j) : Disjoint (S i) (S j) := by
    have d (x y : Fin (P.length+Q.length)) (hxy : x<y) : Disjoint (S x) (S y) :=
      List.pairwise_iff_getElem.mp dis x.val y.val _ _ hxy
    exact (lt_or_gt_of_ne diff).elim (d i j) (fun h => (d j i h).symm)
  refine ⟨_,t,pure,reg,?_,?_,flat,?_,?_,?_⟩
  · intro i j h; exact disjoint_left.mpr fun w hw hw' => disjoint_left.mp (separate h) ((tr i w).mp hw) ((tr j w).mp hw')
  · intro i j h; exact disjoint_left.mpr fun w hw hw' => disjoint_left.mp (separate h) ((tc i w).mp hw) ((tc j w).mp hw')
  · ext j; simp only [mem_biUnion,mem_univ,true_and,tr,pool,mem_filter,mem_sdiff,List.mem_toFinset,Partition.once69,mem_range,show j.val<2*N by omega]
    rfl
  · ext j; simp only [mem_biUnion,mem_univ,true_and,tc,pool,mem_filter,mem_sdiff,List.mem_toFinset,Partition.once69,mem_range,show N+j.val<2*N by omega]
    rfl
  · obtain ⟨hP,hQ⟩ := counts P.length Q.length pure (by simp [pure]); rw [hP,hQ]


theorem markers {N : Nat} (rd : Nat → Nat) (R C : Finset (Fin N)) :
    ∃ H : List Nat, H.Nodup ∧ (∀ w∈H,w<2*N) ∧ (∀ w∈H,rd w=1) ∧ H.length≤R.card+C.card ∧
      (∀ i : Fin N, rd i.val=1 → (i.val∈H ↔ i∈R)) ∧
      (∀ i : Fin N, rd (N+i.val)=1 → (N+i.val∈H ↔ i∈C)) := by
  classical
  let U := R.image Fin.val ∪ C.image (fun i => N+i.val)
  let S := U.filter (fun w => rd w=1)
  have size : S.card≤R.card+C.card :=
    (card_filter_le _ _).trans ((card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le))
  refine ⟨S.toList,S.nodup_toList,?_,?_,by simpa using size,?_,?_⟩
  · intro w hw
    have hu := (mem_filter.mp (mem_toList.mp hw : w∈S)).1
    rcases mem_union.mp hu with h|h <;> obtain ⟨i,_,rfl⟩ := mem_image.mp h <;> have := i.isLt <;> omega
  · intro w hw; exact (mem_filter.mp (mem_toList.mp hw : w∈S)).2
  · intro i hi; simp only [mem_toList,S,mem_filter,hi,and_true,U,mem_union,mem_image]
    constructor
    · rintro (⟨j,hj,e⟩|⟨j,hj,e⟩)
      · exact Fin.ext e ▸ hj
      · omega
    · intro h; exact Or.inl ⟨i,h,rfl⟩
  · intro i hi; simp only [mem_toList,S,mem_filter,hi,and_true,U,mem_union,mem_image]
    constructor
    · rintro (⟨j,hj,e⟩|⟨j,hj,e⟩)
      · omega
      · exact Fin.ext (Nat.add_left_cancel e) ▸ hj
    · intro h; exact Or.inr ⟨i,h,rfl⟩

end Family25855

namespace Physical25855
open Skeleton25855 PEqualNP.CircuitLowerBounds
def raw (m : Nat) := (List.range m).map (fun i => (⟨i,id⟩ : Ref))
theorem physicalOutput (m : Nat) (hm : 0 < m) (C : Circuit) (h : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ (ds : List Node) (r : Ref), ok m ds ∧ ds.length = C.gates.countP (fun g => g.inputs.length == 2) ∧ r.idx < m+ds.length ∧
     ∀ s : List Bool, s.length=m → C.eval s = r.run (ds.foldl step s) := by
  obtain ⟨ds,out,hok,hs,hr,hw⟩ := compile C.gates h (raw m) hm (by simp [raw])
  refine ⟨ds,out.getD C.output fallback,hok,hs,?_,?_⟩
  · by_cases lt : C.output < out.length
    · simp [List.getD_eq_getElem?_getD,lt,hr _ (List.getElem_mem lt)]
    · simp [List.getD_eq_getElem?_getD,lt,fallback]; omega
  · intro s hlen
    have he : (raw m).map (fun r => r.run s) = s := by
      apply List.ext_getElem
      · simp [raw,hlen]
      · intro i hi hj; simp [raw,Ref.run,List.getD_eq_getElem?_getD,hj]
    have hh := hw s hlen
    rw [he] at hh
    change (C.gates.foldl physical s).getD C.output false = _
    rw [hh]; simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; cases out[C.output]? <;> rfl
end Physical25855

namespace Support25855
open Skeleton25855 Shape25855 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover CutLib25855

theorem agrees (ds : List Node) (s t : List Bool) (len : s.length=t.length) (o : Nat)
    (start : ∀ i, i < s.length → (i=o ∨ ∃ g ∈ ds, g.a=i ∨ g.b=i) → s.getD i false=t.getD i false) :
    (ds.foldl step s).getD o false = (ds.foldl step t).getD o false := by
  induction ds generalizing s t with
  | nil =>
    by_cases h : o < s.length
    · exact start o h (Or.inl rfl)
    · simp [List.getD_eq_getElem?_getD,h,← len]
  | cons g gs ih =>
    have val (i : Nat) (h : g.a=i ∨ g.b=i) : s.getD i false=t.getD i false := by
      by_cases hi : i < s.length
      · exact start i hi (Or.inr ⟨g,List.mem_cons_self,h⟩)
      · simp [List.getD_eq_getElem?_getD,hi,←len]
    have he : g.act (s.getD g.a false) (s.getD g.b false) = g.act (t.getD g.a false) (t.getD g.b false) := by rw [val g.a (Or.inl rfl),val g.b (Or.inr rfl)]
    apply ih _ _ (by simp [step,len]); intro i hi needed
    have before : i=o ∨ ∃ x ∈ g::gs, x.a=i ∨ x.b=i := by
      rcases needed with h|⟨x,hx,ha⟩; exact Or.inl h; exact Or.inr ⟨x,List.mem_cons_of_mem _ hx,ha⟩
    by_cases lt : i<s.length
    · simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append_left lt,List.getElem?_append_left (len ▸ lt)] using start i lt before
    · have eq : i=s.length := by simp [step] at hi; omega
      subst i; unfold step; rw [Private25855.snoc,Private25855.snoc]; simpa [len] using he

theorem raw_read {n : Nat} {ds : List Node} {r : Ref} (pos : ds ≠ []) (live : Prune25855.Live n ds r) {i : Nat} (hi : i<n) (need : i=r.idx ∨ ∃ g ∈ ds, g.a=i ∨ g.b=i) :
    0 < Active (shape ds r.idx) i := by
  rcases need with eq|⟨g,hg,h⟩
  · rw [Prune25855.last_output live pos] at eq; omega
  · obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    change 0 < readsIn (shape ds r.idx) (Finset.range (shape ds r.idx).size) i
    simpa [shape,Circuit.size] using (counted (o:=r.idx) hj h)
end Support25855

namespace Unread25855
open Skeleton25855 Shape25855 Support25855 PEqualNP.CircuitLowerBounds PEqualNP.Represents CutLib25855 Private25855 Finset

theorem pins {N : Nat} {ds : List Node} {r : Ref} (pos : ds≠[]) (live : Prune25855.Live (2*N) ds r) (i j x y : Fin N)
    (same : ∀ w < 2*N, 0 < Active (shape ds r.idx) w → ((w=i.val ∨ w=N+x.val) ↔ (w=j.val ∨ w=N+y.val))) :
    r.run (ds.foldl Skeleton25855.step (oneEach i x)) = r.run (ds.foldl Skeleton25855.step (oneEach j y)) := by
  apply congrArg r.act; apply agrees; · simp [oneEach]
  intro w hw need
  have low : w<2*N := by simpa [oneEach,two_mul] using hw
  apply Bool.eq_iff_iff.mpr; simpa only [hotPin] using same w low (raw_read pos live low need)

theorem unseen {N v : Nat} (T M : Fin N → Fin N → Bool) (seen : Finset (Fin N))
    (sep : ∀ i j, i≠j → 17+2*(v-1) ≤ distance (T i) (T j)) (out : ∀ i∉seen, ∀ j∉seen,M i=M j) :
    (univ.filter (fun i => i∉seen ∧ distance (T i) (M i)<v)).card ≤ 1 := by
  apply card_le_one.mpr; intro i hi j hj
  obtain ⟨ha,la⟩ := (mem_filter.mp hi).2; obtain ⟨hb,lb⟩ := (mem_filter.mp hj).2
  by_contra ne; have h := good_distance T M (sep i j ne) la lb; rw [out i ha j hb] at h; simp [distance] at h

theorem sides {N v : Nat} {ds : List Node} {r : Ref} (pos : ds≠[]) (live : Prune25855.Live (2*N) ds r)
    (T : Fin N → Fin N → Bool) (sep : ∀ i j, i≠j → 17+2*(v-1) ≤ distance (T i) (T j) ∧ 17+2*(v-1) ≤ distance (Function.swap T i) (Function.swap T j)) :
    let D := shape ds r.idx
    let M := fun i j : Fin N => r.run (ds.foldl Skeleton25855.step (oneEach i j))
    (univ.filter (fun i : Fin N => Active D i.val=0 ∧ distance (T i) (M i)<v)).card ≤ 1 ∧
    (univ.filter (fun i : Fin N => Active D (N+i.val)=0 ∧ distance (Function.swap T i) (Function.swap M i)<v)).card ≤ 1 := by
  intro D M
  constructor
  · let s := univ.filter (fun i : Fin N => 0 < Active D i.val)
    have h := unseen T M s (fun i j ne => (sep i j ne).1) (by
      intro i hi j hj; funext t; apply pins pos live
      intro w hw read; change 0 < Active D w at read; simp only [s,mem_filter,mem_univ,true_and] at hi hj
      have ni : w≠i.val := fun he => by subst w; omega
      have nj : w≠j.val := fun he => by subst w; omega
      simp [ni,nj])
    simpa [s] using h
  · let s := univ.filter (fun i : Fin N => 0 < Active D (N+i.val))
    have h := unseen (Function.swap T) (Function.swap M) s (fun i j ne => (sep i j ne).2) (by
      intro i hi j hj; funext t; apply pins pos live
      intro w hw read; change 0 < Active D w at read; simp only [s,mem_filter,mem_univ,true_and] at hi hj
      have ni : w≠N+i.val := fun he => by subst w; omega
      have nj : w≠N+j.val := fun he => by subst w; omega
      simp [ni,nj])
    simpa [s] using h
end Unread25855

namespace RawCount25855
open Finset

theorem halves (N : Nat) (P : Nat → Prop) [DecidablePred P] :
    ((range (2*N)).filter P).card = (univ.filter (fun i : Fin N => P i.val)).card + (univ.filter (fun i : Fin N => P (N+i.val))).card := by
  classical
  let X := univ.filter (fun i : Fin N => P i.val)
  let Y := univ.filter (fun i : Fin N => P (N+i.val))
  let r := X.image Fin.val
  let c := Y.image (fun i => N+i.val)
  have eq : (range (2*N)).filter P = r ∪ c := by
    ext w
    constructor
    · intro hw; obtain ⟨h,hp⟩ := mem_filter.mp hw; have lt := mem_range.mp h
      by_cases low : w<N
      · exact mem_union_left _ (mem_image.mpr ⟨⟨w,low⟩,mem_filter.mpr ⟨mem_univ _,hp⟩,rfl⟩)
      · have hi : w-N<N := by omega
        have he : N+(w-N)=w := by omega
        exact mem_union_right _ (mem_image.mpr ⟨⟨w-N,hi⟩,mem_filter.mpr ⟨mem_univ _,show P (N+(w-N)) by rw [he]; exact hp⟩,he⟩)
    · intro h; rcases mem_union.mp h with h|h <;> obtain ⟨i,hi,rfl⟩ := mem_image.mp h <;> exact mem_filter.mpr ⟨mem_range.mpr (by have := i.isLt; omega),(mem_filter.mp hi).2⟩
  have dis : Disjoint r c := by
    apply disjoint_left.mpr; intro w hr hc; obtain ⟨i,_,rfl⟩ := mem_image.mp hr; obtain ⟨j,_,he⟩ := mem_image.mp hc; have := i.isLt; omega
  rw [eq,card_union_of_disjoint dis,card_image_of_injective _ Fin.val_injective,card_image_of_injective _ (show Function.Injective (fun i : Fin N => N+i.val) from fun _ _ he => Fin.ext (Nat.add_left_cancel he))]

theorem ledger {N : Nat} (rd : Fin N → Nat) (heavy : Finset (Fin N)) (h : (univ.filter (fun i => rd i=0 ∧ i∉heavy)).card ≤ 1) :
    N ≤ (univ.filter (fun i => 1 ≤ rd i)).card+heavy.card+1 ∧
    N ≤ (univ.filter (fun i => rd i=1 ∧ i∉heavy)).card + (univ.filter (fun i => 2≤rd i)).card+heavy.card+1 := by
  classical
  let z := univ.filter (fun i => rd i=0 ∧ i∉heavy)
  let x := univ.filter (fun i => rd i=1 ∧ i∉heavy)
  let y := univ.filter (fun i => 2≤rd i)
  let a := univ.filter (fun i => 1≤rd i)
  have sub : univ ⊆ x ∪ y ∪ heavy ∪ z := by intro i hi; by_cases hh : i∈heavy <;> simp [x,y,z,hh] <;> omega
  have sub' : univ ⊆ a ∪ heavy ∪ z := by intro i hi; by_cases hh : i∈heavy <;> simp [a,z,hh] <;> omega
  have := card_le_card sub; have := card_le_card sub'; have := card_union_le x y; have := card_union_le (x∪y) heavy; have := card_union_le (x∪y∪heavy) z; have := card_union_le a heavy; have := card_union_le (a∪heavy) z
  change z.card ≤ 1 at h; change N ≤ a.card+heavy.card+1 ∧ N ≤ x.card+y.card+heavy.card+1
  simp only [card_univ,Fintype.card_fin] at *; omega
end RawCount25855

namespace Budget25855
open Skeleton25855 Shape25855 Prune25855 PEqualNP.Represents CutLib25855 Private25855 Finset

def heavySet {N : Nat} (T M : Fin N → Fin N → Bool) (v : Nat) := univ.filter fun i => v ≤ distance (T i) (M i)

theorem ledger {N v : Nat} {ds : List Node} {r : Ref} (pos : ds≠[]) (ord : ok (2*N) ds) (lv : Live (2*N) ds r) (hv : 0<v)
    (T : Fin N → Fin N → Bool) (sep : ∀ i j, i≠j → 17+2*(v-1) ≤ distance (T i) (T j) ∧ 17+2*(v-1) ≤ distance (Function.swap T i) (Function.swap T j)) :
    let D := shape ds r.idx
    let M := fun i j : Fin N => r.run (ds.foldl Skeleton25855.step (oneEach i j))
    let R := heavySet T M v
    let C := heavySet (Function.swap T) (Function.swap M) v
    let k := surplus (2*N) D
    let H := errors T M/v
    k+2*N ≤ ds.length+3+2*H ∧
    2*N ≤ (univ.filter (fun i : Fin N => Active D i.val=1 ∧ i∉R)).card + (univ.filter (fun i : Fin N => Active D (N+i.val)=1 ∧ i∉C)).card + k + 2*H + 2 := by
  classical
  intro D M R C k H
  obtain ⟨rr,cc⟩ := Unread25855.sides pos lv T sep
  have lr := RawCount25855.ledger (fun i : Fin N => Active D i.val) R (by simpa [R,heavySet,M,D] using rr)
  have lc := RawCount25855.ledger (fun i : Fin N => Active D (N+i.val)) C (by simpa [C,heavySet,M,D] using cc)
  have hr : R.card ≤ H := heavy T M v hv
  have hc : C.card ≤ H := by have h := heavy (Function.swap T) (Function.swap M) v hv; rwa [error_transpose] at h
  have usedHalf := RawCount25855.halves N (fun i => 1≤Active D i)
  change used (2*N) D = _ at usedHalf
  have shareHalf := RawCount25855.halves N (fun i => 2≤Active D i)
  change (sharedRaw (2*N) D).card = _ at shareHalf
  have sc := (sharingCosts (2*N) D).1
  obtain ⟨_,_,_,_,_,_,_,balance⟩ := Partition25855.partition ord lv pos
  change ds.length+1=used (2*N) D+k at balance
  change (sharedRaw (2*N) D).card+_ ≤ k at sc
  omega
end Budget25855

namespace NoLive25855
open Private25855 PEqualNP.Represents Skeleton25855 Finset

theorem constantSide {N v : Nat} (T M : Fin N → Fin N → Bool) (hv : 0<v)
    (sep : ∀ i j, i≠j → 17+2*(v-1) ≤ distance (T i) (T j)) (flat : ∀ i j, M i = M j) : N ≤ errors T M / v + 1 := by
  have h := Unread25855.unseen T M ∅ sep (fun i _ j _ => flat i j)
  let B := Budget25855.heavySet T M v
  have hB : B.card ≤ errors T M/v := heavy T M v hv
  have h1 : (univ.filter (fun i : Fin N => 0=0 ∧ i∉B)).card ≤ 1 := by simpa [B,Budget25855.heavySet] using h
  have hr := (RawCount25855.ledger (fun _ : Fin N => 0) B h1).1
  simp only [Nat.reduceLeDiff,filter_false,card_empty,zero_add] at hr
  omega

theorem raw {N v : Nat} (T : Fin N → Fin N → Bool) (r : Ref) (hv : 0<v)
    (sep : ∀ i j, i≠j → 17+2*(v-1) ≤ distance (T i) (T j) ∧ 17+2*(v-1) ≤ distance (Function.swap T i) (Function.swap T j)) :
    let M := fun i j : Fin N => r.run (oneEach i j)
    N ≤ errors T M/v + 1 := by
  intro M
  by_cases lo : r.idx<N
  · have h := constantSide (Function.swap T) (Function.swap M) hv (fun i j ne => (sep i j ne).2) (by
      intro i j; funext z; change r.act _ = r.act _; apply congrArg r.act; apply Bool.eq_iff_iff.mpr
      simp only [hotPin]; have hi := i.isLt; have hj := j.isLt; constructor <;> rintro (h|h) <;> first | exact Or.inl h | omega)
    rwa [error_transpose] at h
  · apply constantSide T M hv (fun i j ne => (sep i j ne).1)
    intro i j; funext z; change r.act _ = r.act _; apply congrArg r.act; apply Bool.eq_iff_iff.mpr
    simp only [hotPin]; have hi := i.isLt; have hj := j.isLt; constructor <;> rintro (h|h) <;> first | exact Or.inr h | omega
end NoLive25855

namespace Charge25855
open Finset
variable {L : Type*} [LinearOrder L]
theorem charge (s : Finset L) (T F : L → L → Bool) (P : L → L → Bool → Bool → Bool) :
    ((s ×ˢ s).filter (fun z => z.1 < z.2 ∧ P z.1 z.2 (F z.1 z.2) (F z.2 z.1) = true)).card ≤
    ((s ×ˢ s).filter (fun z => z.1 < z.2 ∧ P z.1 z.2 (T z.1 z.2) (T z.2 z.1) = true)).card +
    ((s ×ˢ s).filter (fun z => T z.1 z.2 ≠ F z.1 z.2)).card := by
  classical
  let U := s ×ˢ s
  let cf := U.filter (fun z => z.1 < z.2 ∧ P z.1 z.2 (F z.1 z.2) (F z.2 z.1) = true)
  let ct := U.filter (fun z => z.1 < z.2 ∧ P z.1 z.2 (T z.1 z.2) (T z.2 z.1) = true)
  let changed := U.filter (fun z => T z.1 z.2 ≠ F z.1 z.2)
  let pick (z : L × L) := if T z.1 z.2 = F z.1 z.2 then z.swap else z
  have hm (z) (hz : z ∈ cf \ ct) : pick z ∈ changed := by
    obtain ⟨h1,h2⟩ := mem_sdiff.mp hz
    obtain ⟨hu,hl,hp⟩ := mem_filter.mp h1
    have hn : ¬ P z.1 z.2 (T z.1 z.2) (T z.2 z.1) = true := fun h => h2 (mem_filter.mpr ⟨hu,hl,h⟩)
    obtain ⟨ha,hb⟩ := mem_product.mp hu
    by_cases h : T z.1 z.2 = F z.1 z.2
    · have hr : T z.2 z.1 ≠ F z.2 z.1 := fun he => hn (by rwa [h,he])
      exact mem_filter.mpr ⟨by simpa [pick,h,U] using And.intro hb ha,by simpa [pick,h] using hr⟩
    · simpa [pick,h,changed,hu]
  have hin : Set.InjOn pick ↑(cf \ ct) := by
    intro a ha b hb h
    have al := (mem_filter.mp (mem_sdiff.mp ha).1).2.1
    have bl := (mem_filter.mp (mem_sdiff.mp hb).1).2.1
    dsimp [pick] at h; split at h <;> split at h
    · exact congrArg Prod.swap h
    · exact False.elim ((not_lt_of_ge al.le) (by simpa [← h] using bl))
    · exact False.elim ((not_lt_of_ge bl.le) (by simpa [h] using al))
    · exact h
  have hh := card_le_card_of_injOn pick hm hin
  change cf.card ≤ ct.card + changed.card
  have := Finset.card_le_card (show cf ⊆ ct ∪ (cf \ ct) by intro z hz; by_cases h : z ∈ ct <;> simp [h,hz])
  have := Finset.card_union_le ct (cf \ ct)
  omega
end Charge25855

namespace Rectangle25855
open Finset
variable {I : Type*} [DecidableEq I]
theorem rectangle {p : Nat} (row col : Fin p → I) (hr : Function.Injective row) (hc : Function.Injective col)
    (A B : Finset I) (ra : ∀ i, row i ∉ A) (cb : ∀ i, col i ∉ B) (T F : I → I → Bool) (q u : Nat)
    (h : ∀ X Y : Finset I, Disjoint X A → Disjoint Y B → X.card = Y.card → ((X ×ˢ Y).filter (fun z => T z.1 z.2 ≠ F z.1 z.2)).card ≤ q*X.card+u) :
    (univ.filter (fun z : Fin p × Fin p => T (row z.1) (col z.2) ≠ F (row z.1) (col z.2))).card ≤ q*p+u := by
  classical
  let X := univ.image row
  let Y := univ.image col
  have hx : X.card = p := by simp [X,Finset.card_image_of_injective _ hr]
  have hy : Y.card = p := by simp [Y,Finset.card_image_of_injective _ hc]
  have dx : Disjoint X A := by simp [X,Finset.disjoint_left,ra]
  have dy : Disjoint Y B := by simp [Y,Finset.disjoint_left,cb]
  have step := h X Y dx dy (hx.trans hy.symm)
  rw [hx] at step
  apply le_trans _ step
  apply Finset.card_le_card_of_injOn (fun z : Fin p × Fin p => (row z.1,col z.2))
  · intro z hz
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem _ (mem_univ _),mem_image_of_mem _ (mem_univ _)⟩,(mem_filter.mp hz).2⟩
  · intro x hx y hy he
    exact Prod.ext (hr (congrArg Prod.fst he)) (hc (congrArg Prod.snd he))
end Rectangle25855

namespace Arithmetic25855
theorem finish (p n b d A B q a m e u : Nat)
    (labels : 32*n ≤ p+15*b+50+44*d+A+B)
    (conflicts : p^2 ≤ 4*(e+u)+(4+4*q+2*a*m)*p) :
    (32*n-(15*b+54+44*d+A+B+4*q+2*a*m))^2 ≤ 4*(e+u) := by
  let t := 4+4*q+2*a*m
  let s := 32*n-(15*b+54+44*d+A+B+4*q+2*a*m)
  change s^2 ≤ _
  by_cases hs : s = 0
  · simp [hs]
  have h : s+t ≤ p := by dsimp [s,t] at *; omega
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le h
  change p^2 ≤ 4*(e+u)+t*p at conflicts
  rw [hj] at conflicts
  nlinarith [Nat.zero_le (s*t), Nat.zero_le (s*j), Nat.zero_le (j*t), Nat.zero_le (j*j)]
end Arithmetic25855


open Finset Real
open scoped BigOperators
namespace Histogram25855

noncomputable def sign (b : Bool) : ℝ := if b then -1 else 1

private theorem sign_xor (b c : Bool) : sign (xor b c) = sign b * sign c := by
  cases b <;> cases c <;> norm_num [sign]

private theorem squareSign (b : Bool) : sign b * sign b = 1 := by
  cases b <;> norm_num [sign]

private theorem cube_mgf {k : Nat} (w : Fin k → ℝ) :
    (∑ z : Fin k → Bool, exp (∑ l, w l * sign (z l))) ≤
      2^k * exp ((∑ l, w l ^ 2)/2) := by
  calc
    _ = ∏ l, ∑ b : Bool, exp (w l * sign b) := by
      rw [Fintype.prod_sum]; simp only [Real.exp_sum]
    _ ≤ ∏ l, (2 * exp (w l ^ 2 / 2)) := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro l hl
      simp [sign]
      linarith [show (exp (w l) + exp (-w l)) / 2 ≤ exp (w l ^ 2 / 2) by
        simpa only [← Real.cosh_eq] using Real.cosh_le_exp_half_sq (w l)]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [← Real.exp_sum, Finset.sum_div]

private theorem word_inj {k} : Function.Injective
    (fun x : Fin (2 ^ k) => fun l : Fin k => x.val.testBit l.val) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact congrFun h ⟨i,hi⟩
  · have hki : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le hki),
        Nat.testBit_eq_false_of_lt (y.isLt.trans_le hki)]

private theorem subcube_mgf {ι : Type*} [DecidableEq ι] {k : Nat}
    (S : Finset ι) (row : ι → Fin (2^k)) (inj : Set.InjOn row S)
    (w : Fin k → ℝ) :
    (∑ i ∈ S, exp (∑ l, w l * sign ((row i).val.testBit l))) ≤
      2^k * exp ((∑ l, w l ^ 2)/2) := by
  classical
  let word (i : ι) (l : Fin k) := (row i).val.testBit l.val
  have hw : Set.InjOn word S := fun _ h _ h' e => inj h h' (word_inj e)
  calc
    _ = ∑ z ∈ S.image word, exp (∑ l, w l * sign (z l)) := (Finset.sum_image hw).symm
    _ ≤ ∑ z : Fin k → Bool, exp (∑ l, w l * sign (z l)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    _ ≤ _ := cube_mgf w


theorem energy {ι : Type*} [DecidableEq ι] {k : Nat}
    (S : Finset ι) (row : ι → Fin (2^k)) (inj : Set.InjOn row S)
    (flip : ι → Bool) (hS : S.Nonempty) :
    (∑ l : Fin k, (∑ i ∈ S, sign (flip i) * sign ((row i).val.testBit l)) ^ 2) ≤
      2 * (S.card : ℝ)^2 * Real.log (2 * 2^k / S.card) := by
  classical
  let m := (S.card : ℝ)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Finset.card_pos.mpr hS
  let w (l : Fin k) := (∑ i ∈ S, sign (flip i) * sign ((row i).val.testBit l)) / m
  let E := ∑ l, w l ^ 2
  let U (i : ι) := ∑ l, w l * sign ((row i).val.testBit l)
  have hsum : (∑ i ∈ S, sign (flip i) * U i) = m * E := by
    simp only [U, Finset.mul_sum]
    rw [Finset.sum_comm]
    dsimp only [E]; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    calc
      _ = w l * ∑ i ∈ S, sign (flip i) * sign ((row i).val.testBit l) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ = m * w l ^ 2 := by dsimp [w]; field_simp
  have hj : exp E ≤ (1/m) * ∑ i ∈ S, exp (sign (flip i) * U i) := by
    have h := convexOn_exp.map_sum_le (t := S) (p := fun i => sign (flip i) * U i)
      (w := fun _ => (1/m : ℝ)) (by intros; positivity) (by simp; field_simp; rfl)
      (by intros; trivial)
    simp only [smul_eq_mul, ← Finset.mul_sum, hsum] at h
    convert h using 2; field_simp
  have hs : (∑ i ∈ S, exp (sign (flip i) * U i)) ≤
      2 * 2^k * exp (E/2) := by
    calc
      _ ≤ ∑ i ∈ S, (exp (U i) + exp (-U i)) := by
        apply Finset.sum_le_sum; intro i hi
        cases hv : flip i <;> simp [sign] <;> positivity
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := by
        have h₁ := subcube_mgf S row inj w
        have h₂ := subcube_mgf S row inj (fun l => -w l)
        simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at h₂
        change (∑ i ∈ S, exp (U i)) ≤ 2^k * exp (E/2) at h₁
        change (∑ i ∈ S, exp (-U i)) ≤ 2^k * exp (E/2) at h₂
        linarith
  have hexp : exp (E/2) ≤ 2 * 2^k / m := by
    apply (le_of_mul_le_mul_right (a := exp (E/2)) · (Real.exp_pos _))
    rw [← Real.exp_add, show E/2+E/2=E by ring]
    calc
      exp E ≤ _ := hj
      _ ≤ (1/m) * (2 * 2^k * exp (E/2)) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have hlog := (Real.le_log_iff_exp_le (by positivity : 0 < (2:ℝ) * 2^k / m)).mpr hexp
  have hsc : (∑ l : Fin k, (∑ i ∈ S, sign (flip i) * sign ((row i).val.testBit l))^2) = m^2 * E := by
    dsimp only [E]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intros; dsimp only [w]; field_simp
  rw [hsc]; change m ^ 2 * E ≤ 2 * m ^ 2 * log (2 * 2 ^ k / m)
  nlinarith [mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hlog)]

private theorem log_cap {m M : ℝ} {a : Nat} (hm : 0 < m) (h : m ≤ M) (ha : 3 ≤ a) :
    m * log (2 * 2^a * M / m) ≤ a * M := by
  have hM := hm.trans_le h
  have hlog : log 2 * (1 + a) ≤ a := by
    have h₁ := Real.log_two_lt_d9
    have h₂ : (3:ℝ) ≤ a := by exact_mod_cast ha
    nlinarith [mul_nonneg (by linarith : 0 ≤ 0.7 - log 2) (show 0 ≤ (a:ℝ) by positivity)]
  have hml := Real.log_le_sub_one_of_pos (div_pos hM hm)
  have hbound := mul_le_mul_of_nonneg_left hml hm.le
  have hcancel : m * (M/m-1) = M-m := by field_simp
  rw [hcancel] at hbound
  rw [show 2 * 2^a * M / m = (2*2^a) * (M/m) by ring, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have h₃ : 1 ≤ (a:ℝ) := by exact_mod_cast (by omega : 1 ≤ a)
  nlinarith [mul_le_mul_of_nonneg_left hlog hm.le, mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr h₃)]

private theorem gram {p k : Nat} (addr : Fin p → Fin k) (b : Fin p → Fin k → ℝ) :
    (∑ i, ∑ j, b i (addr j) * b j (addr i)) ≤
      ∑ t : Fin k, ∑ l : Fin k, (∑ i : Fin p with addr i = t, b i l)^2 := by
  classical
  let S (t : Fin k) := univ.filter (fun i => addr i = t)
  let V (t l : Fin k) := ∑ i ∈ S t, b i l
  have group (f : Fin p → ℝ) : ∑ i, f i = ∑ t, ∑ i ∈ S t, f i :=
    (Finset.sum_fiberwise univ addr f).symm
  have heq : (∑ i, ∑ j, b i (addr j) * b j (addr i)) = ∑ t, ∑ l, V t l * V l t := by
    rw [group]; apply sum_congr rfl; intro t _
    calc
      _ = ∑ i ∈ S t, ∑ l, ∑ j ∈ S l, b i l * b j t := by
        apply sum_congr rfl; intro i hi
        rw [group]; apply sum_congr rfl; intro l _
        apply sum_congr rfl; intro j hj
        rw [(mem_filter.mp hi).2, (mem_filter.mp hj).2]
      _ = _ := by
        rw [sum_comm]; apply sum_congr rfl; intro l _
        simp only [V, Finset.sum_mul, Finset.mul_sum]
        exact sum_comm
  rw [heq]
  change _ ≤ ∑ t, ∑ l, V t l ^ 2
  have hh : (∑ t, ∑ l, 2 * (V t l * V l t)) ≤ ∑ t, ∑ l, (V t l ^ 2 + V l t ^ 2) :=
    sum_le_sum fun t _ => sum_le_sum fun l _ => by nlinarith [sq_nonneg (V t l - V l t)]
  have sw : (∑ t, ∑ l, V l t ^ 2) = ∑ t, ∑ l, V t l ^ 2 := sum_comm
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, sw] at hh
  linarith

private theorem bias {p k a : Nat} (ha : 3 ≤ a) (row : Fin p → Fin (2^k))
    (hr : Function.Injective row) (flip : Fin p → Bool) (addr : Fin p → Fin k)
    (M : Nat) (hM : 2^a * M = 2^k)
    (cap : ∀ t, (univ.filter (fun i => addr i = t)).card ≤ M) :
    let b (i : Fin p) (l : Fin k) := sign (flip i) * sign ((row i).val.testBit l)
    (∑ i, ∑ j, b i (addr j) * b j (addr i)) ≤ 2 * a * M * p := by
  classical
  intro b
  let S (t : Fin k) := univ.filter (fun i => addr i = t)
  have factor : (2:ℝ)^a * M = 2^k := by exact_mod_cast hM
  have whole : (∑ t, ((S t).card : ℝ)) = p := by
    simpa [S] using (Finset.sum_fiberwise (univ : Finset (Fin p)) addr (fun _ => (1:ℝ)))
  refine (gram addr b).trans ?_
  calc
    _ ≤ ∑ t, (2 * a * M * ((S t).card : ℝ)) := by
      apply sum_le_sum; intro t _
      by_cases hs : (S t).Nonempty
      · have he := energy (S t) row hr.injOn flip hs
        have hm : (0:ℝ) < (S t).card := by exact_mod_cast Finset.card_pos.mpr hs
        have hc : ((S t).card : ℝ) ≤ M := by exact_mod_cast cap t
        have hl := log_cap hm hc ha
        rw [mul_assoc 2 ((2:ℝ)^a) (M:ℝ), factor] at hl
        exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hl hm.le])
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hs
        change (∑ l, (∑ i ∈ S t, b i l)^2) ≤ _
        simp [hz]
    _ = _ := by rw [← Finset.mul_sum, whole]

private theorem residue_cap {p k a : Nat} (hk : 2^a ≤ k) (col : Fin p → Fin (2^k))
    (hc : Function.Injective col) (j : Fin k) :
    (univ.filter (fun i => (col i).val % 2^a = j.val)).card ≤ 2^k / 2^a := by
  let r := 2^a
  have hr : 0 < r := by positivity
  have hak : a ≤ k := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans hk
  have hd : r ∣ 2^k := pow_dvd_pow 2 hak
  have prod := Nat.div_mul_cancel hd
  have h := Finset.card_le_card_of_injOn (s := univ.filter (fun i => (col i).val % r = j.val))
    (t := range (2^k/r)) (fun i => (col i).val/r) (by
      intro i _; apply mem_range.mpr; apply (Nat.div_lt_iff_lt_mul hr).mpr
      rw [prod]; exact (col i).isLt) (by
      intro i hi l hl eq; apply hc; apply Fin.ext
      have h₁ := (mem_filter.mp hi).2; have h₂ := (mem_filter.mp hl).2
      have e₁ := Nat.div_add_mod (col i).val r; have e₂ := Nat.div_add_mod (col l).val r
      change (col i).val / r = (col l).val / r at eq
      rw [h₁] at e₁; rw [h₂, ← eq] at e₂; omega)
  simpa [r] using h

private theorem orientation_sum {p : Nat} (F : Fin p → Fin p → Bool) :
    (∑ i, ∑ j, sign (F i j) * sign (F j i)) =
      (p:ℝ)^2 - 4 * ((univ.filter (fun z : Fin p × Fin p =>
         z.1 < z.2 ∧ F z.1 z.2 ≠ F z.2 z.1)).card : ℝ) := by
  classical
  let d (i j : Fin p) : ℝ := if i < j ∧ F i j ≠ F j i then 1 else 0
  have cell (i j : Fin p) : sign (F i j) * sign (F j i) = 1 - 2 * d i j - 2 * d j i := by
    rcases lt_trichotomy i j with h|rfl|h
    · have hn := not_lt_of_ge h.le
      cases h₁ : F i j <;> cases h₂ : F j i <;> norm_num [sign,d,h,hn,h₁,h₂]
    · simp [d,squareSign]
    · have hn := not_lt_of_ge h.le
      cases h₁ : F i j <;> cases h₂ : F j i <;> norm_num [sign,d,h,hn,h₁,h₂]
  have sum_d : (∑ i, ∑ j, d i j) =
      ((univ.filter (fun z : Fin p × Fin p => z.1 < z.2 ∧ F z.1 z.2 ≠ F z.2 z.1)).card : ℝ) := by
    rw [← Fintype.sum_prod_type' (fun i j => d i j)]; simp [d]
  have sw : (∑ i, ∑ j, d j i) = ∑ i, ∑ j, d i j := sum_comm
  simp only [cell, Finset.sum_sub_distrib, ← Finset.mul_sum, sw, sum_d]
  simp; ring


theorem orientation {k a p : Nat} (ha : 0 < a) (hk : 2^a ≤ k)
    (row col : Fin p → Fin (2^k)) (hr : Function.Injective row) (hc : Function.Injective col)
    (f g : Fin (2^k) → Bool) :
    let F (i j : Fin p) := xor ((row i).val.testBit ((col j).val % 2^a))
      (xor (f (row i)) (g (col j)))
    p^2 ≤ 4 * (univ.filter (fun z : Fin p × Fin p => z.1 < z.2 ∧ F z.1 z.2 ≠ F z.2 z.1)).card
          + 2*a*(2^k / 2^a)*p := by
  classical
  intro F
  let M := 2^k / 2^a
  have hak : a ≤ k := Nat.lt_two_pow_self.le.trans hk
  have hM : 2^a * M = 2^k := Nat.mul_div_cancel' (pow_dvd_pow 2 hak)
  by_cases hbig : 3 ≤ a
  · let addr (i : Fin p) : Fin k := ⟨(col i).val % 2^a, (Nat.mod_lt _ (by positivity)).trans_le hk⟩
    let flip (i : Fin p) := xor (f (row i)) (g (col i))
    have cap (j : Fin k) : (univ.filter (fun i => addr i = j)).card ≤ M := by
      simpa [addr, Fin.ext_iff, M] using residue_cap hk col hc j
    have e := bias hbig row hr flip addr M hM cap
    let b (i : Fin p) (l : Fin k) := sign (flip i) * sign ((row i).val.testBit l)
    have hcell (i j : Fin p) : b i (addr j) * b j (addr i) = sign (F i j) * sign (F j i) := by
      simp only [b, flip, addr, F, sign_xor]; ring
    change (∑ i, ∑ j, b i (addr j) * b j (addr i)) ≤ _ at e
    simp_rw [hcell] at e
    rw [orientation_sum] at e
    exact_mod_cast (sub_le_iff_le_add'.mp e)
  · have hp : p ≤ 2^k := by simpa using Fintype.card_le_of_injective row hr
    have h : 2^a ≤ 2*a := by interval_cases a <;> decide
    have hp' : p ≤ 2*a*M := hp.trans (hM ▸ Nat.mul_le_mul_right M h)
    exact (show p^2 ≤ 2*a*M*p by nlinarith [Nat.mul_le_mul_right p hp']).trans (Nat.le_add_left _ _)

end Histogram25855

namespace FromMatching25855
open Finset
theorem finish {k a p : Nat} (ha : 0<a) (hk : 2^a ≤ k) (row col : Fin p → Fin (2^k)) (hr : Function.Injective row) (hc : Function.Injective col)
    (T : Fin (2^k) → Fin (2^k) → Bool) (f g : Fin (2^k) → Bool) (A B : Finset (Fin (2^k))) (q u e d b : Nat)
    (ra : ∀ i, row i ∉ A) (cb : ∀ i, col i ∉ B)
    (labels : 32*(2^k) ≤ p+15*b+50+44*d+A.card+B.card)
    (bad : (univ.filter (fun z : Fin p × Fin p => z.1 < z.2 ∧ T (row z.1) (col z.2) ≠ T (row z.2) (col z.1))).card ≤ e+p) :
    let F := fun x y : Fin (2^k) => xor (x.val.testBit (y.val % 2^a)) (xor (f x) (g y))
    (∀ X Y : Finset (Fin (2^k)), Disjoint X A → Disjoint Y B → X.card = Y.card → ((X ×ˢ Y).filter (fun z => T z.1 z.2 ≠ F z.1 z.2)).card ≤ q*X.card+u) →
    (32*(2^k)-(15*b+54+44*d+A.card+B.card+4*q+2*a*(2^k/2^a)))^2 ≤ 4*(e+u) := by
  classical
  intro F rect
  have orient := Histogram25855.orientation ha hk row col hr hc f g
  have cells := Rectangle25855.rectangle row col hr hc A B ra cb T F q u rect
  have charge := Charge25855.charge (univ : Finset (Fin p)) (fun i j => T (row i) (col j)) (fun i j => F (row i) (col j)) (fun _ _ x y => decide (x ≠ y))
  simp only [univ_product_univ,decide_eq_true_eq] at charge
  apply Arithmetic25855.finish p _ _ _ _ _ _ _ _ _ _ labels
  dsimp only at orient
  change p^2 ≤ 4 * (univ.filter (fun z : Fin p × Fin p => z.1 < z.2 ∧ F (row z.1) (col z.2) ≠ F (row z.2) (col z.1))).card + 2*a*(2^k/2^a)*p at orient
  nlinarith
end FromMatching25855

namespace Delete25855
open Finset
variable {I J L : Type*} [DecidableEq I] [DecidableEq J] [DecidableEq L]
theorem loss (s : Finset L) (row : L → I) (col : L → J) (hr : Function.Injective row) (hc : Function.Injective col) (A : Finset I) (B : Finset J) :
    s.card ≤ (s.filter (fun i => row i ∉ A ∧ col i ∉ B)).card + A.card + B.card := by
  classical
  let keep := s.filter (fun i => row i ∉ A ∧ col i ∉ B)
  let x := s.filter (fun i => row i ∈ A)
  let y := s.filter (fun i => col i ∈ B)
  have sub : s ⊆ keep ∪ x ∪ y := by intro i hi; by_cases ha : row i ∈ A <;> by_cases hb : col i ∈ B <;> simp [keep,x,y,hi,ha,hb]
  have hx : x.card ≤ A.card := Finset.card_le_card_of_injOn row (by intro i hi; exact (Finset.mem_filter.mp hi).2) hr.injOn
  have hy : y.card ≤ B.card := Finset.card_le_card_of_injOn col (by intro i hi; exact (Finset.mem_filter.mp hi).2) hc.injOn
  have h := Finset.card_le_card sub
  have h' := Finset.card_union_le (keep ∪ x) y
  have h'' := Finset.card_union_le keep x
  change s.card ≤ keep.card + A.card + B.card
  omega
end Delete25855

namespace Hereditary25855
open Finset Private25855

theorem finish {k a p : Nat} (ha : 0<a) (hk : 2^a ≤ k) (row col : Fin p → Fin (2^k)) (hr : Function.Injective row) (hc : Function.Injective col)
    (T M : Fin (2^k) → Fin (2^k) → Bool) (f g : Fin (2^k) → Bool) (A B : Finset (Fin (2^k))) (q u d b : Nat)
    (labels : 32*2^k ≤ p+15*b+50+44*d)
    (bad : ∀ {m : Nat} (j : Fin m ↪o Fin p), (univ.filter (fun z : Fin m × Fin m => z.1 < z.2 ∧ M (row (j z.1)) (col (j z.2)) ≠ M (row (j z.2)) (col (j z.1)))).card ≤ m) :
    let F := fun x y : Fin (2^k) => xor (x.val.testBit (y.val % 2^a)) (xor (f x) (g y))
    (∀ X Y : Finset (Fin (2^k)), Disjoint X A → Disjoint Y B → X.card = Y.card → ((X ×ˢ Y).filter (fun z => T z.1 z.2 ≠ F z.1 z.2)).card ≤ q*X.card+u) →
    (32*2^k-(15*b+54+44*d+A.card+B.card+4*q+2*a*(2^k/2^a)))^2 ≤ 4*(errors T M+u) := by
  classical
  intro F rect
  let s := univ.filter (fun i => row i ∉ A ∧ col i ∉ B)
  let j := s.orderEmbOfFin rfl
  have ja (i : Fin s.card) : row (j i) ∉ A ∧ col (j i) ∉ B := (mem_filter.mp (s.orderEmbOfFin_mem rfl i)).2
  have loss := Delete25855.loss univ row col hr hc A B
  change (univ : Finset (Fin p)).card ≤ s.card + A.card + B.card at loss
  simp only [card_univ,Fintype.card_fin] at loss
  apply FromMatching25855.finish ha hk (row ∘ j) (col ∘ j) (hr.comp j.injective) (hc.comp j.injective) T f g A B q u _ d b (fun i => (ja i).1) (fun i => (ja i).2) (by omega) _ rect
  have c := Charge25855.charge (univ : Finset (Fin s.card)) (fun i k => M (row (j i)) (col (j k))) (fun i k => T (row (j i)) (col (j k))) (fun _ _ x y => decide (x ≠ y))
  simp only [univ_product_univ,decide_eq_true_eq] at c
  have err : (univ.filter (fun z : Fin s.card × Fin s.card => M (row (j z.1)) (col (j z.2)) ≠ T (row (j z.1)) (col (j z.2)))).card ≤ errors T M := by
    apply card_le_card_of_injOn (fun z : Fin s.card × Fin s.card => (row (j z.1),col (j z.2)))
    · intro z hz; exact mem_filter.mpr ⟨mem_univ _,Ne.symm (mem_filter.mp hz).2⟩
    · intro x hx y hy he; exact Prod.ext (j.injective (hr (congrArg Prod.fst he))) (j.injective (hc (congrArg Prod.snd he)))
  exact c.trans (by have := bad j; omega)
end Hereditary25855

namespace PhysicalFinish25855
open Skeleton25855 Private25855 PEqualNP.CircuitLowerBounds PEqualNP.Represents Finset

theorem one {N : Nat} (ds : List Node) (r : Ref) (i j : Fin N) : Piece.One (TreeSemantic25855.table ds r) i j = r.run (ds.foldl Skeleton25855.step (oneEach i j)) := by simp [Piece.One,TreeSemantic25855.table,TreeSemantic25855.val,TreeSemantic25855.input,oneEach,Ref.run]

def Match {N : Nat} (M : Fin N → Fin N → Bool) (b H : Nat) := ∃ p, ∃ row col : Fin p → Fin N, Function.Injective row ∧ Function.Injective col ∧ 32*N ≤ p+15*b+50+44*H ∧ ∀ {m : Nat} (j : Fin m ↪o Fin p), (univ.filter (fun z : Fin m × Fin m => z.1 < z.2 ∧ M (row (j z.1)) (col (j z.2)) ≠ M (row (j z.2)) (col (j z.1)))).card ≤ m

theorem finish {k a v : Nat} (ha : 0<a) (hk : 2^a≤k) (T : Fin (2^k) → Fin (2^k) → Bool) (f g : Fin (2^k) → Bool) (A B : Finset (Fin (2^k))) (q u : Nat) (hv : 0<v)
    (sep : ∀ i j, i≠j → 17+2*(v-1) ≤ distance (T i) (T j) ∧ 17+2*(v-1) ≤ distance (Function.swap T i) (Function.swap T j))
    (rect : ∀ X Y : Finset (Fin (2^k)), Disjoint X A → Disjoint Y B → X.card=Y.card → ((X ×ˢ Y).filter (fun z => T z.1 z.2 ≠ xor (z.1.val.testBit (z.2.val % 2^a)) (xor (f z.1) (g z.2)))).card ≤ q*X.card+u)
    (C : Circuit) (fan : ∀ g∈C.gates,g.inputs.length≤2)
    (nonempty : ∀ (ds : List Node) (r : Ref), ds≠[] → ok (2*2^k) ds → Prune25855.Live (2*2^k) ds r → r.idx < 2*2^k+ds.length →
      let M := Piece.One (TreeSemantic25855.table ds r : Table (2^k))
      Match M ds.length (errors T M/v)) :
    let M := fun i j : Fin (2^k) => C.eval (oneEach i j)
    let e := errors T M
    let b := C.gates.countP (fun g => g.inputs.length == 2)
    (32*2^k-(15*b+54+44*(e/v)+A.card+B.card+4*q+2*a*(2^k/2^a)))^2 ≤ 4*(e+u) := by
  intro M e b
  obtain ⟨all,out,ho,hs,hout,sem⟩ := Physical25855.physicalOutput (2*2^k) (by positivity) C fan
  obtain ⟨ds,r,hord,hle,hr,hv',he⟩ := Prune25855.prune all out ho hout
  have size : ds.length ≤ b := hle.trans hs.le
  have eq (i j : Fin (2^k)) : M i j = r.run (ds.foldl Skeleton25855.step (oneEach i j)) := by
    have len : (oneEach i j).length=2*2^k := by simp [oneEach,two_mul]
    exact (sem _ len).trans (he _ len)
  by_cases hds : ds=[]
  · subst ds; have eq' : M = fun i j => r.run (oneEach i j) := funext fun i => funext fun j => eq i j
    have small := NoLive25855.raw T r hv sep
    change 2^k ≤ errors T (fun i j => r.run (oneEach i j))/v+1 at small
    rw [←eq'] at small; change 2^k ≤ e/v+1 at small
    have bound : 32*2^k ≤ 15*b+54+44*(e/v)+A.card+B.card+4*q+2*a*(2^k/2^a) := by omega
    simp [Nat.sub_eq_zero_of_le bound]
  · have eq' : Piece.One (TreeSemantic25855.table ds r : Table (2^k)) = M := funext fun i => funext fun j => (one ds r i j).trans (eq i j).symm
    have m := nonempty ds r hds hord hv' hr; dsimp only at m; rw [eq'] at m
    obtain ⟨p,x,y,hx,hy,count,conf⟩ := m
    exact Hereditary25855.finish ha hk x y hx hy T M f g A B q u (e/v) b (by change 32*2^k ≤ p+15*ds.length+50+44*(e/v) at count; omega) conf rect
end PhysicalFinish25855

namespace Owner25855
open Finset Private25855 PhysicalFinish25855

 theorem inherited {N b H p m : ℕ} (M : Fin N → Fin N → Bool) (row col : Fin p → Fin N)
    (ir : Function.Injective row) (ic : Function.Injective col) (ledger : 32*N≤p+15*b+50+44*H)
    (owner : Fin p → Fin m) (fib : ∀ i, (univ.filter fun j => owner j=owner i).card ≤3)
    (symm : ∀ i j, owner i≠owner j → M (row i) (col j)=M (row j) (col i)) : Match M b H := by
  classical
  refine ⟨p,row,col,ir,ic,ledger,?_⟩
  intro s emb
  apply conflicts (owner ∘ emb) (fun i j => M (row (emb i)) (col (emb j))) _ (fun i j => symm _ _)
  intro i
  apply le_trans _ (fib (emb i))
  apply card_le_card_of_injOn emb
  · intro j hj; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2⟩
  · exact emb.injective.injOn

theorem finish {N m b H K : ℕ} (F : Table N) (t : Fin m → Piece N) (pure : Fin m → Bool)
    (reg : ∀ z, Piece.Regular F (t z))
    (dr : ∀ z w, z≠w → Disjoint (t z).rows (t w).rows)
    (dc : ∀ z w, z≠w → Disjoint (t z).cols (t w).cols)
    (flat : ∀ z, pure z=true → ∀ X Y, Piece.eval X Y false (t z)=Piece.eval X Y true (t z))
    (sr : ∀ z w i, i∈(t z).rows → ∀ j∈(t w).rows, i≠j → 17≤distance (Piece.One F i) (Piece.One F j))
    (sc : ∀ z w i, i∈(t z).cols → ∀ j∈(t w).cols, i≠j →
      17≤distance (Function.swap (Piece.One F) i) (Function.swap (Piece.One F) j))
    (scarcity : K+2*N≤b+3+2*H)
    (coverage : 2*N ≤ (univ.biUnion fun z => (t z).rows).card + (univ.biUnion fun z => (t z).cols).card+K+2*H+2)
    (cost : (univ.filter fun i => pure i=true).card+3*(univ.filter fun i => pure i=false).card≤14*K+1+12*H) :
    Match (Piece.One F) b H := by
  obtain ⟨p,x,y,hx,hy,count,own,cap,agree⟩ := Piece.matching F t pure reg dr dc flat sr sc scarcity coverage cost
  exact inherited _ _ _ hx hy count own cap agree

end Owner25855

namespace Posted25855
open Skeleton25855 Private25855

theorem finalStep (nonempty : ∀ (N v : Nat) (hv : 0<v) (T : Fin N → Fin N → Bool), (∀ i j, i≠j → 17+2*(v-1) ≤ distance (T i) (T j) ∧ 17+2*(v-1) ≤ distance (Function.swap T i) (Function.swap T j)) → ∀ (ds : List Node) (r : Ref), ds≠[] → ok (2*N) ds → Prune25855.Live (2*N) ds r → r.idx < 2*N+ds.length → let M := Piece.One (TreeSemantic25855.table ds r : Table N); PhysicalFinish25855.Match M ds.length (errors T M/v)) : ∀ k a : ℕ, (0 < a ∧ 2^a ≤ k) →
  let N := 2^k
  let r := 2^a
  let I := Fin N
  ∀ (T : I → I → Bool) (f g : I → Bool) (A B : Finset I) (q u v : ℕ),
    let F := fun x y : I => xor (x.val.testBit (y.val % r)) (xor (f x) (g y))
    0 < v →
    (∀ i j : I, i ≠ j →
      17+2*(v-1) ≤ (Finset.univ.filter (fun z : I => T i z ≠ T j z)).card ∧
      17+2*(v-1) ≤ (Finset.univ.filter (fun z : I => T z i ≠ T z j)).card) →
    (∀ X Y : Finset I, Disjoint X A → Disjoint Y B → X.card = Y.card →
      ((X ×ˢ Y).filter (fun z => T z.1 z.2 ≠ F z.1 z.2)).card ≤ q*X.card+u) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) →
      let e := (Finset.univ.filter (fun z : I × I =>
        C.eval (PEqualNP.Represents.oneEach z.1 z.2) ≠ T z.1 z.2)).card
      let b := C.gates.countP (fun gate => gate.inputs.length == 2)
      (32*N-(15*b+54+44*(e/v)+A.card+B.card+4*q+2*a*(N/r)))^2 ≤ 4*(e+u) := by
  intro k a h; dsimp only; intro T f g A B q u v hv sep rect C fan
  have h' := PhysicalFinish25855.finish h.1 h.2 T f g A B q u hv sep rect C fan (nonempty _ _ hv T sep)
  dsimp only at h'
  simpa only [errors,ne_comm (a := T _ _)] using h'
end Posted25855

namespace Complete25855
open Private25855 Skeleton25855 CutLib25855 Finset

theorem nonempty (N v : Nat) (hv : 0<v) (T : Fin N → Fin N → Bool) (sep : ∀ i j, i≠j → 17+2*(v-1) ≤ distance (T i) (T j) ∧ 17+2*(v-1) ≤ distance (Function.swap T i) (Function.swap T j)) (ds : List Node) (r : Ref) (pos : ds≠[]) (ord : ok (2*N) ds) (lv : Prune25855.Live (2*N) ds r) (hi : r.idx<2*N+ds.length) :
    let M := Piece.One (TreeSemantic25855.table ds r : Table N)
    PhysicalFinish25855.Match M ds.length (errors T M/v) := by
  classical
  intro M
  let O := Shape25855.shape ds r.idx
  let R := Budget25855.heavySet T M v
  let C := Budget25855.heavySet (Function.swap T) (Function.swap M) v
  let d := errors T M/v
  have eqM : (fun i j : Fin N => r.run (ds.foldl Skeleton25855.step (PEqualNP.Represents.oneEach i j))) = M := funext fun i => funext fun j => (PhysicalFinish25855.one ds r i j).symm
  have budget := Budget25855.ledger pos ord lv hv T sep
  dsimp only at budget; rw [eqM] at budget
  change surplus (2*N) O + 2*N ≤ ds.length+3+2*d ∧ 2*N ≤ (univ.filter (fun i : Fin N => Active O i.val=1 ∧ i∉R)).card + (univ.filter (fun i : Fin N => Active O (N+i.val)=1 ∧ i∉C)).card + surplus (2*N) O + 2*d+2 at budget
  obtain ⟨L,nd,raw,once,sz,memR,memC⟩ := Family25855.markers (Active O) R C
  obtain ⟨P,Q,cost,dis,cov,pr,ch,bal⟩ := Mark25855.partition nd raw once ord lv pos
  have lo : 2*N≤r.idx := by rw [Prune25855.last_output lv pos]; omega
  obtain ⟨m,t,pure,reg,dr,dc,flat,rows,cols,slots⟩ := Family25855.assemble L ord raw lo hi P Q dis cov pr ch
  have rr : (univ.biUnion fun z => (t z).rows) = univ.filter (fun i : Fin N => Active O i.val=1 ∧ i∉R) := by
    rw [rows]; ext i; simp only [mem_filter,mem_univ,true_and]; by_cases h : Active O i.val=1
    · simp only [show Active (Shape25855.shape ds r.idx) i.val=1 from h,h,true_and,memR i h]
    · simp [O] at h; simp [O,h]
  have cc : (univ.biUnion fun z => (t z).cols) = univ.filter (fun i : Fin N => Active O (N+i.val)=1 ∧ i∉C) := by
    rw [cols]; ext i; simp only [mem_filter,mem_univ,true_and]; by_cases h : Active O (N+i.val)=1
    · simp only [show Active (Shape25855.shape ds r.idx) (N+i.val)=1 from h,h,true_and,memC i h]
    · simp [O] at h; simp [O,h]
  have lightR (z) (i : Fin N) (h : i∈(t z).rows) : distance (T i) (M i)<v := by
    have h' : i∈univ.biUnion (fun z => (t z).rows) := mem_biUnion.mpr ⟨z,mem_univ _,h⟩; rw [rr] at h'; have := (mem_filter.mp h').2.2; simpa [R,Budget25855.heavySet] using this
  have lightC (z) (i : Fin N) (h : i∈(t z).cols) : distance (Function.swap T i) (Function.swap M i)<v := by
    have h' : i∈univ.biUnion (fun z => (t z).cols) := mem_biUnion.mpr ⟨z,mem_univ _,h⟩; rw [cc] at h'; have := (mem_filter.mp h').2.2; simpa [C,Budget25855.heavySet] using this
  apply Owner25855.finish (K:=surplus (2*N) O) _ t pure reg dr dc flat
  · intro z w i hi j hj ne; exact good_distance T M (sep i j ne).1 (lightR z i hi) (lightR w j hj)
  · intro z w i hi j hj ne; exact good_distance (Function.swap T) (Function.swap M) (sep i j ne).2 (lightC z i hi) (lightC w j hj)
  · exact budget.1
  · rw [rr,cc]; exact budget.2
  · rw [slots]; have hr : R.card≤d := heavy T M v hv
    have hc : C.card≤d := by have h := heavy (Function.swap T) (Function.swap M) v hv; rwa [error_transpose] at h
    obtain ⟨_,_,_,_,_,_,_,orig⟩ := Partition25855.partition ord lv pos
    change ds.length+1=used (2*N) O+surplus (2*N) O at orig
    change ds.length+1=used (2*N) O+surplus (2*N) (Mark25855.shape (2*N) L ds r.idx) at bal
    change 13*_+1+6*L.length ≥ P.length+3*Q.length at cost
    change P.length+3*Q.length ≤ 14*surplus (2*N) O+1+12*d
    omega
end Complete25855

end PEqualNP.Outside.L_meta_25855_aux
theorem PEqualNP.Outside.L_meta_25855 : ∀ k a : ℕ, (0 < a ∧ 2^a ≤ k) →
  let N := 2^k
  let r := 2^a
  let I := Fin N
  ∀ (T : I → I → Bool) (f g : I → Bool) (A B : Finset I) (q u v : ℕ),
    let F := fun x y : I => xor (x.val.testBit (y.val % r)) (xor (f x) (g y))
    0 < v →
    (∀ i j : I, i ≠ j →
      17+2*(v-1) ≤ (Finset.univ.filter (fun z : I => T i z ≠ T j z)).card ∧
      17+2*(v-1) ≤ (Finset.univ.filter (fun z : I => T z i ≠ T z j)).card) →
    (∀ X Y : Finset I, Disjoint X A → Disjoint Y B → X.card = Y.card →
      ((X ×ˢ Y).filter (fun z => T z.1 z.2 ≠ F z.1 z.2)).card ≤ q*X.card+u) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) →
      let e := (Finset.univ.filter (fun z : I × I =>
        C.eval (PEqualNP.Represents.oneEach z.1 z.2) ≠ T z.1 z.2)).card
      let b := C.gates.countP (fun gate => gate.inputs.length == 2)
      (32*N-(15*b+54+44*(e/v)+A.card+B.card+4*q+2*a*(N/r)))^2 ≤ 4*(e+u) := PEqualNP.Outside.L_meta_25855_aux.Posted25855.finalStep PEqualNP.Outside.L_meta_25855_aux.Complete25855.nonempty

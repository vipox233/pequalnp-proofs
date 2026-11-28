import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1435_aux.Wire
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def input (r : ℕ) (Y : Finset ℕ) := List.ofFn (fun j : Fin r => decide (j.val∈Y)) ++ [false,true]
def Valid (r : ℕ) (D : Circuit) := FanInTwo D ∧ NestedCover.ReadsBack (r+2) D ∧ D.output<r+2+D.size
noncomputable def truth (P : Prop) := @decide P (Classical.propDecidable P)
theorem normTruth (P : Prop) (d : Decidable P) : @decide P d = truth P := by
  unfold truth
  congr 1
end PEqualNP.Outside.L_lib_1435_aux.Wire

namespace PEqualNP.Outside.L_lib_1435_aux.Drivers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (w : List Bool) := gs.foldl
  (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

def tick (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def code : List Gate → List Bool → List Bool
  | [], _ => []
  | g::gs, w =>
    let a := tick w g
    match g.op with
    | .not => (g.op.eval (g.inputs.map fun i => w.getD i false)) :: code gs a
    | _ => code gs a

def mark (g : Gate) : Bool := match g.op with | .not => true | _ => false

theorem code_len (gs : List Gate) (w : List Bool) :
    (code gs w).length = (gs.filter mark).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [code,h,mark,List.filter_cons,ih]

def ordered (x y : List Bool) :=
  x.length=y.length ∧ ∀ i, x.getD i false=true → y.getD i false=true

theorem extend_order {x y : List Bool} (w : ordered x y) {a b : Bool}
    (ab : a=true → b=true) : ordered (x++[a]) (y++[b]) := by
  refine ⟨by simp [w.1],?_⟩
  intro i
  by_cases before : i < x.length
  · rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ (w.1 ▸ before)]
    exact w.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by rw [←w.1]; omega),←w.1]
    cases i-x.length <;> simpa using ab <;> simp

theorem output_order {gs : List Gate}
    (ops : ∀ g∈gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {x y : List Bool} (w : ordered x y) (same : code gs x=code gs y) :
    ordered (run gs x) (run gs y) := by
  induction gs generalizing x y with
  | nil => exact w
  | cons g gs ih =>
    have rest (a) (ha : a∈gs) := ops a (List.mem_cons_of_mem _ ha)
    change ordered (run gs (tick x g)) (run gs (tick y g))
    have casesG := ops g (List.mem_cons_self ..)
    rcases casesG with h|h|h
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
      intro all z i hi ei
      subst z
      exact w.2 i (all _ _ hi rfl)
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.any_eq_true,List.mem_map]
      rintro ⟨z,⟨i,hi,rfl⟩,yes⟩
      exact ⟨_,⟨i,hi,rfl⟩,w.2 i yes⟩
    · simp only [code,h,List.cons.injEq] at same
      apply ih rest (extend_order w ?_) same.2
      rw [h]
      exact fun e => same.1.symm.trans e

theorem input_order {n : Nat} {x y : Fin n → Bool} (xy : ∀ i, x i=true → y i=true) :
    ordered (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i<n
  · rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using xy ⟨i,h⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp
def driverNumber : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 2^bs.length) + driverNumber bs

theorem driver_bound (l : List Bool) : driverNumber l < 2^l.length := by
  induction l with
  | nil => decide
  | cons b bs ih => cases b <;> simp [driverNumber,pow_succ] <;> omega

theorem driver_injective {a b : List Bool} (len : a.length=b.length)
    (num : driverNumber a=driverNumber b) : a=b := by
  induction a generalizing b with
  | nil => simpa using len.symm
  | cons x xs ih =>
    cases b with
    | nil => simp at len
    | cons y ys =>
      have sz : xs.length=ys.length := by simpa using len
      have h₁ := driver_bound xs
      have h₂ := driver_bound ys
      rw [sz] at h₁
      cases x <;> cases y <;> simp [driverNumber,sz] at num ⊢ <;> first | exact ih sz num | omega

theorem driver_mono (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : ordered a b) :
    driverNumber (code gs a) ≤ driverNumber (code gs b) := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have tailops := fun h (hh : h∈gs) => ops h (by simp [hh])
    have oneops : ∀ u ∈ [g], u.op=.and ∨ u.op=.or ∨ u.op=.not := by
      simpa using ops g (by simp)
    have growth (same : code [g] a=code [g] b) : ordered (tick a g) (tick b g) :=
      output_order oneops ab same
    rcases ops g (by simp) with eq|eq|eq
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · let out (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have anti : out b=true → out a=true := by
        cases inp : g.inputs with
        | nil => simp [out,eq,inp,GateOp.eval]
        | cons i more =>
          simp only [out,eq,inp,GateOp.eval,List.map_cons,List.headD_cons,Bool.not_eq_true']
          intro bz
          cases az : a.getD i false
          · rfl
          · have := ab.2 i az
            simp_all
      have len : (code gs (tick a g)).length=(code gs (tick b g)).length := by simp [code_len]
      change driverNumber (code (g::gs) a) ≤ driverNumber (code (g::gs) b)
      simp only [code,eq]
      rw [←eq]
      change driverNumber (out a :: code gs (tick a g)) ≤ driverNumber (out b :: code gs (tick b g))
      by_cases same : out a=out b
      · have next : ordered (tick a g) (tick b g) := extend_order ab (by change out a=true → out b=true; rw [same]; exact id)
        simpa only [driverNumber,same,len,Nat.add_le_add_iff_left] using
          Nat.add_le_add_left (ih tailops next) (if out b then 0 else 2^(code gs (tick b g)).length)
      · have zero : out b=false := by cases hb : out b <;> simp_all
        have one : out a=true := by cases ha : out a <;> simp_all
        have bound := driver_bound (code gs (tick a g))
        rw [len] at bound
        simp only [driverNumber,one,zero,Bool.false_eq_true,if_false,if_true,Nat.zero_add]
        omega

theorem mark_count (C : Circuit) :
    (C.gates.filter mark).length = PEqualNP.NotBracket.notCount C := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases eq : g.op <;> simp [mark,eq]

theorem ordered_refl (x : List Bool) : ordered x x := ⟨rfl, fun _ h => h⟩

theorem ordered_append {a b c d : List Bool} (h1 : ordered a b) (h2 : ordered c d) :
    ordered (a++c) (b++d) := by
  refine ⟨by simp [h1.1,h2.1],?_⟩
  intro i
  by_cases h : i < a.length
  · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (h1.1 ▸ h)]
    exact h1.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by rw [←h1.1]; omega),←h1.1]
    exact h2.2 _

theorem ordered_ofFn {r : Nat} {f g : Fin r → Bool} (fg : ∀ j, f j = true → g j = true) :
    ordered (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i < r
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using fg ⟨i,h⟩
  · simp [List.getD_eq_getElem?_getD,h]

theorem dn_top (l : List Bool) (a : Nat) (h : driverNumber l < 2^a) :
    ∀ i, i + a < l.length → l.getD i false = true := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons b bs ih =>
    intro i hi
    simp only [List.length_cons] at hi
    have hb : driverNumber bs < 2^a := by
      simp only [driverNumber] at h
      omega
    cases i with
    | zero =>
      cases b
      · exfalso
        have : 2^a ≤ 2^bs.length := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp [driverNumber] at h
        omega
      · simp
    | succ i => simpa using ih hb i (by omega)

theorem dn_step (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : ordered a b) (t : Nat) (h1 : (run gs a).getD t false = true)
    (h2 : (run gs b).getD t false = false) :
    driverNumber (code gs a) + 1 ≤ driverNumber (code gs b) := by
  have mono := driver_mono gs ops ab
  by_contra hh
  have eq : driverNumber (code gs a) = driverNumber (code gs b) := by omega
  have same := driver_injective (by simp [code_len]) eq
  have := (output_order ops ab same).2 t h1
  rw [h2] at this
  exact Bool.noConfusion this

theorem head_true (C : Circuit) (ops : ∀ g∈C.gates, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    (a L : Nat) (z : Nat → List Bool) (ord : ∀ i, i < L → ordered (z i) (z (i+1)))
    (fall : ∀ i, i < L → ∃ t, (run C.gates (z i)).getD t false = true ∧
      (run C.gates (z (i+1))).getD t false = false)
    (hL : 2^PEqualNP.NotBracket.notCount C ≤ L + 2^a) (z' : List Bool) (o' : ordered z' (z 0)) :
    ∀ i, i + a < PEqualNP.NotBracket.notCount C → (code C.gates z').getD i false = true := by
  have key : ∀ i, i ≤ L →
      driverNumber (code C.gates (z 0)) + i ≤ driverNumber (code C.gates (z i)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      obtain ⟨t,h1,h2⟩ := fall i (by omega)
      have s1 := dn_step _ ops (ord i (by omega)) t h1 h2
      have s2 := ih (by omega)
      omega
  have h1 := key L le_rfl
  have h2 := driver_bound (code C.gates (z L))
  rw [code_len,mark_count] at h2
  have h3 := driver_mono C.gates ops o'
  intro i hi
  apply dn_top _ a (by omega)
  rw [code_len,mark_count]
  exact hi

theorem run_append (a b : List Gate) (w : List Bool) : run (a++b) w = run b (run a w) := by
  simp [run,List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    show (run gs (tick w g)).length = _
    rw [ih]
    simp [tick]
    omega

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem getD_run (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    show (run gs (tick w g)).getD i false = _
    rw [ih _ (by simp [tick]; omega)]
    simp only [tick]
    rw [List.getD_append _ _ _ _ h]

theorem getD_snoc_length (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem wire_gate (C : Circuit) (n : Nat) (back : ReadsBack n C) (xs : List Bool) (len : xs.length=n)
    (a : Nat) (ha : a < C.size) :
    (C.wires xs).getD (n+a) false =
      (gateAt C a).op.eval ((gateAt C a).inputs.map (fun i => (C.wires xs).getD i false)) := by
  let front := C.gates.take a
  let rest := C.gates.drop (a+1)
  let g := gateAt C a
  have geta : g=C.gates[a] := by simp [g,gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha]
  have split : C.gates=(front++[g])++rest := by
    rw [geta,←List.take_succ_eq_append_getElem ha,List.take_append_drop]
  have whole : C.wires xs=run rest (run [g] (run front xs)) := by
    change run C.gates xs=_
    conv_lhs => rw [split,run_append,run_append]
  have fw : (run front xs).length=n+a := by
    simp [run_length,front,len,List.length_take,Nat.min_eq_left (show a ≤ C.gates.length by exact ha.le)]
  have sw : (run [g] (run front xs)).length=n+a+1 := by rw [run_length,fw]; simp
  have old (i) (hi : i∈g.inputs) : (C.wires xs).getD i false=(run front xs).getD i false := by
    have good := back a ha i hi
    rw [whole,getD_run _ _ _ (sw ▸ (by omega)),getD_run _ _ _ (fw ▸ good)]
  change _=g.op.eval _
  rw [whole,getD_run _ _ _ (sw ▸ (by omega)),run_singleton,←fw,getD_snoc_length]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (old i hi).symm.trans (by rw [whole,run_singleton])

def remap (ρ : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

theorem gateAt_map (gs : List Gate) (o : Nat) (ρ : Nat → Nat) (j : Nat) :
    gateAt ⟨gs.map (remap ρ), o⟩ j = remap ρ (gateAt ⟨gs, o⟩ j) := by
  simp only [gateAt,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases gs[j]? <;> simp [remap]

theorem notCount_map (gs : List Gate) (o o' : Nat) (ρ : Nat → Nat) :
    PEqualNP.NotBracket.notCount ⟨gs.map (remap ρ), o⟩ = PEqualNP.NotBracket.notCount ⟨gs, o'⟩ := by
  unfold PEqualNP.NotBracket.notCount
  simp only [List.filter_map,List.length_map]
  rfl

def rho (n r t : Nat) : Nat := if t < n then t else if t < n+r+1 then n else t - r

theorem tail_getD (r k : Nat) :
    (List.replicate r false ++ [false,true]).getD k false = decide (k = r+1) := by
  induction r generalizing k with
  | zero => rcases k with _|_|k <;> simp
  | succ r ih =>
    cases k with
    | zero => simp [List.replicate_succ]
    | succ k => simpa [List.replicate_succ,List.getD_eq_getElem?_getD] using ih k

theorem inputs_agree (n r : Nat) (u : List Bool) (hu : u.length = n) (t : Nat) (ht : t < n+r+2) :
    (u ++ [false,true]).getD (rho n r t) false =
      (u ++ List.replicate r false ++ [false,true]).getD t false := by
  by_cases h1 : t < n
  · have : rho n r t = t := by unfold rho; simp [h1]
    rw [this,List.append_assoc,List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
  · have h0 := tail_getD 0 (rho n r t - n)
    simp only [List.replicate_zero,List.nil_append] at h0
    rw [List.append_assoc,List.getD_append_right _ _ _ _ (by unfold rho; split_ifs <;> omega),
      List.getD_append_right _ _ _ _ (by omega),hu,h0,tail_getD]
    congr 1
    simp only [eq_iff_iff]
    unfold rho
    split_ifs <;> omega

def valid (N : Nat) (C : Circuit) : Prop :=
  FanInTwo C ∧ ReadsBack N C ∧ C.output < N + C.size

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g::gs) w = run gs (tick w g) := rfl

theorem code_append (a b : List Gate) (w : List Bool) :
    code (a++b) w = code a w ++ code b (run a w) := by
  induction a generalizing w with
  | nil => rfl
  | cons g a ih => cases h : g.op <;> simp [code,h,ih,run_cons]

theorem code_at' (a : List Gate) (g : Gate) (b : List Gate) (w : List Bool) (gop : g.op = .not) :
    (code (a ++ g :: b) w).getD (a.filter mark).length false =
      (run (a ++ g :: b) w).getD (w.length + a.length) false := by
  rw [code_append,List.getD_append_right _ _ _ _ (by rw [code_len]),code_len,Nat.sub_self,
    run_append,run_cons,getD_run _ _ _ (by simp [tick,run_length]),tick,←run_length,
    getD_snoc_length]
  simp [code,gop,tick]

end PEqualNP.Outside.L_lib_1435_aux.Drivers

namespace PEqualNP.Outside.L_lib_1435_aux.Prefix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_lib_1435_aux.Drivers
open PEqualNP.NotBracket (notCount)
theorem rank_split (l : List Gate) (e : Nat) (h : e < (l.filter mark).length) :
    ∃ a g b, l = a ++ g :: b ∧ mark g = true ∧ (a.filter mark).length = e := by
  induction l generalizing e with
  | nil => simp at h
  | cons g l ih =>
    by_cases hm : mark g = true
    · cases e with
      | zero => exact ⟨[], g, l, rfl, hm, rfl⟩
      | succ e =>
        obtain ⟨a,g',b,rfl,h1,h2⟩ := ih e (by simpa [List.filter_cons,hm] using h)
        exact ⟨g::a, g', b, rfl, h1, by simp [List.filter_cons,hm,h2]⟩
    · obtain ⟨a,g',b,rfl,h1,h2⟩ := ih e (by simpa [List.filter_cons,hm] using h)
      exact ⟨g::a, g', b, rfl, h1, by simp [List.filter_cons,hm,h2]⟩

theorem firstCircuit (C : Circuit) (v : valid N C) (pos : 0 < notCount C) (z : ℕ) (hz : z < N) :
    ∃ S : Circuit, valid N S ∧ notCount S=0 ∧ S.size ≤ C.size-notCount C ∧
      ∀ x : List Bool, x.length=N → x.getD z false=false →
        S.eval x = !(code C.gates x).getD 0 false := by
  obtain ⟨a,g,b,eq,mg,na⟩ := rank_split C.gates 0 (by simpa only [mark_count] using pos)
  have op : g.op=.not := by cases h : g.op <;> simp_all [mark]
  have sz : C.size = a.length+1+b.length := by simp [Circuit.size,eq]; omega
  have gp : gateAt C a.length=g := by simp [gateAt,eq,List.getD_append_right _ _ _ _ le_rfl]
  have gs (i) (h : i∈g.inputs) : i<N+a.length := v.2.1 a.length (by simp [eq]) i (gp ▸ h)
  let o := g.inputs.headD z
  let S : Circuit := ⟨a,o⟩
  have vS : valid N S := by
    refine ⟨fun h hh => v.1 h (by rw [eq]; exact List.mem_append_left _ hh),?_,?_⟩
    · intro j hj i hi
      have same : gateAt C j=gateAt S j := by
        unfold gateAt
        rw [eq,List.getD_append _ _ _ _ (show j < a.length from hj)]
      apply v.2.1 j (by simp [eq]; change j<a.length at hj; omega) i (same ▸ hi)
    · change g.inputs.headD z<N+a.length
      cases h : g.inputs with
      | nil => simp; omega
      | cons i t => exact gs i (by simp [h])
  have countS : notCount S=0 := (mark_count _).symm.trans na
  have cost : S.size ≤ C.size-notCount C := by
    have nb := List.length_filter_le mark b
    have nc : notCount C=(b.filter mark).length+1 := by
      rw [←mark_count,eq,List.filter_append,List.length_append,na]
      simp [List.filter_cons,mg]
    change a.length ≤ _
    omega
  refine ⟨S,vS,countS,cost,?_⟩
  intro x hx h0
  have noCode : code a x=[] := List.length_eq_zero_iff.mp ((code_len a x).trans na)
  rw [eq,code_append,noCode,List.nil_append]
  simp only [PEqualNP.Outside.L_lib_1435_aux.Drivers.code,op,List.getD_cons_zero]
  change (run a x).getD o false = !((GateOp.not).eval (g.inputs.map fun i => (run a x).getD i false))
  cases h : g.inputs with
  | nil => simpa [o,h,GateOp.eval] using (getD_run a x z (hx ▸ hz)).trans h0
  | cons i t => simp [o,h,GateOp.eval]
end PEqualNP.Outside.L_lib_1435_aux.Prefix

namespace PEqualNP.Outside.L_lib_1435_aux.Prefix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_lib_1435_aux.Wire PEqualNP.Outside.L_lib_1435_aux.Drivers
open PEqualNP.NotBracket (notCount)
theorem inputAt (s : ℕ) (X : Finset ℕ) (k : ℕ) (h : k<s) :
    (input s X).getD k false=decide (k∈X) := by
  rw [input,List.getD_append _ _ _ _ (by simpa)]
  simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h]
theorem inputFalse (s : ℕ) (X : Finset ℕ) : (input s X).getD s false=false := by
  rw [input,List.getD_append_right _ _ _ _ (by simp)]
  simp
theorem inputTrue (s : ℕ) (X : Finset ℕ) : (input s X).getD (s+1) false=true := by
  rw [input,List.getD_append_right _ _ _ _ (by simp)]
  simp
theorem orderedInput (r : ℕ) {A B : Finset ℕ} (h : A ⊆ B) : ordered (input r A) (input r B) := by
  apply input_order
  intro i yes
  simpa using h (of_decide_eq_true yes)
theorem readFirst (r : ℕ) (D : Circuit) (v : Valid r D) :
    ∃ S : Circuit, Valid r S ∧ notCount S=0 ∧ S.size ≤ D.size-notCount D ∧
      ∀Y,S.eval (input r Y) = !(code D.gates (input r Y)).getD 0 false := by
  by_cases h : 0 < notCount D
  · obtain ⟨S,vS,n,c,ev⟩ := firstCircuit D v h r (by omega)
    exact ⟨S,vS,n,c,fun Y => ev _ (by simp [input]) (inputFalse _ _)⟩
  · let S : Circuit := ⟨[],r+1⟩
    have good : Valid r S := by
      refine ⟨fun g m => False.elim (List.not_mem_nil m),fun j hj => False.elim (by change j<0 at hj; omega),?_⟩
      simp [S,Circuit.size]
    refine ⟨S,good,rfl,Nat.zero_le _,?_⟩
    intro Y
    have empty : code D.gates (input r Y)=[] := List.length_eq_zero_iff.mp (by rw [code_len,mark_count]; omega)
    simp only [empty,List.getD_nil,Bool.not_false]
    exact inputTrue r Y
end PEqualNP.Outside.L_lib_1435_aux.Prefix

namespace PEqualNP.Outside.L_lib_1435_aux.Tree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

def pivot (s j : ℕ) : ℕ := (2 * (s / 2 ^ (j + 1)) + 1) * 2 ^ j

def path (h s : ℕ) (v : Bool) : Finset ℕ :=
  ((Finset.range h).filter (fun j => decide (s / 2 ^ j % 2 = 1) = v)).image (pivot s)

def cell (h : ℕ) (s : Fin (2 ^ h)) (Y : Finset ℕ) : Prop :=
  path h s.val true ⊆ Y ∧ Disjoint (path h s.val false) Y

lemma pivot_inj (s : ℕ) : Function.Injective (pivot s) := by
  intro j1 j2 h
  unfold pivot at h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hdiv : 2 ^ j1 ∣ (2 * (s / 2 ^ (j2 + 1)) + 1) * 2 ^ j2 := by
      have : 2 ^ j1 ∣ 2 ^ j2 := Nat.pow_dvd_pow 2 (Nat.le_of_lt hlt)
      exact dvd_mul_of_dvd_right this _
    have h1 : 2 * (s / 2 ^ (j1 + 1)) + 1 = (2 * (s / 2 ^ (j2 + 1)) + 1) * 2 ^ (j2 - j1) := by
      have hpow : 2 ^ j2 = 2 ^ (j2 - j1) * 2 ^ j1 := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      rw [hpow, ← Nat.mul_assoc] at h
      exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by decide : 0 < 2)) h
    have heven : 2 ∣ (2 * (s / 2 ^ (j2 + 1)) + 1) * 2 ^ (j2 - j1) := by
      apply dvd_mul_of_dvd_right
      exact dvd_pow_self 2 (by omega)
    rw [← h1] at heven
    omega
  · have h1 : 2 * (s / 2 ^ (j2 + 1)) + 1 = (2 * (s / 2 ^ (j1 + 1)) + 1) * 2 ^ (j1 - j2) := by
      have hpow : 2 ^ j1 = 2 ^ (j1 - j2) * 2 ^ j2 := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hgt)]
      rw [hpow, ← Nat.mul_assoc] at h
      exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by decide : 0 < 2)) h.symm
    have heven : 2 ∣ (2 * (s / 2 ^ (j1 + 1)) + 1) * 2 ^ (j1 - j2) := by
      apply dvd_mul_of_dvd_right
      exact dvd_pow_self 2 (by omega)
    rw [← h1] at heven
    omega

lemma pivot_pos (s j : ℕ) : 1 ≤ pivot s j := by
  unfold pivot
  have h2 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
  have h1 : 1 ≤ 2 * (s / 2 ^ (j + 1)) + 1 := by omega
  nlinarith

lemma pivot_lt {h s j : ℕ} (hs : s < 2 ^ h) (hj : j < h) : pivot s j < 2 ^ h := by
  unfold pivot
  have hpow : 2 ^ h = 2 ^ (h - (j + 1)) * 2 ^ (j + 1) := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hdiv : s / 2 ^ (j + 1) < 2 ^ (h - (j + 1)) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))]
    rw [← hpow]
    exact hs
  have h1 : 2 * (s / 2 ^ (j + 1)) + 1 < 2 * 2 ^ (h - (j + 1)) := by omega
  have h2 : (2 * (s / 2 ^ (j + 1)) + 1) * 2 ^ j < (2 * 2 ^ (h - (j + 1))) * 2 ^ j :=
    Nat.mul_lt_mul_of_pos_right h1 (Nat.pow_pos (by decide : 0 < 2))
  have h3 : (2 * 2 ^ (h - (j + 1))) * 2 ^ j = 2 ^ h := by
    calc (2 * 2 ^ (h - (j + 1))) * 2 ^ j
        = 2 ^ (h - (j + 1)) * (2 ^ j * 2) := by ring
      _ = 2 ^ (h - (j + 1)) * 2 ^ (j + 1) := by rw [← Nat.pow_succ]
      _ = 2 ^ h := hpow.symm
  rw [h3] at h2
  exact h2

lemma nat_bit_decomp (s j : ℕ) :
    s = (s / 2 ^ (j + 1)) * 2 ^ (j + 1) + (s / 2 ^ j % 2) * 2 ^ j + s % 2 ^ j := by
  have h1 := (Nat.div_add_mod s (2 ^ j)).symm
  have h2 := (Nat.div_add_mod (s / 2 ^ j) 2).symm
  have h3 : (s / 2 ^ j) / 2 = s / 2 ^ (j + 1) := by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  rw [h3] at h2
  have h4 : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
  calc s = 2 ^ j * (s / 2 ^ j) + s % 2 ^ j := h1
    _ = 2 ^ j * (2 * (s / 2 ^ (j + 1)) + s / 2 ^ j % 2) + s % 2 ^ j := by nth_rw 1 [h2]
    _ = (s / 2 ^ (j + 1)) * (2 ^ j * 2) + (s / 2 ^ j % 2) * 2 ^ j + s % 2 ^ j := by ring
    _ = (s / 2 ^ (j + 1)) * 2 ^ (j + 1) + (s / 2 ^ j % 2) * 2 ^ j + s % 2 ^ j := by rw [← h4]

lemma pivot_le_of_bit1 {s j : ℕ} (hb : s / 2 ^ j % 2 = 1) : pivot s j ≤ s := by
  have hd := nat_bit_decomp s j
  rw [hb] at hd
  unfold pivot
  have h4 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
  have : (2 * (s / 2 ^ (j + 1)) + 1) * 2 ^ j = (s / 2 ^ (j + 1)) * 2 ^ (j + 1) + 1 * 2 ^ j := by
    rw [h4]; ring
  omega

lemma lt_pivot_of_bit0 {s j : ℕ} (hb : s / 2 ^ j % 2 = 0) : s < pivot s j := by
  have hd := nat_bit_decomp s j
  rw [hb] at hd
  have hmod : s % 2 ^ j < 2 ^ j := Nat.mod_lt s (Nat.pow_pos (by decide : 0 < 2))
  unfold pivot
  have h4 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
  have : (2 * (s / 2 ^ (j + 1)) + 1) * 2 ^ j = (s / 2 ^ (j + 1)) * 2 ^ (j + 1) + 2 ^ j := by
    rw [h4]; ring
  omega

lemma part1 (h : ℕ) (s : Fin (2 ^ h)) :
    (path h s.val true ∪ path h s.val false).card = h ∧ cell h s (Finset.Icc 1 s.val) := by
  constructor
  · have hunion : path h s.val true ∪ path h s.val false = (Finset.range h).image (pivot s.val) := by
      unfold path
      rw [← Finset.image_union]
      congr 1
      ext j
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
      · intro hj
        cases hdec : decide (s.val / 2 ^ j % 2 = 1)
        · exact Or.inr ⟨hj, rfl⟩
        · exact Or.inl ⟨hj, rfl⟩
    rw [hunion, Finset.card_image_of_injective _ (pivot_inj s.val), Finset.card_range]
  · constructor
    · intro p hp
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hp
      obtain ⟨j, ⟨_, hb⟩, rfl⟩ := hp
      exact Finset.mem_Icc.mpr ⟨pivot_pos s.val j, pivot_le_of_bit1 hb⟩
    · rw [Finset.disjoint_left]
      intro p hp hmem
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_false_iff_not] at hp
      obtain ⟨j, ⟨_, hb⟩, rfl⟩ := hp
      have hb0 : s.val / 2 ^ j % 2 = 0 := by omega
      have hlt := lt_pivot_of_bit0 hb0
      have hle := (Finset.mem_Icc.mp hmem).2
      omega

lemma exists_highest_diff : ∀ (h s t : ℕ), s < 2 ^ h → t < 2 ^ h → t < s →
    ∃ j < h, s / 2 ^ (j + 1) = t / 2 ^ (j + 1) ∧ s / 2 ^ j % 2 = 1 ∧ t / 2 ^ j % 2 = 0 := by
  intro h
  induction h with
  | zero => intro s t hs ht hlt; omega
  | succ k ih =>
    intro s t hs ht hlt
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hs1 : s / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt hs
    have ht1 : t / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt ht
    by_cases hsk : s / 2 ^ k = t / 2 ^ k
    · have hs' : s % 2 ^ k < 2 ^ k := Nat.mod_lt s (Nat.pow_pos (by decide : 0 < 2))
      have ht' : t % 2 ^ k < 2 ^ k := Nat.mod_lt t (Nat.pow_pos (by decide : 0 < 2))
      have hlt' : t % 2 ^ k < s % 2 ^ k := by
        have h1 := Nat.div_add_mod s (2 ^ k)
        have h2 := Nat.div_add_mod t (2 ^ k)
        rw [hsk] at h1
        omega
      obtain ⟨j, hj, hdiv, hsb, htb⟩ := ih (s % 2 ^ k) (t % 2 ^ k) hs' ht' hlt'
      refine ⟨j, by omega, ?_, ?_, ?_⟩
      · have hpow2 : 2 ^ k = 2 ^ (j + 1) * 2 ^ (k - (j + 1)) := by
          rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
        have h1 : s = 2 ^ (j + 1) * (s / 2 ^ k * 2 ^ (k - (j + 1))) + s % 2 ^ k := by
          calc s = 2 ^ k * (s / 2 ^ k) + s % 2 ^ k := (Nat.div_add_mod s (2 ^ k)).symm
            _ = 2 ^ (j + 1) * (s / 2 ^ k * 2 ^ (k - (j + 1))) + s % 2 ^ k := by rw [hpow2]; ring
        have h2 : t = 2 ^ (j + 1) * (t / 2 ^ k * 2 ^ (k - (j + 1))) + t % 2 ^ k := by
          calc t = 2 ^ k * (t / 2 ^ k) + t % 2 ^ k := (Nat.div_add_mod t (2 ^ k)).symm
            _ = 2 ^ (j + 1) * (t / 2 ^ k * 2 ^ (k - (j + 1))) + t % 2 ^ k := by rw [hpow2]; ring
        rw [h1, h2, hsk,
            Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)),
            Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)), hdiv]
      · have hpow2 : 2 ^ k = 2 ^ j * (2 * 2 ^ (k - j - 1)) := by
          rw [← Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add]
          congr 1; omega
        have h1 : s = 2 ^ j * (2 * (s / 2 ^ k * 2 ^ (k - j - 1))) + s % 2 ^ k := by
          calc s = 2 ^ k * (s / 2 ^ k) + s % 2 ^ k := (Nat.div_add_mod s (2 ^ k)).symm
            _ = 2 ^ j * (2 * (s / 2 ^ k * 2 ^ (k - j - 1))) + s % 2 ^ k := by rw [hpow2]; ring
        rw [h1, Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)), Nat.mul_add_mod, hsb]
      · have hpow2 : 2 ^ k = 2 ^ j * (2 * 2 ^ (k - j - 1)) := by
          rw [← Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add]
          congr 1; omega
        have h2 : t = 2 ^ j * (2 * (t / 2 ^ k * 2 ^ (k - j - 1))) + t % 2 ^ k := by
          calc t = 2 ^ k * (t / 2 ^ k) + t % 2 ^ k := (Nat.div_add_mod t (2 ^ k)).symm
            _ = 2 ^ j * (2 * (t / 2 ^ k * 2 ^ (k - j - 1))) + t % 2 ^ k := by rw [hpow2]; ring
        rw [h2, Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)), Nat.mul_add_mod, htb]
    · have hsle : s / 2 ^ k < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))]; omega
      have htle : t / 2 ^ k < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))]; omega
      have hle : t / 2 ^ k ≤ s / 2 ^ k := Nat.div_le_div_right (Nat.le_of_lt hlt)
      have hsbit : s / 2 ^ k = 1 := by
        generalize ha : s / 2 ^ k = a at hsle hle hsk
        generalize hb : t / 2 ^ k = b at htle hle hsk
        omega
      have htbit : t / 2 ^ k = 0 := by
        generalize ha : s / 2 ^ k = a at hsle hle hsk
        generalize hb : t / 2 ^ k = b at htle hle hsk
        omega
      exact ⟨k, by omega, by rw [hs1, ht1], by simp [hsbit], by simp [htbit]⟩

lemma part3 (h : ℕ) (X Y : Finset ℕ) (s t : Fin (2 ^ h))
    (hXY : X ⊆ Y) (hs : cell h s X) (ht : cell h t Y) : s ≤ t := by
  by_contra hgt
  have hlt : t.val < s.val := Nat.lt_of_not_ge hgt
  obtain ⟨j, hj, hdiv, hsb, htb⟩ := exists_highest_diff h s.val t.val s.isLt t.isLt hlt
  have hp : pivot s.val j = pivot t.val j := by unfold pivot; rw [hdiv]
  have hinX : pivot s.val j ∈ X := hs.1 (by
    simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    exact ⟨j, ⟨hj, by simp [hsb]⟩, rfl⟩)
  have hinY : pivot t.val j ∈ Y := hp ▸ hXY hinX
  have hnotY : pivot t.val j ∉ Y := Finset.disjoint_left.mp ht.2 (by
    simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    exact ⟨j, ⟨hj, by simp [htb]⟩, rfl⟩)
  exact hnotY hinY

def findIdx : ℕ → ℕ → Finset ℕ → ℕ
  | 0, base, _ => base
  | k + 1, base, Y =>
    if (base + 2 ^ k) ∈ Y then findIdx k (base + 2 ^ k) Y else findIdx k base Y

lemma findIdx_spec (Y : Finset ℕ) : ∀ (k q : ℕ),
    q * 2 ^ k ≤ findIdx k (q * 2 ^ k) Y ∧
    findIdx k (q * 2 ^ k) Y < (q + 1) * 2 ^ k ∧
    ∀ j < k, (findIdx k (q * 2 ^ k) Y / 2 ^ j % 2 = 1 ↔ pivot (findIdx k (q * 2 ^ k) Y) j ∈ Y) := by
  intro k
  induction k with
  | zero =>
    intro q
    simp only [findIdx, Nat.pow_zero, Nat.mul_one]
    exact ⟨le_rfl, by omega, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro q
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hq0 : q * 2 ^ (k + 1) = (2 * q) * 2 ^ k := by rw [hpow]; ring
    have hq1 : q * 2 ^ (k + 1) + 2 ^ k = (2 * q + 1) * 2 ^ k := by rw [hpow]; ring
    unfold findIdx
    by_cases hin : q * 2 ^ (k + 1) + 2 ^ k ∈ Y
    · simp only [hin, ite_true]
      rw [hq1]
      obtain ⟨hlo, hhi, hbits⟩ := ih (2 * q + 1)
      set r := findIdx k ((2 * q + 1) * 2 ^ k) Y
      have hdivk1 : r / 2 ^ (k + 1) = q := by
        have hp : 0 < 2 ^ (k + 1) := Nat.pow_pos (by decide : 0 < 2)
        apply Nat.le_antisymm
        · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).mpr (by rw [hpow]; nlinarith))
        · exact (Nat.le_div_iff_mul_le hp).mpr (by rw [hpow]; nlinarith)
      have hdivk : r / 2 ^ k = 2 * q + 1 := by
        have hp : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
        apply Nat.le_antisymm
        · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith))
        · exact (Nat.le_div_iff_mul_le hp).mpr hlo
      refine ⟨by rw [hpow]; nlinarith, by rw [hpow]; nlinarith, fun j hj => ?_⟩
      by_cases hjk : j < k
      · exact hbits j hjk
      · have heq : j = k := by omega
        subst j
        have hpiv : pivot r k = q * 2 ^ (k + 1) + 2 ^ k := by
          unfold pivot; rw [hdivk1, hq1]
        rw [hdivk, hpiv]
        simp [hin]
    · simp only [hin, ite_false]
      rw [hq0]
      obtain ⟨hlo, hhi, hbits⟩ := ih (2 * q)
      set r := findIdx k ((2 * q) * 2 ^ k) Y
      have hdivk1 : r / 2 ^ (k + 1) = q := by
        have hp : 0 < 2 ^ (k + 1) := Nat.pow_pos (by decide : 0 < 2)
        apply Nat.le_antisymm
        · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).mpr (by rw [hpow]; nlinarith))
        · exact (Nat.le_div_iff_mul_le hp).mpr (by rw [hpow]; nlinarith)
      have hdivk : r / 2 ^ k = 2 * q := by
        have hp : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
        apply Nat.le_antisymm
        · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith))
        · exact (Nat.le_div_iff_mul_le hp).mpr hlo
      refine ⟨hlo, by rw [hpow]; nlinarith, fun j hj => ?_⟩
      by_cases hjk : j < k
      · exact hbits j hjk
      · have heq : j = k := by omega
        subst j
        have hpiv : pivot r k = q * 2 ^ (k + 1) + 2 ^ k := by
          unfold pivot; rw [hdivk1, hq1]
        rw [hdivk, hpiv]
        simp [hin]

lemma part2 (h : ℕ) (Y : Finset ℕ) : ∃! s : Fin (2 ^ h), cell h s Y := by
  have hspec := findIdx_spec Y h 0
  simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul] at hspec
  obtain ⟨_, hlt, hbits⟩ := hspec
  let s : Fin (2 ^ h) := ⟨findIdx h 0 Y, hlt⟩
  refine ⟨s, ?_, fun t ht => le_antisymm (part3 h Y Y t s (Finset.Subset.refl _) ht ?_)
    (part3 h Y Y s t (Finset.Subset.refl _) ?_ ht)⟩
  · constructor
    · intro p hp
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact (hbits j hj).mp hb
    · rw [Finset.disjoint_left]
      intro p hp hin
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_false_iff_not] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact hb ((hbits j hj).mpr hin)
  · constructor
    · intro p hp
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact (hbits j hj).mp hb
    · rw [Finset.disjoint_left]
      intro p hp hin
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_false_iff_not] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact hb ((hbits j hj).mpr hin)
  · constructor
    · intro p hp
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact (hbits j hj).mp hb
    · rw [Finset.disjoint_left]
      intro p hp hin
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_false_iff_not] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact hb ((hbits j hj).mpr hin)

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma runW_nil (w : List Bool) : runW [] w = w := rfl

lemma runW_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    runW (g :: gs) w = runW gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma runW_append (gs hs : List Gate) (w : List Bool) :
    runW (gs ++ hs) w = runW hs (runW gs w) := by
  simp [runW, List.foldl_append]

lemma runW_len (gs : List Gate) : ∀ w : List Bool, (runW gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [runW]
  | cons g gs ih => intro w; rw [runW_cons, ih]; simp; omega

lemma runW_old (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (runW gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [runW_cons, ih _ i (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma eval_eq_runW (C : Circuit) (w : List Bool) :
    C.eval w = (runW C.gates w).getD C.output false := rfl

def notCnt (gs : List Gate) : ℕ :=
  notCount ⟨gs, 0⟩

lemma notCnt_append (gs hs : List Gate) : notCnt (gs ++ hs) = notCnt gs + notCnt hs := by
  simp [notCnt, notCount, List.filter_append]

lemma notCnt_of_no_not (gs : List Gate) (h : ∀ g ∈ gs, g.op ≠ GateOp.not) : notCnt gs = 0 := by
  unfold notCnt notCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  simp [h g hg]

def validGs (base : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < base + j)

lemma validGs_nil (base : ℕ) : validGs base [] :=
  ⟨fun _ h => absurd h (List.not_mem_nil), fun _ h => absurd h (Nat.not_lt_zero _)⟩

lemma validGs_append {base : ℕ} {gs hs : List Gate}
    (h1 : validGs base gs) (h2 : validGs (base + gs.length) hs) : validGs base (gs ++ hs) := by
  refine ⟨fun g hg => ?_, fun j hj i hi => ?_⟩
  · rcases List.mem_append.mp hg with hg | hg
    · exact h1.1 g hg
    · exact h2.1 g hg
  · by_cases hlt : j < gs.length
    · rw [List.getD_append _ _ _ _ hlt] at hi
      exact h1.2 j hlt i hi
    · have hge : gs.length ≤ j := Nat.le_of_not_gt hlt
      rw [List.getD_append_right _ _ _ _ hge] at hi
      have hlt2 : j - gs.length < hs.length := by simp at hj; omega
      have := h2.2 (j - gs.length) hlt2 i hi
      omega

def orChain (acc base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], acc)
  | w :: ws =>
    let p := orChain base (base + 1) ws
    (⟨.or, [acc, w]⟩ :: p.1, p.2)

lemma orChain_len (ws : List ℕ) : ∀ acc base, (orChain acc base ws).1.length = ws.length := by
  induction ws with
  | nil => intro _ _; rfl
  | cons w ws ih => intro acc base; simp [orChain, ih]

lemma orChain_out (ws : List ℕ) : ∀ acc base, acc < base →
    (orChain acc base ws).2 < base + ws.length := by
  induction ws with
  | nil => intro acc base h; simpa [orChain] using h
  | cons w ws ih =>
    intro acc base h
    have := ih base (base + 1) (by omega)
    simp only [orChain, List.length_cons]
    omega

lemma orChain_notCnt (ws : List ℕ) : ∀ acc base, notCnt (orChain acc base ws).1 = 0 := by
  induction ws with
  | nil => intro _ _; rfl
  | cons w ws ih =>
    intro acc base
    have h1 : (orChain acc base (w :: ws)).1 = [⟨.or, [acc, w]⟩] ++ (orChain base (base + 1) ws).1 := rfl
    rw [h1, notCnt_append, ih base (base + 1), Nat.add_zero]
    exact notCnt_of_no_not _ (fun g hg => by simp at hg; subst hg; simp)

lemma orChain_valid (ws : List ℕ) : ∀ acc base, acc < base → (∀ w ∈ ws, w < base) →
    validGs base (orChain acc base ws).1 := by
  induction ws with
  | nil => intro _ _ _ _; exact validGs_nil _
  | cons w ws ih =>
    intro acc base hacc hws
    have hw0 : w < base := hws w List.mem_cons_self
    have hrest := ih base (base + 1) (by omega) (fun x hx => by have := hws x (List.mem_cons_of_mem _ hx); omega)
    have h1 : validGs base [⟨.or, [acc, w]⟩] := by
      refine ⟨fun g hg => by simp at hg; subst hg; simp, fun j hj i hi => ?_⟩
      simp at hj; subst hj
      simp only [List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    exact validGs_append h1 hrest

lemma orChain_eval (ws : List ℕ) : ∀ (acc : ℕ) (init : List Bool),
    acc < init.length → (∀ w ∈ ws, w < init.length) →
    (runW (orChain acc init.length ws).1 init).getD (orChain acc init.length ws).2 false =
      (init.getD acc false || ws.any (fun w => init.getD w false)) := by
  induction ws with
  | nil =>
    intro acc init _ _
    simp [orChain, runW]
  | cons w ws ih =>
    intro acc init hacc hws
    have hw0 : w < init.length := hws w List.mem_cons_self
    let init1 := init ++ [GateOp.or.eval ([acc, w].map fun i => init.getD i false)]
    have hlen1 : init1.length = init.length + 1 := by simp [init1]
    simp only [orChain, runW_cons]
    change (runW (orChain init.length (init.length + 1) ws).1 init1).getD
      (orChain init.length (init.length + 1) ws).2 false = _
    rw [← hlen1, ih init.length init1 (by omega) (fun x hx => by have := hws x (List.mem_cons_of_mem _ hx); omega)]
    have hlast : init1.getD init.length false = (init.getD acc false || init.getD w false) := by
      simp [init1, GateOp.eval]
    have hany : ws.any (fun x => init1.getD x false) = ws.any (fun x => init.getD x false) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      exact exists_congr fun x => and_congr_right fun hx => by
        rw [List.getD_append _ _ _ _ (hws x (List.mem_cons_of_mem _ hx))]
    rw [hlast, hany]
    simp [Bool.or_assoc]

def orList (base zeroWire : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], zeroWire)
  | w :: ws => orChain w base ws

lemma orList_len_le (base zeroWire : ℕ) (ws : List ℕ) :
    (orList base zeroWire ws).1.length ≤ ws.length := by
  cases ws with
  | nil => simp [orList]
  | cons w ws => simp [orList, orChain_len]

lemma orList_out (base zeroWire : ℕ) (ws : List ℕ) (hz : zeroWire < base) (hws : ∀ w ∈ ws, w < base) :
    (orList base zeroWire ws).2 < base + (orList base zeroWire ws).1.length := by
  cases ws with
  | nil => simpa [orList] using hz
  | cons w ws =>
    simp only [orList, orChain_len]
    exact orChain_out ws w base (hws w List.mem_cons_self)

lemma orList_notCnt (base zeroWire : ℕ) (ws : List ℕ) : notCnt (orList base zeroWire ws).1 = 0 := by
  cases ws with
  | nil => rfl
  | cons w ws => exact orChain_notCnt ws w base

lemma orList_valid (base zeroWire : ℕ) (ws : List ℕ) (hws : ∀ w ∈ ws, w < base) :
    validGs base (orList base zeroWire ws).1 := by
  cases ws with
  | nil => exact validGs_nil _
  | cons w ws =>
    exact orChain_valid ws w base (hws w List.mem_cons_self) (fun x hx => hws x (List.mem_cons_of_mem _ hx))

lemma orList_eval (zeroWire : ℕ) (ws : List ℕ) (init : List Bool)
    (hz : init.getD zeroWire false = false) (hws : ∀ w ∈ ws, w < init.length) :
    (runW (orList init.length zeroWire ws).1 init).getD (orList init.length zeroWire ws).2 false =
      ws.any (fun w => init.getD w false) := by
  cases ws with
  | nil => simpa [orList, runW] using hz
  | cons w ws =>
    simp only [orList, List.any_cons]
    exact orChain_eval ws w init (hws w List.mem_cons_self) (fun x hx => hws x (List.mem_cons_of_mem _ hx))

def andPivotGs (k : ℕ) (flags : List ℕ) : List Gate :=
  flags.mapIdx (fun q w => ⟨.and, [w, (2 * q + 1) * 2 ^ k]⟩)

lemma andPivotGs_len (k : ℕ) (flags : List ℕ) : (andPivotGs k flags).length = flags.length := by
  simp [andPivotGs]

lemma andPivotGs_notCnt (k : ℕ) (flags : List ℕ) : notCnt (andPivotGs k flags) = 0 := by
  apply notCnt_of_no_not
  intro g hg
  simp only [andPivotGs, List.mem_iff_getElem, List.length_mapIdx, List.getElem_mapIdx] at hg
  obtain ⟨i, _, rfl⟩ := hg
  simp

lemma andPivotGs_valid (h k base : ℕ) (flags : List ℕ) (hM : 2 ^ h ≤ base)
    (hfl : ∀ w ∈ flags, w < base) (hflLen : flags.length * 2 ^ (k + 1) ≤ 2 ^ h) :
    validGs base (andPivotGs k flags) := by
  refine ⟨fun g hg => ?_, fun j hj i hi => ?_⟩
  · simp only [andPivotGs, List.mem_iff_getElem, List.length_mapIdx, List.getElem_mapIdx] at hg
    obtain ⟨_, _, rfl⟩ := hg; simp
  · rw [andPivotGs_len] at hj
    have hget : (andPivotGs k flags).getD j ⟨GateOp.or, []⟩ =
        ⟨.and, [flags[j], (2 * j + 1) * 2 ^ k]⟩ := by
      simp [andPivotGs, List.getD_eq_getElem?_getD, hj]
    rw [hget] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · have := hfl flags[j] (List.getElem_mem hj); omega
    · have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      have h1 : (2 * j + 1) * 2 ^ k < (j + 1) * 2 ^ (k + 1) := by rw [hpow]; nlinarith [Nat.pow_pos (a := 2) (n := k) (by decide)]
      have h2 : (j + 1) * 2 ^ (k + 1) ≤ flags.length * 2 ^ (k + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega

lemma andPivotGs_eval_aux (k : ℕ) : ∀ (off : ℕ) (flags : List ℕ) (init : List Bool),
    (∀ w ∈ flags, w < init.length) →
    (∀ q < flags.length, (2 * (off + q) + 1) * 2 ^ k < init.length) →
    ∀ q < flags.length,
      (runW (flags.mapIdx fun q w => ⟨.and, [w, (2 * (off + q) + 1) * 2 ^ k]⟩) init).getD (init.length + q) false =
        (init.getD (flags.getD q 0) false && init.getD ((2 * (off + q) + 1) * 2 ^ k) false) := by
  intro off flags
  induction flags generalizing off with
  | nil => intro _ _ _ q hq; exact absurd hq (Nat.not_lt_zero _)
  | cons w ws ih =>
    intro init hfl hpiv q hq
    have hw0 : w < init.length := hfl w List.mem_cons_self
    have hp0 : (2 * (off + 0) + 1) * 2 ^ k < init.length := hpiv 0 (by simp)
    have hmap : ((w :: ws).mapIdx fun q w => ({ op := .and, inputs := [w, (2 * (off + q) + 1) * 2 ^ k] } : Gate)) =
        ({ op := .and, inputs := [w, (2 * off + 1) * 2 ^ k] } : Gate) ::
        (ws.mapIdx fun q w => ({ op := .and, inputs := [w, (2 * ((off + 1) + q) + 1) * 2 ^ k] } : Gate)) := by
      simp only [List.mapIdx_cons, Nat.add_zero]
      congr 1
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.getElem_mapIdx]
      congr 2; congr 1; congr 1; omega
    rw [hmap, runW_cons]
    let init1 := init ++ [GateOp.and.eval ([w, (2 * off + 1) * 2 ^ k].map fun i => init.getD i false)]
    have hl1 : init1.length = init.length + 1 := by simp [init1]
    change (runW (ws.mapIdx fun q w => ⟨.and, [w, (2 * ((off + 1) + q) + 1) * 2 ^ k]⟩) init1).getD
      (init.length + q) false = _
    cases q with
    | zero =>
      simp only [Nat.add_zero]
      rw [runW_old _ init1 init.length (by omega)]
      simp [init1, GateOp.eval]
    | succ q' =>
      have hq' : q' < ws.length := by simp at hq; omega
      have hidx : init.length + (q' + 1) = init1.length + q' := by omega
      rw [hidx]
      have hres := ih (off + 1) init1
        (fun x hx => by have := hfl x (List.mem_cons_of_mem _ hx); omega)
        (fun r hr => by
          have := hpiv (r + 1) (by simp; omega)
          have heq : off + 1 + r = off + (r + 1) := by omega
          rw [heq]; omega)
        q' hq'
      rw [hres]
      have hflq : ws.getD q' 0 < init.length := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq', Option.getD_some]
        exact hfl ws[q'] (List.mem_cons_of_mem _ (List.getElem_mem hq'))
      have hpq : (2 * (off + 1 + q') + 1) * 2 ^ k < init.length := by
        have := hpiv (q' + 1) (by simp; omega)
        have heq : off + 1 + q' = off + (q' + 1) := by omega
        rw [heq]; exact this
      rw [List.getD_append _ _ _ _ hflq, List.getD_append _ _ _ _ hpq]
      have heq : off + 1 + q' = off + (q' + 1) := by omega
      rw [heq]
      rfl

def leftGs (nsel : ℕ) (flags : List ℕ) : List Gate :=
  flags.map (fun w => ⟨.and, [w, nsel]⟩)

lemma leftGs_len (nsel : ℕ) (flags : List ℕ) : (leftGs nsel flags).length = flags.length := by
  simp [leftGs]

lemma leftGs_notCnt (nsel : ℕ) (flags : List ℕ) : notCnt (leftGs nsel flags) = 0 := by
  apply notCnt_of_no_not
  intro g hg
  simp only [leftGs, List.mem_map] at hg
  obtain ⟨_, _, rfl⟩ := hg; simp

lemma leftGs_valid (nsel base : ℕ) (flags : List ℕ) (hns : nsel < base) (hfl : ∀ w ∈ flags, w < base) :
    validGs base (leftGs nsel flags) := by
  refine ⟨fun g hg => ?_, fun j hj i hi => ?_⟩
  · simp only [leftGs, List.mem_map] at hg; obtain ⟨_, _, rfl⟩ := hg; simp
  · rw [leftGs_len] at hj
    have hget : (leftGs nsel flags).getD j ⟨GateOp.or, []⟩ = ⟨.and, [flags[j], nsel]⟩ := by
      simp [leftGs, List.getD_eq_getElem?_getD, hj]
    rw [hget] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · have := hfl flags[j] (List.getElem_mem hj); omega
    · omega

lemma leftGs_eval (nsel : ℕ) : ∀ (flags : List ℕ) (init : List Bool),
    nsel < init.length → (∀ w ∈ flags, w < init.length) →
    ∀ q < flags.length,
      (runW (leftGs nsel flags) init).getD (init.length + q) false =
        (init.getD (flags.getD q 0) false && init.getD nsel false) := by
  intro flags
  induction flags with
  | nil => intro _ _ _ q hq; exact absurd hq (Nat.not_lt_zero _)
  | cons w ws ih =>
    intro init hns hfl q hq
    have hcons : leftGs nsel (w :: ws) = ⟨.and, [w, nsel]⟩ :: leftGs nsel ws := rfl
    rw [hcons, runW_cons]
    let init1 := init ++ [GateOp.and.eval ([w, nsel].map fun i => init.getD i false)]
    have hl1 : init1.length = init.length + 1 := by simp [init1]
    cases q with
    | zero =>
      simp only [Nat.add_zero]
      rw [runW_old _ init1 init.length (by omega)]
      simp [init1, GateOp.eval]
    | succ q' =>
      have hq' : q' < ws.length := by simp at hq; omega
      have hidx : init.length + (q' + 1) = init1.length + q' := by omega
      rw [hidx]
      have hres := ih init1 (by omega)
        (fun x hx => by have := hfl x (List.mem_cons_of_mem _ hx); omega) q' hq'
      rw [hres]
      have hflq : ws.getD q' 0 < init.length := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq', Option.getD_some]
        exact hfl ws[q'] (List.mem_cons_of_mem _ (List.getElem_mem hq'))
      rw [List.getD_append _ _ _ _ hflq, List.getD_append _ _ _ _ hns]
      rfl

def levelStep (h k base : ℕ) (flags : List ℕ) : List Gate × List ℕ :=
  let m := flags.length
  let g1 := andPivotGs k flags
  let tWires := (List.range m).map (fun q => base + q)
  let selP := orList (base + m) (2 ^ h) tWires
  let nselWire := base + m + selP.1.length
  let g3 := [⟨.not, [selP.2]⟩]
  let leftBase := nselWire + 1
  let g4 := leftGs nselWire flags
  let newFlags := (List.range m).flatMap (fun q => [leftBase + q, base + q])
  (g1 ++ selP.1 ++ g3 ++ g4, newFlags)

lemma flatMap_pair_len (m : ℕ) (f1 f2 : ℕ → ℕ) :
    ((List.range m).flatMap (fun q => [f1 q, f2 q])).length = 2 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp; omega

lemma flatMap_pair_getD (m : ℕ) (f1 f2 : ℕ → ℕ) (r : ℕ) (hr : r < 2 * m) :
    ((List.range m).flatMap (fun q => [f1 q, f2 q])).getD r 0 =
      if r % 2 = 0 then f1 (r / 2) else f2 (r / 2) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hlt : r < 2 * m
    · rw [List.getD_append _ _ _ _ (by rw [flatMap_pair_len]; exact hlt)]
      exact ih hlt
    · rw [List.getD_append_right _ _ _ _ (by rw [flatMap_pair_len]; omega)]
      rw [flatMap_pair_len]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hcases : r = 2 * m ∨ r = 2 * m + 1 := by omega
      rcases hcases with rfl | rfl
      · simp
      · have hsub : 2 * m + 1 - 2 * m = 1 := by omega
        have hmod : (2 * m + 1) % 2 = 1 := by omega
        have hdiv : (2 * m + 1) / 2 = m := by omega
        rw [hsub, hmod, hdiv]
        simp

lemma levelStep_len (h k base : ℕ) (flags : List ℕ) :
    (levelStep h k base flags).1.length ≤ 3 * flags.length + 1 ∧
    notCnt (levelStep h k base flags).1 = 1 ∧
    (levelStep h k base flags).2.length = 2 * flags.length := by
  unfold levelStep
  dsimp only
  have hl1 : (andPivotGs k flags).length = flags.length := andPivotGs_len k flags
  have hl2 : (orList (base + flags.length) (2 ^ h) ((List.range flags.length).map (fun q => base + q))).1.length ≤
      flags.length := by
    have := orList_len_le (base + flags.length) (2 ^ h) ((List.range flags.length).map (fun q => base + q))
    simpa using this
  refine ⟨by simp only [List.length_append, List.length_singleton, hl1, leftGs_len]; omega, ?_, ?_⟩
  · simp only [notCnt_append, andPivotGs_notCnt, orList_notCnt, leftGs_notCnt]
    rfl
  · exact flatMap_pair_len flags.length _ _

lemma levelStep_valid (h k base : ℕ) (flags : List ℕ) (hM : 2 ^ h < base)
    (hfl : ∀ w ∈ flags, w < base) (hflLen : flags.length * 2 ^ (k + 1) ≤ 2 ^ h) :
    validGs base (levelStep h k base flags).1 ∧
    ∀ w ∈ (levelStep h k base flags).2, w < base + (levelStep h k base flags).1.length := by
  unfold levelStep
  dsimp only
  set m := flags.length
  set g1 := andPivotGs k flags
  set tWires := (List.range m).map (fun q => base + q)
  set selP := orList (base + m) (2 ^ h) tWires
  set nselWire := base + m + selP.1.length
  set g3 : List Gate := [⟨.not, [selP.2]⟩]
  set leftBase := nselWire + 1
  set g4 := leftGs nselWire flags
  have hg1len : g1.length = m := andPivotGs_len k flags
  have hv1 : validGs base g1 := andPivotGs_valid h k base flags (by omega) hfl hflLen
  have htW : ∀ w ∈ tWires, w < base + m := by
    intro w hw; simp only [tWires, List.mem_map, List.mem_range] at hw
    obtain ⟨q, hq, rfl⟩ := hw; omega
  have hv2 : validGs (base + g1.length) selP.1 := by
    rw [hg1len]; exact orList_valid (base + m) (2 ^ h) tWires htW
  have hselOut : selP.2 < nselWire := by
    exact orList_out (base + m) (2 ^ h) tWires (by omega) htW
  have hv3 : validGs (base + (g1 ++ selP.1).length) g3 := by
    refine ⟨fun g hg => by simp [g3] at hg; subst hg; simp, fun j hj i hi => ?_⟩
    simp [g3] at hj; subst hj
    simp only [g3, List.getD_cons_zero, List.mem_singleton] at hi
    subst hi
    simp only [List.length_append, hg1len]; omega
  have hv4 : validGs (base + (g1 ++ selP.1 ++ g3).length) g4 := by
    have heq : base + (g1 ++ selP.1 ++ g3).length = leftBase := by
      simp only [List.length_append, List.length_singleton, g3, hg1len, leftBase, nselWire]; omega
    rw [heq]
    exact leftGs_valid nselWire leftBase flags (by omega) (fun w hw => by have := hfl w hw; omega)
  constructor
  · exact validGs_append (validGs_append (validGs_append hv1 hv2) hv3) hv4
  · intro w hw
    have hg4len : g4.length = m := leftGs_len nselWire flags
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hw
    obtain ⟨q, hq, rfl | rfl⟩ := hw
    · simp only [List.length_append, List.length_singleton, hg1len, hg4len, g3, leftBase, nselWire]
      omega
    · simp only [List.length_append, List.length_singleton, hg1len, hg4len, g3]
      omega

lemma levelStep_eval (h k : ℕ) (hk : k < h) (flags : List ℕ) (init : List Bool) (Y : Finset ℕ)
    (s : Fin (2 ^ h)) (hcell : cell h s Y)
    (hM : 2 ^ h < init.length) (hz : init.getD (2 ^ h) false = false)
    (hY : ∀ p < 2 ^ h, init.getD p false = decide (p ∈ Y))
    (hfl : ∀ w ∈ flags, w < init.length)
    (hflLen : flags.length * 2 ^ (k + 1) = 2 ^ h)
    (hinv : ∀ q < flags.length, init.getD (flags.getD q 0) false = decide (q = s.val / 2 ^ (k + 1))) :
    ∀ r < 2 * flags.length,
      (runW (levelStep h k init.length flags).1 init).getD ((levelStep h k init.length flags).2.getD r 0) false =
        decide (r = s.val / 2 ^ k) := by
  intro r hr
  unfold levelStep
  dsimp only
  set m := flags.length
  set base := init.length
  set g1 := andPivotGs k flags
  set tWires := (List.range m).map (fun q => base + q)
  set selP := orList (base + m) (2 ^ h) tWires
  set nselWire := base + m + selP.1.length
  set g3 : List Gate := [⟨.not, [selP.2]⟩]
  set leftBase := nselWire + 1
  set g4 := leftGs nselWire flags
  let w1 := runW g1 init
  let w2 := runW selP.1 w1
  let w3 := runW g3 w2
  let w4 := runW g4 w3
  have hw1len : w1.length = base + m := by simp [w1, runW_len, g1, andPivotGs_len, base, m]
  have hw2len : w2.length = nselWire := by simp [w2, runW_len, hw1len, nselWire]
  have hw3len : w3.length = leftBase := by simp [w3, runW_len, hw2len, g3, leftBase]
  have hrun : runW (g1 ++ selP.1 ++ g3 ++ g4) init = w4 := by
    simp only [w4, w3, w2, w1, runW_append]
  rw [hrun, flatMap_pair_getD m _ _ r hr]
  have hpivLt : ∀ q < m, (2 * q + 1) * 2 ^ k < 2 ^ h := by
    intro q hq
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : (2 * q + 1) * 2 ^ k < (q + 1) * 2 ^ (k + 1) := by
      rw [hpow]; nlinarith [Nat.pow_pos (a := 2) (n := k) (by decide)]
    have h2 : (q + 1) * 2 ^ (k + 1) ≤ m * 2 ^ (k + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have htq : ∀ q < m, w1.getD (base + q) false =
      (decide (q = s.val / 2 ^ (k + 1)) && decide ((2 * q + 1) * 2 ^ k ∈ Y)) := by
    intro q hq
    have hev := andPivotGs_eval_aux k 0 flags init hfl (fun i hi => by
      simp only [Nat.zero_add]; have := hpivLt i hi; omega) q hq
    simp only [Nat.zero_add] at hev
    dsimp only [w1, g1, andPivotGs, base]
    rw [hev, hinv q hq, hY _ (hpivLt q hq)]
  have hsdivLt : s.val / 2 ^ (k + 1) < m := by
    have : (s.val / 2 ^ (k + 1)) * 2 ^ (k + 1) ≤ s.val := Nat.div_mul_le_self _ _
    have hlt : (s.val / 2 ^ (k + 1)) * 2 ^ (k + 1) < m * 2 ^ (k + 1) := by omega
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hselBit : decide (pivot s.val k ∈ Y) = decide (s.val / 2 ^ k % 2 = 1) := by
    cases hb : decide (s.val / 2 ^ k % 2 = 1) with
    | true =>
      have hin : pivot s.val k ∈ Y := hcell.1 (by
        simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
        exact ⟨k, ⟨hk, hb⟩, rfl⟩)
      simp [hin]
    | false =>
      have hnot : pivot s.val k ∉ Y := Finset.disjoint_left.mp hcell.2 (by
        simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
        exact ⟨k, ⟨hk, hb⟩, rfl⟩)
      simp [hnot]
  have hselVal : w2.getD selP.2 false = decide (s.val / 2 ^ k % 2 = 1) := by
    have hev := orList_eval (2 ^ h) tWires w1
      (by rw [runW_old g1 init (2 ^ h) hM, hz])
      (fun w hw => by
        simp only [tWires, List.mem_map, List.mem_range] at hw
        obtain ⟨q, hq, rfl⟩ := hw; omega)
    rw [hw1len] at hev
    change w2.getD selP.2 false = _
    rw [hev, ← hselBit]
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨w, hw, hwt⟩
      simp only [tWires, List.mem_map, List.mem_range] at hw
      obtain ⟨q, hq, rfl⟩ := hw
      rw [htq q hq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwt
      obtain ⟨rfl, hin⟩ := hwt
      exact hin
    · intro hin
      refine ⟨base + s.val / 2 ^ (k + 1), ?_, ?_⟩
      · simp only [tWires, List.mem_map, List.mem_range]
        exact ⟨s.val / 2 ^ (k + 1), hsdivLt, rfl⟩
      · rw [htq _ hsdivLt, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨rfl, hin⟩
  have hnselVal : w3.getD nselWire false = decide (s.val / 2 ^ k % 2 = 0) := by
    have hstep : w3 = w2 ++ [!w2.getD selP.2 false] := by
      simp [w3, g3, runW, GateOp.eval]
    rw [hstep, ← hw2len, List.getD_append_right _ _ _ _ le_rfl]
    simp only [Nat.sub_self, List.getD_cons_zero, hselVal]
    cases hmod : s.val / 2 ^ k % 2 with
    | zero => rfl
    | succ n =>
      have : n = 0 := by omega
      subst this; rfl
  have hr2 : r / 2 < m := by omega
  have hdiv2 : (s.val / 2 ^ k) / 2 = s.val / 2 ^ (k + 1) := by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  by_cases heven : r % 2 = 0
  · simp only [heven, ite_true]
    have hfl3 : ∀ w ∈ flags, w < w3.length := fun w hw => by have := hfl w hw; omega
    have hev4 := leftGs_eval nselWire flags w3 (by omega) hfl3 (r / 2) hr2
    rw [hw3len] at hev4
    change w4.getD (leftBase + r / 2) false = _
    rw [hev4, hnselVal]
    have hflq : flags.getD (r / 2) 0 < base := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr2, Option.getD_some]
      exact hfl flags[r / 2] (List.getElem_mem hr2)
    have h3eq : w3.getD (flags.getD (r / 2) 0) false = init.getD (flags.getD (r / 2) 0) false := by
      rw [runW_old g3 w2 _ (by omega), runW_old selP.1 w1 _ (by omega), runW_old g1 init _ hflq]
    rw [h3eq, hinv (r / 2) hr2]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩; omega
    · intro h1; subst h1; exact ⟨hdiv2, heven⟩
  · simp only [heven, ite_false]
    have h4eq : w4.getD (base + r / 2) false = w1.getD (base + r / 2) false := by
      rw [runW_old g4 w3 _ (by omega), runW_old g3 w2 _ (by omega), runW_old selP.1 w1 _ (by omega)]
    rw [h4eq, htq (r / 2) hr2]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have hp : pivot s.val k ∈ Y := by unfold pivot; rw [← h1]; exact h2
      have hsb : s.val / 2 ^ k % 2 = 1 := by
        have := hselBit
        simp [hp] at this
        exact this
      omega
    · intro h1
      subst h1
      refine ⟨hdiv2, ?_⟩
      have hsb : s.val / 2 ^ k % 2 = 1 := by omega
      have := hselBit
      simp [hsb] at this
      unfold pivot at this
      rw [hdiv2]
      exact this

def buildTreeAux (h : ℕ) : ℕ → List Gate × List ℕ
  | 0 => ([], [2 ^ h + 1])
  | d + 1 =>
    let p := buildTreeAux h d
    let step := levelStep h (h - 1 - d) (2 ^ h + 2 + p.1.length) p.2
    (p.1 ++ step.1, step.2)

lemma buildTreeAux_props (h : ℕ) : ∀ d ≤ h,
    (buildTreeAux h d).2.length = 2 ^ d ∧
    notCnt (buildTreeAux h d).1 = d ∧
    (buildTreeAux h d).1.length ≤ 3 * (2 ^ d - 1) + d ∧
    validGs (2 ^ h + 2) (buildTreeAux h d).1 ∧
    (∀ w ∈ (buildTreeAux h d).2, w < 2 ^ h + 2 + (buildTreeAux h d).1.length) := by
  intro d
  induction d with
  | zero =>
    intro _
    simp only [buildTreeAux, Nat.pow_zero, List.length_singleton, List.length_nil, Nat.sub_self,
      Nat.mul_zero, Nat.add_zero, le_refl, true_and]
    refine ⟨rfl, validGs_nil _, fun w hw => by simp at hw; omega⟩
  | succ d ih =>
    intro hd
    obtain ⟨hlen, hnot, hsz, hval, hfl⟩ := ih (by omega)
    unfold buildTreeAux
    dsimp only
    set p := buildTreeAux h d
    set k := h - 1 - d
    set step := levelStep h k (2 ^ h + 2 + p.1.length) p.2
    have hstep : step = levelStep h k (2 ^ h + 2 + p.1.length) p.2 := rfl
    obtain ⟨hsLen, hsNot, hsFlen⟩ := levelStep_len h k (2 ^ h + 2 + p.1.length) p.2
    rw [← hstep] at hsLen hsNot hsFlen
    have hmul : p.2.length * 2 ^ (k + 1) = 2 ^ h := by
      rw [hlen, ← Nat.pow_add]; congr 1; omega
    obtain ⟨hvStep, hflStep⟩ := levelStep_valid h k (2 ^ h + 2 + p.1.length) p.2 (by omega) hfl (le_of_eq hmul)
    rw [← hstep] at hvStep hflStep
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hsFlen, hlen, Nat.pow_succ, Nat.mul_comm]
    · rw [notCnt_append, hnot, hsNot]
    · rw [List.length_append]
      have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
      have hpos : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
      omega
    · exact validGs_append hval (by simpa only [Nat.add_assoc] using hvStep)
    · intro w hw
      have := hflStep w hw
      rw [List.length_append]
      omega

lemma buildTreeAux_eval (h : ℕ) (Y : Finset ℕ) (s : Fin (2 ^ h)) (hcell : cell h s Y)
    (init : List Bool) (hinitLen : init.length = 2 ^ h + 2)
    (hinitZ : init.getD (2 ^ h) false = false) (hinitO : init.getD (2 ^ h + 1) false = true)
    (hinitY : ∀ p < 2 ^ h, init.getD p false = decide (p ∈ Y)) :
    ∀ d ≤ h, ∀ r < 2 ^ d,
      (runW (buildTreeAux h d).1 init).getD ((buildTreeAux h d).2.getD r 0) false =
        decide (r = s.val / 2 ^ (h - d)) := by
  intro d
  induction d with
  | zero =>
    intro _ r hr
    have hr0 : r = 0 := by simp at hr; exact hr
    subst hr0
    simp only [buildTreeAux, runW_nil, List.getD_cons_zero, Nat.sub_zero, hinitO]
    have hdiv : s.val / 2 ^ h = 0 := Nat.div_eq_of_lt s.isLt
    simp [hdiv]
  | succ d ih =>
    intro hd r hr
    obtain ⟨hlen, _, _, _, hfl⟩ := buildTreeAux_props h d (by omega)
    unfold buildTreeAux
    dsimp only
    set p := buildTreeAux h d
    set k := h - 1 - d
    set w0 := runW p.1 init
    have hw0len : w0.length = 2 ^ h + 2 + p.1.length := by rw [runW_len, hinitLen]
    rw [runW_append]
    change (runW (levelStep h k (2 ^ h + 2 + p.1.length) p.2).1 w0).getD
      ((levelStep h k (2 ^ h + 2 + p.1.length) p.2).2.getD r 0) false = _
    rw [← hw0len]
    have hmul : p.2.length * 2 ^ (k + 1) = 2 ^ h := by
      rw [hlen, ← Nat.pow_add]; congr 1; omega
    have hr' : r < 2 * p.2.length := by rw [hlen, ← Nat.mul_comm, ← Nat.pow_succ]; exact hr
    have hk1 : k + 1 = h - d := by omega
    have hres := levelStep_eval h k (by omega) p.2 w0 Y s hcell (by omega)
      (by rw [runW_old p.1 init (2 ^ h) (by omega), hinitZ])
      (fun x hx => by rw [runW_old p.1 init x (by omega), hinitY x hx])
      (fun w hw => by rw [hw0len]; exact hfl w hw)
      hmul
      (fun q hq => by rw [hk1]; exact ih (by omega) q (by omega))
      r hr'
    have hkeq : h - (d + 1) = k := by omega
    rw [hkeq]
    exact hres

lemma part4 (h : ℕ) (f : Fin (2 ^ h) → Bool) :
    let bits := fun (r : ℕ) (Y : Finset ℕ) => List.ofFn (fun j : Fin r => decide (j.val ∈ Y)) ++ [false, true]
    ∃ D : Circuit,
      (FanInTwo D ∧ ReadsBack (2 ^ h + 2) D ∧ D.output < 2 ^ h + 2 + D.size) ∧
      notCount D ≤ h ∧ D.size - notCount D ≤ 6 * 2 ^ h ∧
      ∀ Y ⊆ Finset.range (2 ^ h), ∀ s : Fin (2 ^ h), cell h s Y → D.eval (bits (2 ^ h) Y) = f s := by
  intro bits
  let M := 2 ^ h
  let tree := buildTreeAux h h
  obtain ⟨hlen, hnot, hsz, hval, hfl⟩ := buildTreeAux_props h h le_rfl
  let selLeaves : List ℕ :=
    (List.finRange M).filterMap (fun i => if f i then some (tree.2.getD i.val 0) else none)
  have hselLen : selLeaves.length ≤ M := by
    calc selLeaves.length ≤ (List.finRange M).length := List.length_filterMap_le _ _
      _ = M := List.length_finRange
  have hselLt : ∀ w ∈ selLeaves, w < M + 2 + tree.1.length := by
    intro w hw
    simp only [selLeaves, List.mem_filterMap] at hw
    obtain ⟨i, _, hi⟩ := hw
    split at hi
    · injection hi with hEq
      subst hEq
      have hiLt : i.val < tree.2.length := by rw [hlen]; exact i.isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiLt, Option.getD_some]
      exact hfl tree.2[i.val] (List.getElem_mem hiLt)
    · contradiction
  let outP := orList (M + 2 + tree.1.length) M selLeaves
  let D : Circuit := ⟨tree.1 ++ outP.1, outP.2⟩
  have hDval : validGs (M + 2) D.gates :=
    validGs_append hval (orList_valid (M + 2 + tree.1.length) M selLeaves hselLt)
  have hDnot : notCount D = h := by
    change notCnt (tree.1 ++ outP.1) = h
    rw [notCnt_append, hnot, orList_notCnt, Nat.add_zero]
  have hDout : D.output < M + 2 + D.size := by
    have hout : outP.2 < M + 2 + tree.1.length + outP.1.length :=
      orList_out (M + 2 + tree.1.length) M selLeaves (by omega) hselLt
    change outP.2 < M + 2 + (tree.1 ++ outP.1).length
    rw [List.length_append]
    omega
  have hDsz : D.size - notCount D ≤ 6 * M := by
    rw [hDnot]
    have ho : outP.1.length ≤ M := le_trans (orList_len_le _ _ _) hselLen
    have ht : tree.1.length ≤ 3 * (2 ^ h - 1) + h := hsz
    change (tree.1 ++ outP.1).length - h ≤ 6 * M
    rw [List.length_append]
    omega
  refine ⟨D, ⟨hDval.1, hDval.2, hDout⟩, le_of_eq hDnot, hDsz, fun Y _ s hcell => ?_⟩
  let init := bits M Y
  have hinitLen : init.length = M + 2 := by simp [init, bits]
  have hinitZ : init.getD M false = false := by
    simp [init, bits]
  have hinitO : init.getD (M + 1) false = true := by
    have h1 : (List.ofFn (fun j : Fin M => decide (j.val ∈ Y))).length = M := by simp
    simp only [init, bits]
    rw [List.getD_append_right _ _ _ _ (by omega), h1]
    have : M + 1 - M = 1 := by omega
    rw [this]; rfl
  have hinitY : ∀ p < M, init.getD p false = decide (p ∈ Y) := by
    intro p hp
    simp only [init, bits]
    rw [List.getD_append _ _ _ _ (by simp [hp])]
    simp [List.getD_eq_getElem?_getD, hp]
  have htreeEv := buildTreeAux_eval h Y s hcell init hinitLen hinitZ hinitO hinitY h le_rfl
  let wTree := runW tree.1 init
  have hwTreeLen : wTree.length = M + 2 + tree.1.length := by rw [runW_len, hinitLen]
  rw [eval_eq_runW]
  change (runW (tree.1 ++ outP.1) init).getD outP.2 false = f s
  rw [runW_append]
  have hevOut := orList_eval M selLeaves wTree
    (by rw [runW_old tree.1 init M (by omega), hinitZ])
    (fun w hw => by rw [hwTreeLen]; exact hselLt w hw)
  rw [hwTreeLen] at hevOut
  rw [hevOut]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨w, hw, hwt⟩
    simp only [selLeaves, List.mem_filterMap] at hw
    obtain ⟨i, _, hi⟩ := hw
    cases hfi : f i with
    | false => simp [hfi] at hi
    | true =>
      simp only [hfi, ite_true, Option.some.injEq] at hi
      subst hi
      have h1 := htreeEv i.val i.isLt
      simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one] at h1
      rw [h1, decide_eq_true_eq] at hwt
      have his : i = s := Fin.ext hwt
      rw [← his, hfi]
  · intro hfs
    refine ⟨tree.2.getD s.val 0, ?_, ?_⟩
    · simp only [selLeaves, List.mem_filterMap]
      exact ⟨s, List.mem_finRange s, by simp [hfs]⟩
    · have h1 := htreeEv s.val s.isLt
      simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one, decide_true] at h1
      exact h1

end PEqualNP.Outside.L_lib_1435_aux.Tree

namespace PEqualNP.Outside.L_lib_1435_aux.Cells

def piv (s j : ℕ) : ℕ := (2*(s/(2^(j+1)))+1)*2^j

theorem div_split (s J : ℕ) : s/2^J = 2*(s/2^(J+1)) + s/2^J%2 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega

theorem piv_le (s J : ℕ) (h : s/2^J%2 = 1) : 1 ≤ piv s J ∧ piv s J ≤ s := by
  have h1 := div_split s J
  have h3 : 2*(s/2^(J+1))+1 = s/2^J := by omega
  unfold piv; rw [h3]
  have h4 : 1 ≤ s/2^J := by omega
  exact ⟨Nat.mul_pos h4 (Nat.two_pow_pos J), Nat.div_mul_le_self s (2^J)⟩

theorem piv_gt (s J : ℕ) (h : ¬ s/2^J%2 = 1) : s < piv s J := by
  have h1 := div_split s J
  have h3 : 2*(s/2^(J+1))+1 = s/2^J + 1 := by omega
  unfold piv; rw [h3]
  have e1 := Nat.div_add_mod s (2^J)
  have e2 := Nat.mod_lt s (Nat.two_pow_pos J)
  nlinarith

theorem piv_lt (a s J : ℕ) (hs : s < 4*2^a) (hJ : J < a+2) : piv s J < 4*2^a := by
  obtain ⟨c, hc⟩ : ∃ c, a + 1 = J + c := ⟨a+1-J, by omega⟩
  have hM : 4*2^a = 2^(J+1) * 2^c := by
    rw [← pow_add]
    have : J+1+c = a+2 := by omega
    rw [this]; ring
  have hq : s/2^(J+1) < 2^c := Nat.div_lt_of_lt_mul (by rw [← hM]; exact hs)
  have h5 : (s/2^(J+1) + 1) * 2^J ≤ 2^c * 2^J := Nat.mul_le_mul_right _ hq
  have h6 : (2:ℕ)^(J+1) = 2*2^J := by ring
  have hp := Nat.two_pow_pos J
  have hM' : 4*2^a = 2*(2^c*2^J) := by rw [hM, h6]; ring
  unfold piv
  rw [hM']
  generalize s/2^(J+1) = q at *
  nlinarith

theorem piv_aux (q q' J c : ℕ) : (2*q+1)*2^J ≠ (2*q'+1)*2^(J+c+1) := by
  intro h
  have e : (2*q'+1)*2^(J+c+1) = (2*((2*q'+1)*2^c))*2^J := by ring
  rw [e] at h
  have := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos J) h
  omega

theorem piv_inj (s J J' : ℕ) (h : piv s J = piv s J') : J = J' := by
  unfold piv at h
  rcases lt_trichotomy J J' with h1 | h1 | h1
  · obtain ⟨c, rfl⟩ : ∃ c, J' = J + c + 1 := ⟨J' - J - 1, by omega⟩
    exact (piv_aux _ _ _ _ h).elim
  · exact h1
  · obtain ⟨c, rfl⟩ : ∃ c, J = J' + c + 1 := ⟨J - J' - 1, by omega⟩
    exact (piv_aux _ _ _ _ h.symm).elim

theorem bitsplit (n s t : ℕ) (hst : s < t) (ht : t < 2^(n+1)) :
    ∃ J, J ≤ n ∧ s/2^(J+1) = t/2^(J+1) ∧ ¬ s/2^J%2 = 1 ∧ t/2^J%2 = 1 := by
  have hn : s/2^(n+1) = t/2^(n+1) := by
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt ht]
  have hex : ∃ J, s/2^(J+1) = t/2^(J+1) := ⟨n, hn⟩
  classical
  obtain ⟨J, hJn, hJ, hmin⟩ : ∃ J, J ≤ n ∧ s/2^(J+1) = t/2^(J+1) ∧ ∀ m < J, ¬ s/2^(m+1) = t/2^(m+1) :=
    ⟨Nat.find hex, Nat.find_min' hex hn, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hne : s/2^J ≠ t/2^J := by
    cases J with
    | zero => intro h; simp at h; omega
    | succ m => exact hmin m (by omega)
  have hle : s/2^J ≤ t/2^J := Nat.div_le_div_right (by omega)
  have := div_split s J
  have := div_split t J
  refine ⟨J, hJn, hJ, ?_, ?_⟩ <;> omega

theorem dec_iff (p : Prop) [Decidable p] (v : Bool) : decide p = v ↔ (p ↔ v = true) := by
  cases v <;> simp

def PM (a d e : ℕ) (L : Fin (4*2^a) → Fin 3 → Fin e × Bool) (s : Fin (4*2^a)) (j : Fin 3)
    (v : Bool) (x : ℕ) : Prop :=
  (∃ o c, (s.val < 2*2^a ∧ o = 0 ∨ ¬ s.val < 2*2^a ∧ o = 2*e) ∧
      ((L s j).2 = v ∧ c = 1 ∨ (L s j).2 ≠ v ∧ c = 0) ∧ x = d + o + 2*(L s j).1.val + c)
  ∨ (((L s j).1.val < d ∧ (L s j).2 = true ∧ (s.val < 2*2^a ↔ v = true)) ∧ x = (L s j).1.val)
  ∨ (∃ k, k < 2 ∧ (j.val/2^k % 2 = 1 ↔ v = true) ∧ x = d+4*e+2*s.val+k)
  ∨ (∃ jj, jj < a+2 ∧ (s.val/2^jj % 2 = 1 ↔ v = true) ∧ x = d+4*e+2*(4*2^a) + piv s.val jj)

def CM (a d e : ℕ) (X : Finset ℕ) (x : ℕ) : Prop :=
  x ∈ X ∨ (d ≤ x ∧ x < d+2*e) ∨ (d+4*e ≤ x ∧ x < d+4*e+4*2^a) ∨
    ∃ j, 1 ≤ j ∧ j ≤ 2*2^a-1 ∧ x = d+4*e+2*(4*2^a)+j

theorem P_range {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (s : Fin (4*2^a)) (j : Fin 3) (v : Bool)
    (x : ℕ) (hx : x ∈ pins s j v) : x < d+4*e+2*(4*2^a)+4*2^a := by
  have hs := s.isLt
  have hi := (L s j).1.isLt
  have hpos := Nat.two_pow_pos a
  rcases (hp s j v x).1 hx with ⟨o, c, ho, hc, rfl⟩ | ⟨⟨h1, -, -⟩, rfl⟩ | ⟨k, hk, -, rfl⟩ | ⟨jj, hjj, -, rfl⟩
  · have ho2 : o ≤ 2*e := by rcases ho with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    have hc2 : c ≤ 1 := by rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    omega
  · omega
  · omega
  · have := piv_lt a s.val jj hs hjj; omega

theorem cut_range {a d e : ℕ} {X : Finset ℕ} (hXd : X ⊆ Finset.range d) (x : ℕ)
    (h : CM a d e X x) : x < d+4*e+2*(4*2^a)+4*2^a := by
  have hpos := Nat.two_pow_pos a
  rcases h with h | h | h | ⟨q, h1, h2, h3⟩
  · have := Finset.mem_range.1 (hXd h); omega
  · omega
  · omega
  · omega

theorem NP_disj {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (s t : Fin (4*2^a)) (j k : Fin 3)
    (hts : t ≤ s) (hside : s.val < 2*2^a ↔ t.val < 2*2^a) (hjk : s = t → j = k)
    (hw : (L s j).1 = (L t k).1 → (L s j).2 = (L t k).2) (x : ℕ)
    (hN : x ∈ pins s j false) (hP : x ∈ pins t k true) : False := by
  have hs := s.isLt
  have ht := t.isLt
  have hi := (L s j).1.isLt
  have hi' := (L t k).1.isLt
  have hts' : t.val ≤ s.val := hts
  rcases (hp s j false x).1 hN with ⟨o, c, ho, hc, rfl⟩ | ⟨⟨h1, h2, h3⟩, rfl⟩ | ⟨k1, hk1, hb1, rfl⟩ | ⟨j1, hj1, hb1, rfl⟩
  · have ho2 : o ≤ 2*e := by rcases ho with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    have hc2 : c ≤ 1 := by rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    rcases (hp t k true _).1 hP with ⟨o', c', ho', hc', h⟩ | ⟨⟨h1', h2', h3'⟩, h⟩ | ⟨k2, hk2, hb2, h⟩ | ⟨j2, hj2, hb2, h⟩
    · have hc2' : c' ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
      have hoo : o = o' := by omega
      have hii : (L s j).1 = (L t k).1 := Fin.ext (by omega)
      have hbb := hw hii
      have hcc : c = c' := by omega
      rcases hc with ⟨hc1, rfl⟩ | ⟨hc1, rfl⟩ <;> rcases hc' with ⟨hc3, rfl⟩ | ⟨hc3, rfl⟩ <;> simp_all
    · omega
    · omega
    · omega
  · rcases (hp t k true _).1 hP with ⟨o', c', ho', hc', h⟩ | ⟨⟨h1', h2', h3'⟩, h⟩ | ⟨k2, hk2, hb2, h⟩ | ⟨j2, hj2, hb2, h⟩
    · omega
    · have a1 : ¬ s.val < 2*2^a := fun hh => Bool.false_ne_true (h3.1 hh)
      exact a1 (hside.2 (h3'.2 rfl))
    · omega
    · omega
  · rcases (hp t k true _).1 hP with ⟨o', c', ho', hc', h⟩ | ⟨⟨h1', h2', h3'⟩, h⟩ | ⟨k2, hk2, hb2, h⟩ | ⟨j2, hj2, hb2, h⟩
    · have ho2 : o' ≤ 2*e := by rcases ho' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
      have hc2' : c' ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
      omega
    · omega
    · have hst : s = t := Fin.ext (by omega)
      have hkk : k1 = k2 := by omega
      have := hjk hst
      subst hst; subst hkk; subst this
      exact Bool.false_ne_true (hb1.1 (hb2.2 rfl))
    · omega
  · have g1 := piv_gt s.val j1 (fun hh => Bool.false_ne_true (hb1.1 hh))
    rcases (hp t k true _).1 hP with ⟨o', c', ho', hc', h⟩ | ⟨⟨h1', h2', h3'⟩, h⟩ | ⟨k2, hk2, hb2, h⟩ | ⟨j2, hj2, hb2, h⟩
    · have ho2 : o' ≤ 2*e := by rcases ho' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
      have hc2' : c' ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
      omega
    · omega
    · omega
    · have g2 := piv_le t.val j2 (hb2.2 rfl)
      omega

theorem consist {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    (Y : Fin (4*2^a) → Finset ℕ) (hY : Monotone Y) (s t : Fin (4*2^a)) (j k : Fin 3) (hst : s ≤ t)
    (hside : s.val < 2*2^a ↔ t.val < 2*2^a) (hPs : pins s j true ⊆ Y s)
    (hNt : Disjoint (pins t k false) (Y t)) (hi : (L s j).1 = (L t k).1) :
    (L s j).2 = (L t k).2 := by
  by_contra hne
  obtain ⟨o, ho⟩ : ∃ o, (s.val < 2*2^a ∧ o = 0 ∨ ¬ s.val < 2*2^a ∧ o = 2*e) := by
    by_cases h : s.val < 2*2^a
    · exact ⟨0, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨2*e, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨c, hc⟩ : ∃ c, ((L s j).2 = true ∧ c = 1 ∨ (L s j).2 ≠ true ∧ c = 0) := by
    cases (L s j).2 <;> simp
  have m1 : d + o + 2*(L s j).1.val + c ∈ pins s j true := (hp _ _ _ _).2 (Or.inl ⟨o, c, ho, hc, rfl⟩)
  have ho' : (t.val < 2*2^a ∧ o = 0 ∨ ¬ t.val < 2*2^a ∧ o = 2*e) := by
    rcases ho with ⟨h, e1⟩ | ⟨h, e1⟩
    · exact Or.inl ⟨hside.1 h, e1⟩
    · exact Or.inr ⟨fun h' => h (hside.2 h'), e1⟩
  have hc' : ((L t k).2 = false ∧ c = 1 ∨ (L t k).2 ≠ false ∧ c = 0) := by
    revert hc hne
    cases (L s j).2 <;> cases (L t k).2 <;> simp
  have m2 : d + o + 2*(L s j).1.val + c ∈ pins t k false :=
    (hp _ _ _ _).2 (Or.inl ⟨o, c, ho', hc', by rw [hi]⟩)
  exact Finset.disjoint_left.1 hNt m2 (hY hst (hPs m1))

theorem P_sub_cut {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (X : Finset ℕ) (s : Fin (4*2^a)) (j : Fin 3)
    (hs : s.val < 2*2^a)
    (hpub : (L s j).1.val < d → (L s j).2 = true → (L s j).1.val ∈ X) (x : ℕ)
    (hx : x ∈ pins s j true) : CM a d e X x := by
  have hi := (L s j).1.isLt
  rcases (hp s j true x).1 hx with ⟨o, c, ho, hc, rfl⟩ | ⟨⟨h1, h2, -⟩, rfl⟩ | ⟨k, hk, -, rfl⟩ | ⟨jj, hjj, hb, rfl⟩
  · have ho2 : o = 0 := by omega
    have hc2 : c ≤ 1 := by rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    exact Or.inr (Or.inl (by omega))
  · exact Or.inl (hpub h1 h2)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · have := piv_le s.val jj (hb.2 rfl)
    exact Or.inr (Or.inr (Or.inr ⟨_, this.1, by omega, rfl⟩))

theorem N_miss_cut {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (X : Finset ℕ) (hX : X ⊆ Finset.range d)
    (s : Fin (4*2^a)) (j : Fin 3) (hs : ¬ s.val < 2*2^a)
    (hpub : (L s j).1.val < d → (L s j).2 = true → (L s j).1.val ∉ X) (x : ℕ)
    (hx : x ∈ pins s j false) (hc : CM a d e X x) : False := by
  have hi := (L s j).1.isLt
  have hsl := s.isLt
  have hXd : ∀ y, y ∈ X → y < d := fun y h => Finset.mem_range.1 (hX h)
  rcases (hp s j false x).1 hx with ⟨o, c, ho, hc', rfl⟩ | ⟨⟨h1, h2, -⟩, rfl⟩ | ⟨k, hk, -, rfl⟩ | ⟨jj, hjj, hb, rfl⟩
  · have ho2 : o = 2*e := by omega
    have hc2 : c ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    rcases hc with h | h | h | ⟨q, _, _, h⟩
    · have := hXd _ h; omega
    · omega
    · omega
    · omega
  · rcases hc with h | h | h | ⟨q, _, _, h⟩
    · exact hpub h1 h2 h
    · omega
    · omega
    · omega
  · rcases hc with h | h | h | ⟨q, _, _, h⟩
    · have := hXd _ h; omega
    · omega
    · omega
    · omega
  · have := piv_gt s.val jj (fun hh => Bool.false_ne_true (hb.1 hh))
    rcases hc with h | h | h | ⟨q, _, _, h⟩
    · have := hXd _ h; omega
    · omega
    · omega
    · omega

theorem sat_of_chain {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3) (hY : Monotone Y)
    (S : Fin (4*2^a) → Prop) (hS : ∀ s t, S s → S t → (s.val < 2*2^a ↔ t.val < 2*2^a))
    (h : ∀ s, S s → pins s (v s) true ⊆ Y s ∧ Disjoint (pins s (v s) false) (Y s)) :
    ∃ w : Fin e → Bool, (∀ s, S s → w (L s (v s)).1 = (L s (v s)).2) ∧
      ∀ i, w i = true → ∃ s, S s ∧ L s (v s) = (i, true) := by
  classical
  refine ⟨fun i => decide (∃ s, S s ∧ L s (v s) = (i, true)), ?_, ?_⟩
  · intro s hs
    by_cases hb : (L s (v s)).2 = true
    · rw [hb, decide_eq_true_eq]; exact ⟨s, hs, Prod.ext rfl hb⟩
    · have hb0 : (L s (v s)).2 = false := by simpa using hb
      rw [hb0, decide_eq_false_iff_not]
      rintro ⟨t, ht, hLt⟩
      have hi : (L s (v s)).1 = (L t (v t)).1 := by rw [hLt]
      have hb' : (L t (v t)).2 = true := by rw [hLt]
      have : (L s (v s)).2 = (L t (v t)).2 := by
        rcases le_total s t with hst | hst
        · exact consist hp Y hY s t _ _ hst (hS s t hs ht) (h s hs).1 (h t ht).2 hi
        · exact (consist hp Y hY t s _ _ hst (hS t s ht hs) (h t ht).1 (h s hs).2 hi.symm).symm
      rw [hb0, hb'] at this; exact Bool.false_ne_true this
  · intro i hi; simpa using hi

theorem chainT_pos {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    {cut : Finset ℕ → Finset ℕ} (hc : ∀ X x, x ∈ cut X ↔ CM a d e X x) (X : Finset ℕ)
    (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3) (hY : Monotone Y)
    (h : ∀ s : Fin (4*2^a), s.val < 2*2^a →
      (Y s ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧ pins s (v s) true ⊆ Y s ∧
        Disjoint (pins s (v s) false) (Y s)) ∧ Y s ⊆ cut X) :
    ∃ w : Fin e → Bool, (∀ s : Fin (4*2^a), s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2) ∧
      ∀ i : Fin e, i.val < d → w i = true → i.val ∈ X := by
  obtain ⟨w, hw1, hw2⟩ := sat_of_chain hp Y v hY (fun s => s.val < 2*2^a)
    (fun s t hs ht => ⟨fun _ => ht, fun _ => hs⟩) (fun s hs => ⟨(h s hs).1.2.1, (h s hs).1.2.2⟩)
  refine ⟨w, fun s hs => ⟨v s, hw1 s hs⟩, fun i hid hwi => ?_⟩
  obtain ⟨s, hs, hL⟩ := hw2 i hwi
  have hm : i.val ∈ pins s (v s) true :=
    (hp _ _ _ _).2 (Or.inr (Or.inl ⟨⟨by rw [hL]; exact hid, by rw [hL], ⟨fun _ => rfl, fun _ => hs⟩⟩, by rw [hL]⟩))
  rcases (hc X _).1 ((h s hs).2 ((h s hs).1.2.1 hm)) with h2 | h2 | h2 | ⟨q, _, _, h2⟩
  · exact h2
  · omega
  · omega
  · omega

theorem chainF_neg {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    {cut : Finset ℕ → Finset ℕ} (hc : ∀ X x, x ∈ cut X ↔ CM a d e X x) (X : Finset ℕ)
    (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3) (hY : Monotone Y)
    (h : ∀ s : Fin (4*2^a), ¬ s.val < 2*2^a →
      (Y s ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧ pins s (v s) true ⊆ Y s ∧
        Disjoint (pins s (v s) false) (Y s)) ∧ cut X ⊆ Y s) :
    ∃ w : Fin e → Bool, (∀ s : Fin (4*2^a), ¬ s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2) ∧
      ∀ i : Fin e, i.val < d → w i = true → i.val ∉ X := by
  obtain ⟨w, hw1, hw2⟩ := sat_of_chain hp Y v hY (fun s => ¬ s.val < 2*2^a)
    (fun s t hs ht => ⟨fun h => absurd h hs, fun h => absurd h ht⟩)
    (fun s hs => ⟨(h s hs).1.2.1, (h s hs).1.2.2⟩)
  refine ⟨w, fun s hs => ⟨v s, hw1 s hs⟩, fun i hid hwi hiX => ?_⟩
  obtain ⟨s, hs, hL⟩ := hw2 i hwi
  have hm : i.val ∈ pins s (v s) false :=
    (hp _ _ _ _).2 (Or.inr (Or.inl ⟨⟨by rw [hL]; exact hid, by rw [hL],
      ⟨fun h => absurd h hs, fun h => absurd h Bool.false_ne_true⟩⟩, by rw [hL]⟩))
  exact Finset.disjoint_left.1 (h s hs).1.2.2 hm ((h s hs).2 ((hc X _).2 (Or.inl hiX)))

theorem pos_chainT {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    {cut : Finset ℕ → Finset ℕ} (hc : ∀ X x, x ∈ cut X ↔ CM a d e X x) (X : Finset ℕ)
    (hXd : X ⊆ Finset.range d) (w : Fin e → Bool)
    (hsat : ∀ s : Fin (4*2^a), s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2)
    (hX : ∀ i : Fin e, i.val < d → w i = true → i.val ∈ X) :
    ∃ (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3), Monotone Y ∧
      ∀ s : Fin (4*2^a), s.val < 2*2^a →
      (Y s ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧ pins s (v s) true ⊆ Y s ∧
        Disjoint (pins s (v s) false) (Y s)) ∧ Y s ⊆ cut X := by
  classical
  choose! v hv using hsat
  refine ⟨fun s => (cut X).filter (fun x => ∃ t, t ≤ s ∧ t.val < 2*2^a ∧ x ∈ pins t (v t) true), v, ?_, ?_⟩
  · intro s s' hss x hx
    simp only [Finset.mem_filter] at hx ⊢
    obtain ⟨hx1, t, ht, ht2, hx2⟩ := hx
    exact ⟨hx1, t, le_trans ht hss, ht2, hx2⟩
  · intro s hs
    refine ⟨⟨?_, ?_, ?_⟩, Finset.filter_subset _ _⟩
    · intro x hx
      exact Finset.mem_range.2 (cut_range hXd x ((hc X x).1 (Finset.mem_filter.1 hx).1))
    · intro x hx
      exact Finset.mem_filter.2 ⟨(hc X x).2 (P_sub_cut hp X s (v s) hs
        (fun h1 h2 => hX _ h1 (by rw [hv s hs]; exact h2)) x hx), s, le_refl s, hs, hx⟩
    · rw [Finset.disjoint_left]
      intro x hxN hxY
      obtain ⟨-, t, ht, ht2, hxP⟩ := Finset.mem_filter.1 hxY
      exact NP_disj hp s t (v s) (v t) ht ⟨fun _ => ht2, fun _ => hs⟩ (fun hst => by rw [hst])
        (fun hi => by rw [← hv s hs, ← hv t ht2, hi]) x hxN hxP

theorem neg_chainF {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    {cut : Finset ℕ → Finset ℕ} (hc : ∀ X x, x ∈ cut X ↔ CM a d e X x) (X : Finset ℕ)
    (hXd : X ⊆ Finset.range d) (w : Fin e → Bool)
    (hsat : ∀ s : Fin (4*2^a), ¬ s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2)
    (hX : ∀ i : Fin e, i.val < d → w i = true → i.val ∉ X) :
    ∃ (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3), Monotone Y ∧
      ∀ s : Fin (4*2^a), ¬ s.val < 2*2^a →
      (Y s ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧ pins s (v s) true ⊆ Y s ∧
        Disjoint (pins s (v s) false) (Y s)) ∧ cut X ⊆ Y s := by
  classical
  choose! v hv using hsat
  refine ⟨fun s => (Finset.range (d+4*e+2*(4*2^a)+4*2^a)).filter
    (fun x => x ∈ cut X ∨ ∃ t, t ≤ s ∧ ¬ t.val < 2*2^a ∧ x ∈ pins t (v t) true), v, ?_, ?_⟩
  · intro s s' hss x hx
    simp only [Finset.mem_filter] at hx ⊢
    obtain ⟨hx1, hx2 | ⟨t, ht, ht2, hx2⟩⟩ := hx
    · exact ⟨hx1, Or.inl hx2⟩
    · exact ⟨hx1, Or.inr ⟨t, le_trans ht hss, ht2, hx2⟩⟩
  · intro s hs
    refine ⟨⟨Finset.filter_subset _ _, ?_, ?_⟩, ?_⟩
    · intro x hx
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (P_range hp s (v s) true x hx),
        Or.inr ⟨s, le_refl s, hs, hx⟩⟩
    · rw [Finset.disjoint_left]
      intro x hxN hxY
      rcases (Finset.mem_filter.1 hxY).2 with hcut | ⟨t, ht, ht2, hxP⟩
      · exact N_miss_cut hp X hXd s (v s) hs (fun h1 h2 => hX _ h1 (by rw [hv s hs]; exact h2))
          x hxN ((hc X x).1 hcut)
      · exact NP_disj hp s t (v s) (v t) ht ⟨fun h => absurd h hs, fun h => absurd h ht2⟩
          (fun hst => by rw [hst]) (fun hi => by rw [← hv s hs, ← hv t ht2, hi]) x hxN hxP
    · intro x hx
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (cut_range hXd x ((hc X x).1 hx)), Or.inl hx⟩

theorem conj2 {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (s t : Fin (4*2^a)) (j k : Fin 3)
    (Y : Finset ℕ) (h1 : pins s j true ⊆ Y) (h1' : Disjoint (pins s j false) Y)
    (h2 : pins t k true ⊆ Y) (h2' : Disjoint (pins t k false) Y) : s = t ∧ j = k := by
  have key : ∀ (s t : Fin (4*2^a)) (j k : Fin 3), s.val < t.val → pins t k true ⊆ Y →
      Disjoint (pins s j false) Y → False := by
    intro s t j k hlt hP hN
    obtain ⟨J, hJ, hq, hbs, hbt⟩ := bitsplit (a+1) s.val t.val hlt
      (by have := t.isLt; rw [pow_succ, pow_succ]; omega)
    have hpiv : piv s.val J = piv t.val J := by unfold piv; rw [hq]
    have m1 : (d+4*e+2*(4*2^a) + piv s.val J) ∈ pins t k true :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inr ⟨J, by omega, ⟨fun _ => rfl, fun _ => hbt⟩, by rw [hpiv]⟩)))
    have m2 : (d+4*e+2*(4*2^a) + piv s.val J) ∈ pins s j false :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inr ⟨J, by omega,
        ⟨fun h => absurd h hbs, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
    exact Finset.disjoint_left.1 hN m2 (hP m1)
  have hst : s = t := by
    rcases lt_trichotomy s.val t.val with h | h | h
    · exact (key s t j k h h2 h1').elim
    · exact Fin.ext h
    · exact (key t s k j h h1 h2').elim
  subst hst
  refine ⟨rfl, ?_⟩
  by_contra hjk
  have hbits : ∀ j k : Fin 3, j ≠ k → ∃ k0 : Fin 2, ((j.val/2^k0.val % 2 = 1 ∧ ¬ k.val/2^k0.val % 2 = 1) ∨
      (k.val/2^k0.val % 2 = 1 ∧ ¬ j.val/2^k0.val % 2 = 1)) := by decide
  obtain ⟨k0, hh | hh⟩ := hbits j k hjk
  · have m1 : d+4*e+2*s.val+k0.val ∈ pins s j true :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inl ⟨k0.val, k0.isLt, ⟨fun _ => rfl, fun _ => hh.1⟩, rfl⟩)))
    have m2 : d+4*e+2*s.val+k0.val ∈ pins s k false :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inl ⟨k0.val, k0.isLt,
        ⟨fun h => absurd h hh.2, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
    exact Finset.disjoint_left.1 h2' m2 (h1 m1)
  · have m1 : d+4*e+2*s.val+k0.val ∈ pins s k true :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inl ⟨k0.val, k0.isLt, ⟨fun _ => rfl, fun _ => hh.1⟩, rfl⟩)))
    have m2 : d+4*e+2*s.val+k0.val ∈ pins s j false :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inl ⟨k0.val, k0.isLt,
        ⟨fun h => absurd h hh.2, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
    exact Finset.disjoint_left.1 h1' m2 (h2 m1)

theorem conj4 {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    {cut : Finset ℕ → Finset ℕ} (hc : ∀ X x, x ∈ cut X ↔ CM a d e X x) :
    (∃ (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3), Monotone Y ∧
      ∀ s : Fin (4*2^a), (Y s ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧ pins s (v s) true ⊆ Y s ∧
        Disjoint (pins s (v s) false) (Y s))) ↔
    ∃ X : Finset ℕ, X ⊆ Finset.range d ∧
      (∃ w : Fin e → Bool, (∀ s : Fin (4*2^a), s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2) ∧
        ∀ i : Fin e, i.val < d → w i = true → i.val ∈ X) ∧
      (∃ w : Fin e → Bool, (∀ s : Fin (4*2^a), ¬ s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2) ∧
        ∀ i : Fin e, i.val < d → w i = true → i.val ∉ X) := by
  classical
  have hpos := Nat.two_pow_pos a
  constructor
  · rintro ⟨Y, v, hY, h⟩
    have h2H : 2*2^a - 1 < 4*2^a := by omega
    let m : Fin (4*2^a) := ⟨2*2^a-1, h2H⟩
    let X : Finset ℕ := (Finset.range d).filter (fun x => x ∈ Y m)
    have hXd : X ⊆ Finset.range d := Finset.filter_subset _ _
    refine ⟨X, hXd,
      chainT_pos hp hc X (fun s => (Y s).filter (fun x => x ∈ cut X)) v ?_ ?_,
      chainF_neg hp hc X (fun s => (Finset.range (d+4*e+2*(4*2^a)+4*2^a)).filter
        (fun x => x ∈ Y s ∨ x ∈ cut X)) v ?_ ?_⟩
    · intro s s' hss x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hY hss hx.1, hx.2⟩
    · intro s hs
      refine ⟨⟨fun x hx => (h s).1 (Finset.mem_filter.1 hx).1, ?_, ?_⟩,
        fun x hx => (Finset.mem_filter.1 hx).2⟩
      · intro x hx
        refine Finset.mem_filter.2 ⟨(h s).2.1 hx, (hc X x).2 (P_sub_cut hp X s (v s) hs
          (fun h1 h2 => ?_) x hx)⟩
        have hm : (L s (v s)).1.val ∈ pins s (v s) true :=
          (hp _ _ _ _).2 (Or.inr (Or.inl ⟨⟨h1, h2, ⟨fun _ => rfl, fun _ => hs⟩⟩, rfl⟩))
        have hsm : s ≤ m := Fin.le_def.2 (by show s.val ≤ 2*2^a-1; omega)
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, hY hsm ((h s).2.1 hm)⟩
      · rw [Finset.disjoint_left]
        intro x hxN hxY
        exact Finset.disjoint_left.1 (h s).2.2 hxN (Finset.mem_filter.1 hxY).1
    · intro s s' hss x hx
      simp only [Finset.mem_filter] at hx ⊢
      rcases hx with ⟨hx1, hx2 | hx2⟩
      · exact ⟨hx1, Or.inl (hY hss hx2)⟩
      · exact ⟨hx1, Or.inr hx2⟩
    · intro s hs
      refine ⟨⟨Finset.filter_subset _ _, ?_, ?_⟩, ?_⟩
      · intro x hx
        exact Finset.mem_filter.2 ⟨(h s).1 ((h s).2.1 hx), Or.inl ((h s).2.1 hx)⟩
      · rw [Finset.disjoint_left]
        intro x hxN hxY
        rcases (Finset.mem_filter.1 hxY).2 with hy | hcut
        · exact Finset.disjoint_left.1 (h s).2.2 hxN hy
        · refine N_miss_cut hp X hXd s (v s) hs (fun h1 h2 hiX => ?_) x hxN ((hc X x).1 hcut)
          have hm : (L s (v s)).1.val ∈ pins s (v s) false :=
            (hp _ _ _ _).2 (Or.inr (Or.inl ⟨⟨h1, h2,
              ⟨fun h => absurd h hs, fun h => absurd h Bool.false_ne_true⟩⟩, rfl⟩))
          have hms : m ≤ s := Fin.le_def.2 (by show 2*2^a-1 ≤ s.val; omega)
          exact Finset.disjoint_left.1 (h s).2.2 hm (hY hms (Finset.mem_filter.1 hiX).2)
      · intro x hx
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (cut_range hXd x ((hc X x).1 hx)), Or.inr hx⟩
  · rintro ⟨X, hXd, ⟨w1, hs1, hX1⟩, ⟨w2, hs2, hX2⟩⟩
    obtain ⟨Y1, v1, m1, h1⟩ := pos_chainT hp hc X hXd w1 hs1 hX1
    obtain ⟨Y2, v2, m2, h2⟩ := neg_chainF hp hc X hXd w2 hs2 hX2
    refine ⟨fun s => if s.val < 2*2^a then Y1 s else Y2 s,
      fun s => if s.val < 2*2^a then v1 s else v2 s, ?_, ?_⟩
    · intro s t hst
      dsimp only
      by_cases hs : s.val < 2*2^a <;> by_cases ht : t.val < 2*2^a
      · rw [if_pos hs, if_pos ht]; exact m1 hst
      · rw [if_pos hs, if_neg ht]; exact (h1 s hs).2.trans (h2 t ht).2
      · exfalso; have : s.val ≤ t.val := hst; omega
      · rw [if_neg hs, if_neg ht]; exact m2 hst
    · intro s
      dsimp only
      by_cases hs : s.val < 2*2^a
      · simp only [if_pos hs]; exact (h1 s hs).1
      · simp only [if_neg hs]; exact (h2 s hs).1

theorem conj1 {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (s : Fin (4*2^a)) (j : Fin 3)
    (U : Finset ℕ) (hU : ∀ x, x ∈ U ↔ x ∈ pins s j true ∨ x ∈ pins s j false) (c : ℕ)
    (hc1 : ((L s j).2 = true ∧ (L s j).1.val < d) → c = 1)
    (hc0 : ¬ ((L s j).2 = true ∧ (L s j).1.val < d) → c = 0) :
    Disjoint (pins s j true) (pins s j false) ∧ U ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧
      U.card = a+6+c := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hP hN
    exact NP_disj hp s s j j le_rfl Iff.rfl (fun _ => rfl) (fun _ => rfl) x hN hP
  · intro x hx
    rcases (hU x).1 hx with h | h <;> exact Finset.mem_range.2 (P_range hp s j _ x h)
  · have hs := s.isLt
    have hi := (L s j).1.isLt
    obtain ⟨o, ho⟩ : ∃ o, (s.val < 2*2^a ∧ o = 0 ∨ ¬ s.val < 2*2^a ∧ o = 2*e) := by
      by_cases h : s.val < 2*2^a
      · exact ⟨0, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨2*e, Or.inr ⟨h, rfl⟩⟩
    have ho2 : o ≤ 2*e := by rcases ho with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    obtain ⟨B, hB, hBc⟩ : ∃ B : Finset ℕ, (∀ x, x ∈ B ↔ ((L s j).2 = true ∧ (L s j).1.val < d) ∧ x = (L s j).1.val) ∧ B.card = c := by
      by_cases h : (L s j).2 = true ∧ (L s j).1.val < d
      · exact ⟨{(L s j).1.val}, fun x => by simp [h], by rw [hc1 h]; simp⟩
      · exact ⟨∅, fun x => by simp [h], by rw [hc0 h]; simp⟩
    set z := d + o + 2*(L s j).1.val with hz
    set q := d+4*e+2*s.val with hq
    set off := d+4*e+2*(4*2^a) with hoff
    have hE : U = (({z, z+1} ∪ B) ∪ ({q, q+1} ∪ (Finset.range (a+2)).image (fun J => off + piv s.val J))) := by
      ext x
      simp only [hU, hp, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_range, hB]
      constructor
      · rintro (h | h) <;>
        rcases h with ⟨o', c', ho', hc', rfl⟩ | ⟨⟨h1, h2, -⟩, rfl⟩ | ⟨k, hk, -, rfl⟩ | ⟨J, hJ, -, rfl⟩
        · have hc2 : c' ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
          exact Or.inl (Or.inl (by omega))
        · exact Or.inl (Or.inr ⟨⟨h2, h1⟩, rfl⟩)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr ⟨J, hJ, rfl⟩)
        · have hc2 : c' ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
          exact Or.inl (Or.inl (by omega))
        · exact Or.inl (Or.inr ⟨⟨h2, h1⟩, rfl⟩)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr ⟨J, hJ, rfl⟩)
      · rintro (((rfl | rfl) | ⟨⟨h2, h1⟩, rfl⟩) | ((rfl | rfl) | ⟨J, hJ, rfl⟩))
        · by_cases hb : (L s j).2 = true
          · exact Or.inr (Or.inl ⟨o, 0, ho, Or.inr ⟨by simp [hb], rfl⟩, rfl⟩)
          · exact Or.inl (Or.inl ⟨o, 0, ho, Or.inr ⟨hb, rfl⟩, rfl⟩)
        · by_cases hb : (L s j).2 = true
          · exact Or.inl (Or.inl ⟨o, 1, ho, Or.inl ⟨hb, rfl⟩, rfl⟩)
          · exact Or.inr (Or.inl ⟨o, 1, ho, Or.inl ⟨by simpa using hb, rfl⟩, rfl⟩)
        · by_cases hl : s.val < 2*2^a
          · exact Or.inl (Or.inr (Or.inl ⟨⟨h1, h2, ⟨fun _ => rfl, fun _ => hl⟩⟩, rfl⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨⟨h1, h2, ⟨fun h => absurd h hl, fun h => absurd h Bool.false_ne_true⟩⟩, rfl⟩))
        · by_cases hb : j.val/2^0%2 = 1
          · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨0, by omega, ⟨fun _ => rfl, fun _ => hb⟩, rfl⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨0, by omega, ⟨fun h => absurd h hb, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
        · by_cases hb : j.val/2^1%2 = 1
          · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨1, by omega, ⟨fun _ => rfl, fun _ => hb⟩, rfl⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨1, by omega, ⟨fun h => absurd h hb, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
        · by_cases hb : s.val/2^J%2 = 1
          · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨J, hJ, ⟨fun _ => rfl, fun _ => hb⟩, rfl⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨J, hJ, ⟨fun h => absurd h hb, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
    have hBd : ∀ x, x ∈ B → x < d := fun x hx => by
      obtain ⟨⟨-, h⟩, rfl⟩ := (hB x).1 hx; exact h
    have hD : ((Finset.range (a+2)).image (fun J => off + piv s.val J)).card = a+2 := by
      rw [Finset.card_image_of_injective _ (fun J J' h => piv_inj s.val J J' (by simpa using h)),
        Finset.card_range]
    rw [hE, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint, hD, hBc, Finset.card_pair (by omega), Finset.card_pair (by omega)]
    · omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_range] at hx hx'
      obtain ⟨J, -, rfl⟩ := hx'
      omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      have := hBd x hx'
      omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_range] at hx hx'
      have h1 : x < d + 4*e := by
        rcases hx with (h | h) | h
        · omega
        · omega
        · have := hBd x h; omega
      rcases hx' with (h | h) | ⟨J, -, rfl⟩ <;> omega

end PEqualNP.Outside.L_lib_1435_aux.Cells

namespace PEqualNP.Outside.L_lib_1435_aux.Packing

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.NotBracket (notCount)

private abbrev Allowed (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .not

private def bitOrder (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false ≤ y.getD i false

private theorem bool_order (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

private theorem bool_digit (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

private theorem digit_order {a b : Bool} (ab : a ≤ b) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all [bool_order]

private theorem digit_inj {a b : Bool} (eq : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem order_append {x y : List Bool} (ordered : bitOrder x y) {a b : Bool} (ab : a ≤ b) :
    bitOrder (x ++ [a]) (y ++ [b]) := by
  refine ⟨by simp [ordered.1],?_⟩
  intro i
  rcases lt_trichotomy i x.length with lt | eq | gt
  · have ly : i < y.length := ordered.1 ▸ lt
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left ly] using ordered.2 i
  · subst i
    simpa [List.getD_eq_getElem?_getD,ordered.1] using ab
  · have noneX : (x ++ [a]).length ≤ i := by simp; omega
    have noneY : (y ++ [b]).length ≤ i := by simp [← ordered.1]; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none noneX,List.getElem?_eq_none noneY]

private def incoming (g : Gate) (w : List Bool) : List Bool :=
  g.inputs.map (fun i => w.getD i false)

private def outputBit (g : Gate) (w : List Bool) : Bool := g.op.eval (incoming g w)

private def firstBit (g : Gate) (w : List Bool) : Bool := (incoming g w).headD false

private theorem first_order (g : Gate) {x y : List Bool} (ordered : bitOrder x y) :
    firstBit g x ≤ firstBit g y := by
  unfold firstBit incoming
  cases h : g.inputs with
  | nil => simp
  | cons i rest => exact ordered.2 i

private theorem and_order {g : Gate} (op : g.op = .and) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.all_eq_true] at on ⊢
  intro v hm
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact (bool_order _ _).mp (ordered.2 i) (on _ (List.mem_map.mpr ⟨i,here,rfl⟩))

private theorem or_order {g : Gate} (op : g.op = .or) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.any_eq_true] at on ⊢
  obtain ⟨v,hm,active⟩ := on
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact ⟨_,List.mem_map.mpr ⟨i,here,rfl⟩,(bool_order _ _).mp (ordered.2 i) active⟩

private def inverting (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

private def advance (s : List Bool × ℕ) (g : Gate) : List Bool × ℕ :=
  (s.1 ++ [outputBit g s.1],if inverting g then 2*s.2+(firstBit g s.1).toNat else s.2)

private def consistent (s t : List Bool × ℕ) : Prop :=
  s.2 ≤ t.2 ∧ (s.2 = t.2 → bitOrder s.1 t.1)

private theorem advance_consistent {s t : List Bool × ℕ} {g : Gate} (allowed : Allowed g)
    (before : consistent s t) : consistent (advance s g) (advance t g) := by
  by_cases strict : s.2 < t.2
  · have increase : (advance s g).2 < (advance t g).2 := by
      by_cases neg : inverting g = true
      · simp only [advance,neg,ite_true]
        have bit := bool_digit (firstBit g s.1)
        omega
      · simpa [advance,neg] using strict
    exact ⟨increase.le,fun eq => (increase.ne eq).elim⟩
  have eq : s.2 = t.2 := Nat.le_antisymm before.1 (Nat.le_of_not_gt strict)
  have ordered := before.2 eq
  rcases allowed with op | op | op
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (and_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (or_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,ite_true]
    have order := digit_order (first_order g ordered)
    refine ⟨by omega,?_⟩
    intro next
    have sameDigit : (firstBit g s.1).toNat = (firstBit g t.1).toNat := by omega
    have sameBit := digit_inj sameDigit
    apply order_append ordered
    simp only [outputBit,op,GateOp.eval]
    change (!firstBit g s.1) ≤ (!firstBit g t.1)
    rw [sameBit]

private def negCount (gates : List Gate) : ℕ := (gates.filter inverting).length

private theorem negCount_spec (C : Circuit) : negCount C.gates = notCount C := by
  classical
  unfold negCount notCount
  congr 2
  funext g
  cases h : g.op <;> simp [inverting,h]

private theorem run_consistent (gates : List Gate) (allowed : ∀ g ∈ gates, Allowed g)
    {s t : List Bool × ℕ} (before : consistent s t) :
    consistent (gates.foldl advance s) (gates.foldl advance t) := by
  induction gates generalizing s t with
  | nil => exact before
  | cons g rest ih =>
    exact ih (fun k hm => allowed k (List.mem_cons_of_mem _ hm))
      (advance_consistent (allowed g (List.mem_cons_self ..)) before)

private theorem run_bounded (gates : List Gate) (s : List Bool × ℕ) (d : ℕ) (bound : s.2 < 2^d) :
    (gates.foldl advance s).2 < 2^(d+negCount gates) := by
  induction gates generalizing s d with
  | nil => simpa [negCount] using bound
  | cons g rest ih =>
    by_cases neg : inverting g = true
    · have raises : (advance s g).2 < 2^(d+1) := by
        simp only [advance,neg,ite_true,Nat.pow_succ]
        have digit := bool_digit (firstBit g s.1)
        omega
      have next := ih (advance s g) (d+1) raises
      simpa [negCount,neg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next
    · have same : (advance s g).2 < 2^d := by simpa [advance,neg] using bound
      simpa [negCount,neg] using ih (advance s g) d same

private theorem run_wires (gates : List Gate) (s : List Bool × ℕ) :
    (gates.foldl advance s).1 =
      gates.foldl (fun w g => w ++ [outputBit g w]) s.1 := by
  induction gates generalizing s with
  | nil => rfl
  | cons g rest ih => exact ih (advance s g)

private theorem inputs_order {n : ℕ} {x y : Fin n → Bool} (xy : x ≤ y) :
    bitOrder (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  have first : bitOrder (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,?_⟩
    intro i
    by_cases inside : i < n
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside] using xy ⟨i,inside⟩
    · simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside]
  simpa only [List.append_assoc,List.singleton_append] using
    order_append (order_append first (a := false) (b := false) le_rfl)
      (a := true) (b := true) le_rfl

def grade {n : ℕ} (C : Circuit) (x : Fin n → Bool) : ℕ :=
  (C.gates.foldl advance (List.ofFn x ++ [false,true],0)).2

theorem grade_bound {n : ℕ} (C : Circuit) (x : Fin n → Bool) : grade C x < 2^(notCount C) := by
  simpa [grade,negCount_spec] using
    run_bounded C.gates (List.ofFn x ++ [false,true],0) 0 (by change 0 < 1; decide)

theorem grade_order {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool} (xy : x ≤ y) :
    grade C x ≤ grade C y ∧ (grade C x = grade C y → ∀ i,
      (C.wires (List.ofFn x ++ [false,true])).getD i false ≤
        (C.wires (List.ofFn y ++ [false,true])).getD i false) := by
  have allowed (g) (mem : g ∈ C.gates) : Allowed g := by
    simpa [Allowed] using (basis g mem).1
  have initial : consistent (List.ofFn x ++ [false,true],0) (List.ofFn y ++ [false,true],0) :=
    ⟨le_rfl,fun _ => inputs_order xy⟩
  have result := run_consistent C.gates allowed initial
  refine ⟨result.1,?_⟩
  intro eq
  have order := (result.2 eq).2
  rw [run_wires,run_wires] at order
  exact order

theorem grade_fall {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool}
    (xy : x ≤ y) (i : ℕ)
    (before : (C.wires (List.ofFn x ++ [false,true])).getD i false = true)
    (after : (C.wires (List.ofFn y ++ [false,true])).getD i false = false) :
    grade C x < grade C y := by
  obtain ⟨order,read⟩ := grade_order basis xy
  refine lt_of_le_of_ne order ?_
  intro eq
  have impossible := read eq i
  rw [before,after] at impossible
  exact (by decide : ¬ (true ≤ false)) impossible

abbrev Reach {n m : ℕ} (P N : (Fin n → Bool) → Fin m → Prop) :
    ℕ → (Fin n → Bool) → Prop :=
  Nat.rec (motive := fun _ => (Fin n → Bool) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j)

theorem no_packing_of_taps {n m r : ℕ} {P N : (Fin n → Bool) → Fin m → Prop}
    {C : Circuit} (tap : Fin m → ℕ) (basis : FanInTwo C) (budget : notCount C ≤ r)
    (fits : ∀ x j,
      let w := (C.wires (List.ofFn x ++ [false,true])).getD (tap j) false
      (P x j → w = true) ∧ (N x j → w = false)) :
    ∀ x, ¬ Reach P N (2^r) x := by
  have lower : ∀ k x, Reach P N k x → k ≤ grade C x := by
    intro k
    induction k with
    | zero => intro x _; exact Nat.zero_le _
    | succ k ih =>
      intro x reached
      obtain ⟨u,v,j,history,uv,vx,positive,negative⟩ := reached
      have old := ih u history
      have middle := grade_fall basis uv (tap j) ((fits u j).1 positive) ((fits v j).2 negative)
      have last := (grade_order basis vx).1
      omega
  intro x found
  have high := lower _ x found
  have low := (grade_bound C x).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) budget)
  omega

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

def value (C : Circuit) (x : List Bool) (i : Nat) : Bool := (C.wires x).getD i false

def nextWire (n : Nat) (C : Circuit) : Nat := n + C.size

def emptyCircuit : Circuit := ⟨[], 0⟩

def appendGate (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], C.output⟩

def appendAnd (C : Circuit) (a b : Nat) : Circuit := appendGate C ⟨.and, [a,b]⟩

def appendOr (C : Circuit) (a b : Nat) : Circuit := appendGate C ⟨.or, [a,b]⟩

def appendNot (C : Circuit) (a : Nat) : Circuit := appendGate C ⟨.not, [a]⟩

def withOutput (C : Circuit) (o : Nat) : Circuit := ⟨C.gates, o⟩

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

private theorem fold_length (gates : List Gate) (x : List Bool) :
    (gates.foldl gateStep x).length = x.length + gates.length := by
  induction gates generalizing x with
  | nil => simp
  | cons g rest ih =>
    rw [List.foldl_cons,ih]
    simp [gateStep] <;> omega

private theorem fold_value (gates : List Gate) (x : List Bool) {i : Nat} (valid : i < x.length) :
    (gates.foldl gateStep x).getD i false = x.getD i false := by
  induction gates generalizing x with
  | nil => rfl
  | cons g rest ih =>
    have available : i < (gateStep x g).length := by simp [gateStep]; omega
    rw [List.foldl_cons,ih _ available]
    exact List.getD_append _ _ _ _ valid

@[local simp] theorem emptyCircuit_size : emptyCircuit.size = 0 := rfl

@[local simp] theorem emptyCircuit_notCount : notCount emptyCircuit = 0 := rfl

theorem emptyCircuit_fanInTwo : FanInTwo emptyCircuit := by
  simp [FanInTwo,emptyCircuit]

theorem emptyCircuit_readsBack (n : Nat) : ReadsBack n emptyCircuit := by
  simp [ReadsBack,emptyCircuit]

@[local simp] theorem withOutput_size (C : Circuit) (o : Nat) : (withOutput C o).size = C.size := rfl

@[local simp] theorem withOutput_output (C : Circuit) (o : Nat) : (withOutput C o).output = o := rfl

@[local simp] theorem withOutput_notCount (C : Circuit) (o : Nat) :
    notCount (withOutput C o) = notCount C := rfl

@[local simp] theorem withOutput_fanInTwo (C : Circuit) (o : Nat) :
    FanInTwo (withOutput C o) ↔ FanInTwo C := Iff.rfl

@[local simp] theorem withOutput_readsBack (n : Nat) (C : Circuit) (o : Nat) :
    ReadsBack n (withOutput C o) ↔ ReadsBack n C := Iff.rfl

@[local simp] theorem withOutput_value (C : Circuit) (o : Nat) (x : List Bool) (i : Nat) :
    value (withOutput C o) x i = value C x i := rfl

@[local simp] theorem withOutput_eval (C : Circuit) (o : Nat) (x : List Bool) :
    (withOutput C o).eval x = value C x o := rfl

theorem withOutput_valid {n : Nat} {C : Circuit} {o : Nat} (valid : o < nextWire n C) :
    (withOutput C o).output < n + (withOutput C o).size := valid

@[local simp] theorem appendGate_size (C : Circuit) (g : Gate) :
    (appendGate C g).size = C.size + 1 := by
  simp [appendGate,Circuit.size]

@[local simp] theorem appendGate_output (C : Circuit) (g : Gate) :
    (appendGate C g).output = C.output := rfl

theorem appendGate_prefix (C : Circuit) (g : Gate) : C.gates <+: (appendGate C g).gates :=
  ⟨[g],rfl⟩

@[local simp] theorem appendGate_notCount (C : Circuit) (g : Gate) :
    notCount (appendGate C g) = notCount C + (@ite ℕ (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not) 1 0) := by
  by_cases inv : g.op = .not <;> simp [notCount,appendGate,inv]

@[local simp] theorem nextWire_appendGate (n : Nat) (C : Circuit) (g : Gate) :
    nextWire n (appendGate C g) = nextWire n C + 1 := by
  simp [nextWire,Nat.add_assoc]

theorem appendGate_fanInTwo {C : Circuit} {g : Gate} (basis : FanInTwo C)
    (op : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (arity : g.inputs.length ≤ 2) : FanInTwo (appendGate C g) := by
  intro k hk
  rcases List.mem_append.mp hk with old | new
  · exact basis k old
  · have same : k = g := List.mem_singleton.mp new
    subst k
    exact ⟨op,arity⟩

theorem appendGate_readsBack {n : Nat} {C : Circuit} {g : Gate} (valid : ReadsBack n C)
    (inputs : ∀ i ∈ g.inputs, i < nextWire n C) : ReadsBack n (appendGate C g) := by
  intro j hj i hi
  change i ∈ ((C.gates ++ [g]).getD j ⟨.or, []⟩).inputs at hi
  by_cases old : j < C.gates.length
  · rw [List.getD_append _ _ _ _ old] at hi
    exact valid j old i hi
  · change j < (C.gates ++ [g]).length at hj
    have same : j = C.gates.length := by simp at hj; omega
    subst j
    rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
    exact inputs i (by simpa using hi)

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = nextWire x.length C := by
  rw [wires_eq]
  exact fold_length C.gates x

theorem value_input (C : Circuit) (x : List Bool) {i : Nat} (valid : i < x.length) :
    value C x i = x.getD i false := by
  rw [value,wires_eq]
  exact fold_value C.gates x valid

theorem nextWire_le_of_prefix {n : Nat} {C D : Circuit} (extension : C.gates <+: D.gates) :
    nextWire n C ≤ nextWire n D := Nat.add_le_add_left extension.length_le n

theorem value_of_prefix {C D : Circuit} (extension : C.gates <+: D.gates) {x : List Bool}
    {i : Nat} (valid : i < nextWire x.length C) : value D x i = value C x i := by
  obtain ⟨rest,appended⟩ := extension
  simp only [value,wires_eq,← appended,List.foldl_append]
  apply fold_value
  rw [fold_length]
  exact valid

theorem appendGate_wires (C : Circuit) (g : Gate) (x : List Bool) :
    (appendGate C g).wires x = C.wires x ++ [g.op.eval (g.inputs.map fun i => value C x i)] := by
  simp [appendGate,wires_eq,gateStep,value]

theorem appendGate_old {C : Circuit} {g : Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendGate C g) x i = value C x i :=
  value_of_prefix (appendGate_prefix C g) valid

theorem appendGate_new (C : Circuit) (g : Gate) (x : List Bool) :
    value (appendGate C g) x (nextWire x.length C) =
      g.op.eval (g.inputs.map fun i => value C x i) := by
  rw [value,appendGate_wires,← wires_length]
  simp [List.getD_eq_getElem?_getD]

@[local simp] theorem appendAnd_size (C : Circuit) (a b : Nat) :
    (appendAnd C a b).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendOr_size (C : Circuit) (a b : Nat) :
    (appendOr C a b).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendNot_size (C : Circuit) (a : Nat) :
    (appendNot C a).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendAnd_notCount (C : Circuit) (a b : Nat) :
    notCount (appendAnd C a b) = notCount C := by simp [appendAnd]

@[local simp] theorem appendOr_notCount (C : Circuit) (a b : Nat) :
    notCount (appendOr C a b) = notCount C := by simp [appendOr]

@[local simp] theorem appendNot_notCount (C : Circuit) (a : Nat) :
    notCount (appendNot C a) = notCount C + 1 := by simp [appendNot]

theorem appendAnd_fanInTwo {C : Circuit} {a b : Nat} (basis : FanInTwo C) :
    FanInTwo (appendAnd C a b) := appendGate_fanInTwo (g := ⟨.and,[a,b]⟩) basis (by simp) (by simp)

theorem appendOr_fanInTwo {C : Circuit} {a b : Nat} (basis : FanInTwo C) :
    FanInTwo (appendOr C a b) := appendGate_fanInTwo (g := ⟨.or,[a,b]⟩) basis (by simp) (by simp)

theorem appendNot_fanInTwo {C : Circuit} {a : Nat} (basis : FanInTwo C) :
    FanInTwo (appendNot C a) := appendGate_fanInTwo (g := ⟨.not,[a]⟩) basis (by simp) (by simp)

theorem appendAnd_readsBack {n : Nat} {C : Circuit} {a b : Nat} (valid : ReadsBack n C)
    (left : a < nextWire n C) (right : b < nextWire n C) : ReadsBack n (appendAnd C a b) := by
  apply appendGate_readsBack (g := ⟨.and,[a,b]⟩) valid
  intro i member
  change i ∈ [a,b] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact left
  · exact right

theorem appendOr_readsBack {n : Nat} {C : Circuit} {a b : Nat} (valid : ReadsBack n C)
    (left : a < nextWire n C) (right : b < nextWire n C) : ReadsBack n (appendOr C a b) := by
  apply appendGate_readsBack (g := ⟨.or,[a,b]⟩) valid
  intro i member
  change i ∈ [a,b] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact left
  · exact right

theorem appendNot_readsBack {n : Nat} {C : Circuit} {a : Nat} (valid : ReadsBack n C)
    (input : a < nextWire n C) : ReadsBack n (appendNot C a) := by
  apply appendGate_readsBack (g := ⟨.not,[a]⟩) valid
  intro i member
  have same : i = a := List.mem_singleton.mp member
  subst i
  exact input

theorem appendAnd_new (C : Circuit) (x : List Bool) (a b : Nat) :
    value (appendAnd C a b) x (nextWire x.length C) = (value C x a && value C x b) := by
  simpa [appendAnd,GateOp.eval] using appendGate_new C ⟨.and,[a,b]⟩ x

theorem appendOr_new (C : Circuit) (x : List Bool) (a b : Nat) :
    value (appendOr C a b) x (nextWire x.length C) = (value C x a || value C x b) := by
  simpa [appendOr,GateOp.eval] using appendGate_new C ⟨.or,[a,b]⟩ x

theorem appendNot_new (C : Circuit) (x : List Bool) (a : Nat) :
    value (appendNot C a) x (nextWire x.length C) = !value C x a := by
  exact appendGate_new C ⟨.not,[a]⟩ x

abbrev Input (n : ℕ) := Fin n → Bool

variable {n m : ℕ} (P N : Input n → Fin m → Prop)

theorem reach_zero (x : Input n) : Reach P N 0 x := trivial

theorem reach_succ (k : ℕ) (x : Input n) : Reach P N (k+1) x ↔
    ∃ u v j, Reach P N k u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j := Iff.rfl

theorem reach_mono (k : ℕ) : Monotone (Reach P N k) := by
  intro x y xy active
  cases k with
  | zero => exact reach_zero P N y
  | succ k =>
    obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
    exact (reach_succ P N k y).mpr ⟨u,v,j,prior,uv,vx.trans xy,pu,nv⟩

theorem reach_pred {k : ℕ} {x : Input n} (active : Reach P N (k+1) x) : Reach P N k x := by
  obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
  exact reach_mono P N k (uv.trans vx) prior

theorem reach_of_le {k l : ℕ} {x : Input n} (bound : k ≤ l) (active : Reach P N l x) :
    Reach P N k x := by
  induction bound with
  | refl => exact active
  | step _ ih => exact ih (reach_pred P N active)

noncomputable def support : Finset (Input n) := by
  classical
  exact Finset.univ.filter (fun x => ∃ j, P x j ∨ N x j)

theorem mem_support (x : Input n) : x ∈ support P N ↔ ∃ j, P x j ∨ N x j := by
  classical
  simp [support]

theorem cone_iff (u x : Input n) : u ≤ x ↔ ∀ i, u i = true → x i = true := by
  constructor
  · intro below i active
    exact Bool.le_iff_imp.mp (below i) active
  · intro on i
    exact Bool.le_iff_imp.mpr (on i)

theorem reach_support {k : ℕ} (positive : 0 < k) (x : Input n) : Reach P N k x ↔
    ∃ v ∈ support P N, v ≤ x ∧ Reach P N k v := by
  constructor
  · intro active
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
      refine ⟨v,(mem_support P N v).mpr ⟨j,Or.inr nv⟩,vx,?_⟩
      exact (reach_succ P N k v).mpr ⟨u,v,j,prior,uv,le_rfl,pu,nv⟩
  · rintro ⟨v,_,vx,active⟩
    exact reach_mono P N k vx active

private noncomputable def levels (d : ℕ) (x : Input n) : Finset ℕ := by
  classical
  exact (Finset.range (d+1)).filter (fun k => Reach P N k x)

private theorem mem_levels (d : ℕ) (x : Input n) (k : ℕ) :
    k ∈ levels P N d x ↔ k ≤ d ∧ Reach P N k x := by
  classical
  simp [levels,Nat.lt_succ_iff]

private theorem levels_nonempty (d : ℕ) (x : Input n) : (levels P N d x).Nonempty :=
  ⟨0,(mem_levels P N d x 0).mpr ⟨Nat.zero_le _,reach_zero P N x⟩⟩

noncomputable def rank (d : ℕ) (x : Input n) : ℕ :=
  (levels P N d x).max' (levels_nonempty P N d x)

theorem rank_bound (d : ℕ) (x : Input n) : rank P N d x ≤ d :=
  ((mem_levels P N d x _).mp (Finset.max'_mem _ (levels_nonempty P N d x))).1

theorem rank_reaches (d : ℕ) (x : Input n) : Reach P N (rank P N d x) x :=
  ((mem_levels P N d x _).mp (Finset.max'_mem _ (levels_nonempty P N d x))).2

theorem level_le_rank {d k : ℕ} {x : Input n} (small : k ≤ d) (active : Reach P N k x) :
    k ≤ rank P N d x :=
  Finset.le_max' (levels P N d x) k ((mem_levels P N d x k).mpr ⟨small,active⟩)

theorem rank_mono (d : ℕ) : Monotone (rank P N d) := by
  intro x y xy
  exact level_le_rank P N (rank_bound P N d x) (reach_mono P N _ xy (rank_reaches P N d x))

theorem rank_threshold_iff {d k : ℕ} {x : Input n} (small : k ≤ d) :
    k ≤ rank P N d x ↔ Reach P N k x :=
  ⟨fun below => reach_of_le P N below (rank_reaches P N d x), level_le_rank P N small⟩

theorem rank_grows {d : ℕ} (bounded : ∀ x, ¬ Reach P N (d+1) x)
    {u v : Input n} {j : Fin m} (uv : u ≤ v) (pu : P u j) (nv : N v j) :
    rank P N d u < rank P N d v := by
  have next : Reach P N (rank P N d u + 1) v :=
    (reach_succ P N _ v).mpr ⟨u,v,j,rank_reaches P N d u,uv,le_rfl,pu,nv⟩
  have room : rank P N d u + 1 ≤ d := by
    by_contra notRoom
    exact bounded v (reach_of_le P N (by omega : d+1 ≤ rank P N d u+1) next)
  exact Nat.lt_of_succ_le (level_le_rank P N room next)

theorem threshold_support (d : ℕ) {k : ℕ} (positive : 0 < k) (x : Input n) :
    k ≤ rank P N d x ↔ ∃ v ∈ support P N, v ≤ x ∧ k ≤ rank P N d v := by
  constructor
  · intro high
    have small : k ≤ d := high.trans (rank_bound P N d x)
    obtain ⟨v,mem,vx,active⟩ := (reach_support P N positive x).mp
      ((rank_threshold_iff P N small).mp high)
    exact ⟨v,mem,vx,level_le_rank P N small active⟩
  · rintro ⟨v,_,vx,high⟩
    exact high.trans (rank_mono P N d vx)

noncomputable def rankBucket (d k : ℕ) : Finset (Input n) := by
  classical
  exact (support P N).filter (fun x => rank P N d x = k)

theorem mem_rankBucket (d k : ℕ) (x : Input n) :
    x ∈ rankBucket P N d k ↔ x ∈ support P N ∧ rank P N d x = k := by
  classical
  simp [rankBucket]

theorem rank_bucket_count (d : ℕ) :
    (∑ k ∈ Finset.range (d+1), (rankBucket P N d k).card) = (support P N).card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise (s := support P N) (t := Finset.range (d+1))
    (f := rank P N d) (by
      intro x _
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (rank_bound P N d x)))).symm

theorem threshold_buckets (d : ℕ) {k : ℕ} (positive : 0 < k) (x : Input n) :
    k ≤ rank P N d x ↔ ∃ l, k ≤ l ∧ l ≤ d ∧ ∃ v ∈ rankBucket P N d l, v ≤ x := by
  constructor
  · intro on
    obtain ⟨v,mem,vx,below⟩ := (threshold_support P N d positive x).mp on
    exact ⟨rank P N d v,below,rank_bound P N d v,v,(mem_rankBucket P N d _ _).mpr ⟨mem,rfl⟩,vx⟩
  · rintro ⟨l,kl,_,v,mem,vx⟩
    obtain ⟨supportV,level⟩ := (mem_rankBucket P N d l v).mp mem
    exact (threshold_support P N d positive x).mpr ⟨v,supportV,vx,level.symm ▸ kl⟩

noncomputable def positiveInputs (j : Fin m) : Finset (Input n) := by
  classical
  exact Finset.univ.filter (fun x => P x j)

noncomputable def positivePairs : Finset (Input n × Fin m) := by
  classical
  exact Finset.univ.filter (fun z => P z.1 z.2)

theorem mem_positiveInputs (j : Fin m) (x : Input n) : x ∈ positiveInputs P j ↔ P x j := by
  classical
  simp [positiveInputs]

theorem mem_positivePairs (z : Input n × Fin m) : z ∈ positivePairs P ↔ P z.1 z.2 := by
  classical
  simp [positivePairs]

theorem positive_input_support {j : Fin m} {x : Input n} (positive : x ∈ positiveInputs P j) :
    x ∈ support P N :=
  (mem_support P N x).mpr ⟨j,Or.inl ((mem_positiveInputs P j x).mp positive)⟩

theorem positive_incidence_count :
    (∑ j : Fin m, (positiveInputs P j).card) = (positivePairs P).card := by
  classical
  calc
    _ = ∑ j : Fin m, ((positivePairs P).filter (fun z => z.2 = j)).card := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.card_nbij' (fun x : Input n => (x,j)) Prod.fst
      · intro x present
        exact Finset.mem_filter.mpr ⟨(mem_positivePairs P _).mpr ((mem_positiveInputs P _ _).mp present),rfl⟩
      · intro z present
        obtain ⟨member,eq⟩ := Finset.mem_filter.mp present
        exact (mem_positiveInputs P _ _).mpr (eq ▸ (mem_positivePairs P z).mp member)
      · intro x _
        rfl
      · intro z present
        exact Prod.ext rfl (Finset.mem_filter.mp present).2.symm
    _ = _ := (Finset.card_eq_sum_card_fiberwise (s := positivePairs P) (t := Finset.univ)
      (f := Prod.snd) (by
        intro j _
        exact Finset.mem_univ _)).symm

def guardedCone (d : ℕ) (u x : Input n) : Prop :=
  u ≤ x ∧ ¬ rank P N d u + 1 ≤ rank P N d x

def tapAccepts (d : ℕ) (x : Input n) (j : Fin m) : Prop :=
  ∃ u ∈ positiveInputs P j, guardedCone P N d u x

theorem tap_accepts_positive (d : ℕ) {x : Input n} {j : Fin m} (positive : P x j) :
    tapAccepts P N d x j := by
  refine ⟨x,(mem_positiveInputs P j x).mpr positive,le_rfl,?_⟩
  omega

theorem tap_rejects_negative {d : ℕ} (bounded : ∀ x, ¬ Reach P N (d+1) x)
    {x : Input n} {j : Fin m} (negative : N x j) : ¬ tapAccepts P N d x j := by
  rintro ⟨u,mem,ux,below⟩
  have grows := rank_grows P N bounded ux ((mem_positiveInputs P j u).mp mem) negative
  exact below (Nat.succ_le_of_lt grows)

namespace Thermometer

abbrev Word (d : ℕ) := Fin d → Bool

def half (d : ℕ) : ℕ := d / 2

def middle (d : ℕ) : ℕ := (d - 1) / 2

theorem half_le (d : ℕ) : half d ≤ d := by
  unfold half
  omega

theorem middle_le_half (d : ℕ) : middle d ≤ half d := by
  unfold middle half
  omega

theorem split_length {d : ℕ} (positive : 0 < d) :
    middle d + 1 + half d = d := by
  unfold middle half
  omega

theorem half_lt_pow {r d : ℕ} (bound : d < 2^(r+1)) : half d < 2^r := by
  rw [Nat.pow_succ] at bound
  unfold half
  omega

def pivot {d : ℕ} (positive : 0 < d) : Fin d :=
  ⟨middle d,by have eq := split_length positive; omega⟩

def lowerSource {d : ℕ} (i : Fin (half d)) : Fin d :=
  ⟨i.val,i.isLt.trans_le (half_le d)⟩

def upperSource {d : ℕ} (positive : 0 < d) (i : Fin (half d)) : Fin d :=
  ⟨middle d + 1 + i.val,by
    have eq := split_length positive
    have h := i.isLt
    omega⟩

def lowerSlot {d : ℕ} (i : Fin d) (before : i.val < middle d) : Fin (half d) :=
  ⟨i.val,before.trans_le (middle_le_half d)⟩

def upperSlot {d : ℕ} (positive : 0 < d) (i : Fin d) (after : middle d < i.val) : Fin (half d) :=
  ⟨i.val - (middle d + 1),by
    have eq := split_length positive
    have h := i.isLt
    omega⟩

def lowerWord {d : ℕ} (w : Word d) : Word (half d) :=
  fun i => if i.val < middle d then w (lowerSource i) else false

def upperWord {d : ℕ} (positive : 0 < d) (w : Word d) : Word (half d) :=
  fun i => w (upperSource positive i)

def folded {d : ℕ} (positive : 0 < d) (w : Word d) : Word (half d) :=
  fun i => (!w (pivot positive) && lowerWord w i) || upperWord positive w i

private theorem lower_antitone {d : ℕ} {w : Word d} (ordered : Antitone w) :
    Antitone (lowerWord w) := by
  intro i j compare
  by_cases before : j.val < middle d
  · have earlier : i.val < middle d := lt_of_le_of_lt compare before
    simp only [lowerWord,ite_eq_left before,ite_eq_left earlier]
    exact ordered (show lowerSource i ≤ lowerSource j from compare)
  · simp only [lowerWord,ite_eq_right before]
    exact Bool.false_le _

private theorem upper_antitone {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w) :
    Antitone (upperWord positive w) := by
  intro i j compare
  apply ordered
  change middle d + 1 + i.val ≤ middle d + 1 + j.val
  exact Nat.add_le_add_left compare _

theorem folded_eq_lower {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w)
    (off : w (pivot positive) = false) (i : Fin (half d)) :
    folded positive w i = lowerWord w i := by
  have after : pivot positive ≤ upperSource positive i := by
    change middle d ≤ middle d + 1 + i.val
    omega
  have upperOff : upperWord positive w i = false :=
    Bool.eq_false_of_le_false (by simpa only [off,upperWord] using ordered after)
  simp [folded,off,upperOff]

theorem folded_eq_upper {d : ℕ} (positive : 0 < d) {w : Word d}
    (on : w (pivot positive) = true) (i : Fin (half d)) :
    folded positive w i = upperWord positive w i := by
  simp [folded,on]

theorem folded_antitone {d : ℕ} (positive : 0 < d) {w : Word d}
    (ordered : Antitone w) : Antitone (folded positive w) := by
  cases bit : w (pivot positive)
  · rw [funext (folded_eq_lower positive ordered bit)]
    exact lower_antitone ordered
  · rw [funext (folded_eq_upper positive bit)]
    exact upper_antitone positive ordered

def decoded {d : ℕ} (positive : 0 < d) (notPivot : Bool)
    (notHalf : Word (half d)) (i : Fin d) : Bool :=
  if before : i.val < middle d then notPivot && notHalf (lowerSlot i before)
  else if atPivot : i.val = middle d then notPivot
  else notPivot || notHalf (upperSlot positive i (by omega))

theorem decoded_lower {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (before : i.val < middle d) :
    decoded positive b z i = (b && z (lowerSlot i before)) := by
  simp only [decoded,dite_eq_left before]

theorem decoded_pivot {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (atPivot : i.val = middle d) : decoded positive b z i = b := by
  have notBefore : ¬ i.val < middle d := by omega
  simp only [decoded,dite_eq_right notBefore,dite_eq_left atPivot]

theorem decoded_upper {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (after : middle d < i.val) :
    decoded positive b z i = (b || z (upperSlot positive i after)) := by
  have notBefore : ¬ i.val < middle d := by omega
  have notPivot : i.val ≠ middle d := by omega
  simp only [decoded,dite_eq_right notBefore,dite_eq_right notPivot]

private theorem lower_at_slot {d : ℕ} (w : Word d) (i : Fin d)
    (before : i.val < middle d) : lowerWord w (lowerSlot i before) = w i := by
  have same : lowerSource (lowerSlot i before) = i := Fin.ext rfl
  change (if i.val < middle d then w (lowerSource (lowerSlot i before)) else false) = w i
  rw [ite_eq_left before,same]

private theorem upper_at_slot {d : ℕ} (positive : 0 < d) (w : Word d) (i : Fin d)
    (after : middle d < i.val) : upperWord positive w (upperSlot positive i after) = w i := by
  apply congrArg w
  apply Fin.ext
  change middle d + 1 + (i.val - (middle d + 1)) = i.val
  omega

theorem decoded_correct {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w)
    {z : Word (half d)} (tail : ∀ j, z j = !(folded positive w j)) (i : Fin d) :
    decoded positive (!w (pivot positive)) z i = !w i := by
  rcases lt_trichotomy i.val (middle d) with before | atPivot | after
  · rw [decoded_lower positive _ _ _ before]
    cases bit : w (pivot positive)
    · simp [bit,tail,folded_eq_lower positive ordered bit,lower_at_slot w i before]
    · have earlier : i ≤ pivot positive := by
        change i.val ≤ middle d
        omega
      have on : w i = true := Bool.eq_true_of_true_le (by simpa only [bit] using ordered earlier)
      simp [bit,on]
  · have same : pivot positive = i := Fin.ext atPivot.symm
    rw [decoded_pivot positive _ _ _ atPivot,same]
  · rw [decoded_upper positive _ _ _ after]
    cases bit : w (pivot positive)
    · have later : pivot positive ≤ i := by
        change middle d ≤ i.val
        omega
      have off : w i = false := Bool.eq_false_of_le_false (by simpa only [bit] using ordered later)
      simp [bit,off]
    · simp [bit,tail,folded_eq_upper positive bit,upper_at_slot positive w i after]

def inverted : (r d : ℕ) → Word d → Word d
  | 0, _, w => w
  | r+1, d, w =>
    if positive : 0 < d then
      decoded positive (!w (pivot positive)) (inverted r (half d) (folded positive w))
    else w

theorem inverted_correct {r d : ℕ} (bound : d < 2^r) (w : Word d) (ordered : Antitone w) :
    inverted r d w = fun i => !w i := by
  induction r generalizing d with
  | zero =>
    funext i
    have existsIndex := i.isLt
    simp at bound
    omega
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inverted,dite_eq_left positive]
      funext i
      have complement := ih (half_lt_pow bound) (folded positive w)
        (folded_antitone positive ordered)
      exact decoded_correct positive ordered (congrFun complement) i
    · funext i
      have existsIndex := i.isLt
      omega

def stepBinary (d : ℕ) : ℕ := 2 * half d + (d - 1)

theorem step_binary_bound (d : ℕ) : stepBinary d + 4 * half d ≤ 4*d := by
  unfold stepBinary half
  omega

def inversionBinary : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r+1, d => if 0 < d then stepBinary d + inversionBinary r (half d) else 0

def inversionNot : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r+1, d => if 0 < d then 1 + inversionNot r (half d) else 0

theorem inversion_binary_bound (r d : ℕ) : inversionBinary r d ≤ 4*d := by
  induction r generalizing d with
  | zero => simp [inversionBinary]
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inversionBinary,ite_eq_left positive]
      exact Nat.le_trans (Nat.add_le_add_left (ih (half d)) _) (step_binary_bound d)
    · simp [inversionBinary,positive]

theorem inversion_not_bound (r d : ℕ) : inversionNot r d ≤ r := by
  induction r generalizing d with
  | zero => simp [inversionNot]
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inversionNot,ite_eq_left positive]
      have count := ih (half d)
      omega
    · simp [inversionNot,positive]

end Thermometer

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def binaryValue (conjunction x y : Bool) : Bool := if conjunction then x && y else x || y

def appendBinary (conjunction : Bool) (C : Circuit) (left right : ℕ) : Circuit :=
  if conjunction then appendAnd C left right else appendOr C left right

def foldBinary (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ) :
    List ℕ → Circuit × ℕ
  | [] => (C,base)
  | i :: rest => foldBinary n conjunction (appendBinary conjunction C base i) (nextWire n C) rest

private theorem fold_values (conjunction : Bool) (indices : List ℕ) (a b : ℕ → Bool)
    (same : ∀ i ∈ indices, a i = b i) (base : Bool) :
    indices.foldl (fun acc i => binaryValue conjunction acc (a i)) base =
      indices.foldl (fun acc i => binaryValue conjunction acc (b i)) base := by
  induction indices generalizing base with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons,same i (List.mem_cons_self ..)]
    exact ih (fun j hj => same j (List.mem_cons_of_mem _ hj)) _

theorem foldBinary_spec (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ)
    (indices : List ℕ) (basis : FanInTwo C) (reads : ReadsBack n C)
    (baseValid : base < nextWire n C) (valid : ∀ i ∈ indices, i < nextWire n C) :
    let result := foldBinary n conjunction C base indices
    FanInTwo result.1 ∧ ReadsBack n result.1 ∧ result.2 < nextWire n result.1 ∧
      result.1.size = C.size + indices.length ∧ notCount result.1 = notCount C ∧
      ∀ (x : List Bool), x.length = n →
        (∀ i < nextWire n C, value result.1 x i = value C x i) ∧
        value result.1 x result.2 =
          indices.foldl (fun acc i => binaryValue conjunction acc (value C x i)) (value C x base) := by
  induction indices generalizing C base with
  | nil => exact ⟨basis,reads,baseValid,by simp [foldBinary],rfl,fun _ _ => ⟨fun _ _ => rfl,rfl⟩⟩
  | cons i rest ih =>
    let D := appendBinary conjunction C base i
    have iValid := valid i (List.mem_cons_self ..)
    have size : D.size = C.size+1 := by cases conjunction <;> simp [D,appendBinary]
    have nots : notCount D = notCount C := by cases conjunction <;> simp [D,appendBinary]
    have growth : nextWire n D = nextWire n C+1 := by simp [nextWire,size,Nat.add_assoc]
    have forms : FanInTwo D := by
      cases conjunction
      · exact appendOr_fanInTwo basis
      · exact appendAnd_fanInTwo basis
    have previous : ReadsBack n D := by
      cases conjunction
      · exact appendOr_readsBack reads baseValid iValid
      · exact appendAnd_readsBack reads baseValid iValid
    have persist (x : List Bool) (length : x.length = n) (j : ℕ) (earlier : j < nextWire n C) :
        value D x j = value C x j := by
      rw [← length] at earlier
      cases conjunction
      · exact appendGate_old (g := ⟨.or,[base,i]⟩) earlier
      · exact appendGate_old (g := ⟨.and,[base,i]⟩) earlier
    have evaluated (x : List Bool) (length : x.length = n) :
        value D x (nextWire n C) = binaryValue conjunction (value C x base) (value C x i) := by
      rw [← length]
      cases conjunction
      · exact appendOr_new C x base i
      · exact appendAnd_new C x base i
    obtain ⟨hasBasis,hasReads,output,finalSize,finalNot,wires⟩ :=
      ih D (nextWire n C) forms previous (by rw [growth]; omega)
        (fun j hj => (valid j (List.mem_cons_of_mem _ hj)).trans (by rw [growth]; omega))
    refine ⟨hasBasis,hasReads,output,?_,finalNot.trans nots,?_⟩
    · change (foldBinary n conjunction D (nextWire n C) rest).1.size = C.size + (i :: rest).length
      rw [finalSize,size,List.length_cons]
      omega
    · intro x length
      obtain ⟨old,current⟩ := wires x length
      refine ⟨fun j hj => (old j (hj.trans (by rw [growth]; omega))).trans (persist x length j hj),?_⟩
      change value (foldBinary n conjunction D (nextWire n C) rest).1 x
        (foldBinary n conjunction D (nextWire n C) rest).2 =
        (i :: rest).foldl (fun acc j => binaryValue conjunction acc (value C x j)) (value C x base)
      rw [List.foldl_cons,current,evaluated x length]
      exact fold_values conjunction rest (value D x) (value C x)
        (fun j hj => persist x length j (valid j (List.mem_cons_of_mem _ hj))) _

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def withConstants {n : ℕ} (x : Input n) : List Bool := List.ofFn x ++ [false,true]

@[local simp] theorem withConstants_length {n : ℕ} (x : Input n) :
    (withConstants x).length = n+2 := by simp [withConstants]

theorem input_value {n : ℕ} (C : Circuit) (x : Input n) (i : Fin n) :
    value C (withConstants x) i.val = x i := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  have inside : i.val < (List.ofFn x).length := by simpa using i.isLt
  simp only [withConstants,List.getD_eq_getElem?_getD,List.getElem?_append_left inside]
  simp [List.getElem?_ofFn,i.isLt]

theorem false_value {n : ℕ} (C : Circuit) (x : Input n) :
    value C (withConstants x) n = false := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  simp [withConstants,List.getD_eq_getElem?_getD]

theorem true_value {n : ℕ} (C : Circuit) (x : Input n) :
    value C (withConstants x) (n+1) = true := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  have outside : (List.ofFn x).length ≤ n+1 := by simp
  simp [withConstants,List.getD_eq_getElem?_getD,List.getElem?_append_right outside]

def coneIndices {n : ℕ} (u : Input n) : List ℕ :=
  ((List.finRange n).filter u).map (fun i => i.val)

theorem coneIndices_length {n : ℕ} (u : Input n) : (coneIndices u).length ≤ n := by
  simpa [coneIndices] using List.length_filter_le (p := u) (l := List.finRange n)

private theorem fold_and_true (inputs : List ℕ) (bits : ℕ → Bool) (base : Bool) :
    inputs.foldl (fun b i => b && bits i) base = true ↔
      base = true ∧ ∀ i ∈ inputs, bits i = true := by
  induction inputs generalizing base with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons,ih,Bool.and_eq_true,List.mem_cons,forall_eq_or_imp,and_assoc]

def emitCone {n : ℕ} (C : Circuit) (u : Input n) : Circuit × ℕ :=
  foldBinary (n+2) true C (n+1) (coneIndices u)

theorem emitCone_spec {n : ℕ} (C : Circuit) (u : Input n)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    let result := emitCone C u
    FanInTwo result.1 ∧ ReadsBack (n+2) result.1 ∧ result.2 < nextWire (n+2) result.1 ∧
      C.size ≤ result.1.size ∧ result.1.size ≤ C.size+n ∧ notCount result.1 = notCount C ∧
      (∀ x : Input n, ∀ i < nextWire (n+2) C,
        value result.1 (withConstants x) i = value C (withConstants x) i) ∧
      ∀ x : Input n, value result.1 (withConstants x) result.2 = true ↔ u ≤ x := by
  have validBase : n+1 < nextWire (n+2) C := by unfold nextWire; omega
  have valid : ∀ i ∈ coneIndices u, i < nextWire (n+2) C := by
    intro i hm
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
    unfold nextWire
    omega
  obtain ⟨newBasis,newReads,output,size,neg,sem⟩ :=
    foldBinary_spec (n+2) true C (n+1) (coneIndices u) basis reads validBase valid
  refine ⟨newBasis,newReads,output,(Nat.le_add_right _ _).trans size.ge,size.le.trans
    (Nat.add_le_add_left (coneIndices_length u) _),neg,?_,?_⟩
  · intro x i hi
    exact (sem (withConstants x) (withConstants_length x)).1 i hi
  · intro x
    have evaluated := (sem (withConstants x) (withConstants_length x)).2
    change value (foldBinary (n+2) true C (n+1) (coneIndices u)).1 (withConstants x)
        (foldBinary (n+2) true C (n+1) (coneIndices u)).2 = true ↔ u ≤ x
    rw [evaluated,true_value]
    simp only [binaryValue,ite_true,fold_and_true,true_and]
    rw [cone_iff]
    constructor
    · intro every i active
      have mem : i.val ∈ coneIndices u := List.mem_map.mpr
        ⟨i,List.mem_filter.mpr ⟨List.mem_finRange _,active⟩,rfl⟩
      exact (input_value C x i).symm.trans (every i.val mem)
    · intro above i mem
      obtain ⟨j,selected,rfl⟩ := List.mem_map.mp mem
      exact (input_value C x j).trans (above j (List.mem_filter.mp selected).2)

def emitCones {n : ℕ} (C : Circuit) : List (Input n) → Circuit × List ℕ
  | [] => (C,[])
  | u :: rest =>
    let first := emitCone C u
    let later := emitCones first.1 rest
    (later.1,first.2 :: later.2)

theorem emitCones_spec {n : ℕ} (C : Circuit) (words : List (Input n))
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    let result := emitCones C words
    FanInTwo result.1 ∧ ReadsBack (n+2) result.1 ∧ C.size ≤ result.1.size ∧
      result.1.size ≤ C.size+n*words.length ∧ notCount result.1 = notCount C ∧
      (∀ x : Input n, ∀ i < nextWire (n+2) C,
        value result.1 (withConstants x) i = value C (withConstants x) i) ∧
      List.Forall₂ (fun u i => i < nextWire (n+2) result.1 ∧
        ∀ x : Input n, value result.1 (withConstants x) i = true ↔ u ≤ x) words result.2 := by
  induction words generalizing C with
  | nil => exact ⟨basis,reads,le_rfl,by simp [emitCones],rfl,fun _ _ _ => rfl,.nil⟩
  | cons u rest ih =>
    let first := emitCone C u
    let later := emitCones first.1 rest
    obtain ⟨headBasis,headReads,headWire,growth,headCost,headNot,headOld,headValue⟩ :=
      emitCone_spec C u basis reads
    obtain ⟨tailBasis,tailReads,tailGrowth,tailCost,tailNot,tailOld,tailValues⟩ :=
      ih first.1 headBasis headReads
    have headValid : first.2 < nextWire (n+2) later.1 := by
      exact headWire.trans_le (Nat.add_le_add_left tailGrowth (n+2))
    refine ⟨tailBasis,tailReads,growth.trans tailGrowth,?_,tailNot.trans headNot,?_,?_⟩
    · change later.1.size ≤ C.size + n * (u :: rest).length
      rw [List.length_cons,Nat.mul_succ]
      change later.1.size ≤ first.1.size + n*rest.length at tailCost
      change first.1.size ≤ C.size+n at headCost
      omega
    · intro x i hi
      have through : i < nextWire (n+2) first.1 :=
        hi.trans_le (Nat.add_le_add_left growth (n+2))
      exact (tailOld x i through).trans (headOld x i hi)
    · refine .cons ⟨headValid,?_⟩ tailValues
      intro x
      change value later.1 (withConstants x) first.2 = true ↔ u ≤ x
      rw [tailOld x first.2 headWire]
      exact headValue x

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def appendGates (C : Circuit) (gates : List Gate) : Circuit := ⟨C.gates ++ gates, C.output⟩

def appendFamily {k : Nat} (C : Circuit) (gate : Fin k → Gate) : Circuit :=
  appendGates C (List.ofFn gate)

private theorem appendGates_cons (C : Circuit) (g : Gate) (rest : List Gate) :
    appendGates C (g :: rest) = appendGates (appendGate C g) rest := by
  simp [appendGates,appendGate,List.append_assoc]

theorem appendGates_prefix (C : Circuit) (gates : List Gate) : C.gates <+: (appendGates C gates).gates :=
  ⟨gates,rfl⟩

@[local simp] theorem appendGates_size (C : Circuit) (gates : List Gate) :
    (appendGates C gates).size = C.size + gates.length := by
  simp [appendGates,Circuit.size]

@[local simp] theorem appendGates_nextWire (n : Nat) (C : Circuit) (gates : List Gate) :
    nextWire n (appendGates C gates) = nextWire n C + gates.length := by
  simp [nextWire,Nat.add_assoc]

@[local simp] theorem appendGates_output (C : Circuit) (gates : List Gate) :
    (appendGates C gates).output = C.output := rfl

theorem appendGates_notCount (C : Circuit) (gates : List Gate) :
    notCount (appendGates C gates) =
      notCount C + (gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)).length := by
  simp [notCount,appendGates]

theorem appendGates_notCount_eq {C : Circuit} {gates : List Gate}
    (noNot : ∀ g ∈ gates, g.op ≠ .not) : notCount (appendGates C gates) = notCount C := by
  have empty : (gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)) = [] :=
    List.filter_eq_nil_iff.mpr fun g member => by simp [noNot g member]
  simp [appendGates_notCount,empty]

private abbrev GateShape (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem appendGates_fanInTwo {C : Circuit} {gates : List Gate} (basis : FanInTwo C)
    (shape : ∀ g ∈ gates, GateShape g) : FanInTwo (appendGates C gates) := by
  intro g member
  rcases List.mem_append.mp member with old | added
  · exact basis g old
  · exact shape g added

theorem appendGates_readsBack {n : Nat} {C : Circuit} {gates : List Gate} (valid : ReadsBack n C)
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire n C) : ReadsBack n (appendGates C gates) := by
  induction gates generalizing C with
  | nil => simpa [appendGates] using valid
  | cons g rest ih =>
    rw [appendGates_cons]
    have fits : ∀ i ∈ g.inputs, i < nextWire n C := reads g (List.mem_cons_self ..)
    apply ih (appendGate_readsBack valid fits)
    intro h member i input
    exact Nat.lt_of_lt_of_le (reads h (List.mem_cons_of_mem _ member) i input)
      (nextWire_le_of_prefix (appendGate_prefix C g))

theorem appendGates_old {C : Circuit} {gates : List Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendGates C gates) x i = value C x i :=
  value_of_prefix (appendGates_prefix C gates) valid

private def readGate (C : Circuit) (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (value C x))

private theorem appendGates_wires {C : Circuit} {gates : List Gate} {x : List Bool}
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire x.length C) :
    (appendGates C gates).wires x = C.wires x ++ gates.map (readGate C x) := by
  induction gates generalizing C with
  | nil => simp [appendGates]
  | cons g rest ih =>
    have restReads : ∀ h ∈ rest, ∀ i ∈ h.inputs, i < nextWire x.length (appendGate C g) :=
      fun h member i input => Nat.lt_of_lt_of_le (reads h (List.mem_cons_of_mem _ member) i input)
        (nextWire_le_of_prefix (appendGate_prefix C g))
    have tail : rest.map (readGate (appendGate C g) x) = rest.map (readGate C x) := by
      apply List.map_congr_left
      intro h member
      unfold readGate
      apply congrArg h.op.eval
      apply List.map_congr_left
      intro i input
      exact appendGate_old (g := g) (reads h (List.mem_cons_of_mem _ member) i input)
    rw [appendGates_cons,ih restReads,tail,appendGate_wires]
    simp [List.append_assoc,readGate]

theorem appendGates_new {C : Circuit} {gates : List Gate} {x : List Bool}
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire x.length C) (j : Fin gates.length) :
    value (appendGates C gates) x (nextWire x.length C + j.val) =
      gates[j].op.eval (gates[j].inputs.map (value C x)) := by
  change ((appendGates C gates).wires x).getD (nextWire x.length C + j.val) false = _
  rw [appendGates_wires (x := x) reads]
  have within : (C.wires x).length ≤ nextWire x.length C + j.val := by rw [wires_length]; omega
  have index : nextWire x.length C + j.val - nextWire x.length C = j.val := by omega
  rw [List.getD_append_right _ _ _ _ within,wires_length,index]
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem j.isLt,readGate]

theorem appendFamily_prefix {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    C.gates <+: (appendFamily C gate).gates := appendGates_prefix C _

@[local simp] theorem appendFamily_size {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    (appendFamily C gate).size = C.size + k := by simp [appendFamily]

@[local simp] theorem appendFamily_nextWire {k : Nat} (n : Nat) (C : Circuit) (gate : Fin k → Gate) :
    nextWire n (appendFamily C gate) = nextWire n C + k := by simp [appendFamily]

@[local simp] theorem appendFamily_output {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    (appendFamily C gate).output = C.output := rfl

theorem appendFamily_notCount {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    notCount (appendFamily C gate) = notCount C +
      ((List.ofFn gate).filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)).length :=
  appendGates_notCount C _

theorem appendFamily_notCount_eq {k : Nat} {C : Circuit} {gate : Fin k → Gate}
    (noNot : ∀ j, (gate j).op ≠ .not) : notCount (appendFamily C gate) = notCount C := by
  apply appendGates_notCount_eq
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact noNot j

theorem appendFamily_fanInTwo {k : Nat} {C : Circuit} {gate : Fin k → Gate} (basis : FanInTwo C)
    (shape : ∀ j, GateShape (gate j)) : FanInTwo (appendFamily C gate) := by
  apply appendGates_fanInTwo basis
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact shape j

theorem appendFamily_readsBack {k n : Nat} {C : Circuit} {gate : Fin k → Gate}
    (valid : ReadsBack n C) (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire n C) :
    ReadsBack n (appendFamily C gate) := by
  apply appendGates_readsBack valid
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact reads j

theorem appendFamily_old {k : Nat} {C : Circuit} {gate : Fin k → Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendFamily C gate) x i = value C x i :=
  appendGates_old valid

theorem appendFamily_new {k : Nat} {C : Circuit} {gate : Fin k → Gate} {x : List Bool}
    (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire x.length C) (j : Fin k) :
    value (appendFamily C gate) x (nextWire x.length C + j.val) =
      (gate j).op.eval ((gate j).inputs.map (value C x)) := by
  have readsList : ∀ g ∈ List.ofFn gate, ∀ i ∈ g.inputs, i < nextWire x.length C := by
    intro g member
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp member
    exact reads t
  let t : Fin (List.ofFn gate).length := ⟨j.val,by simpa using j.isLt⟩
  simpa [appendFamily,t] using appendGates_new readsList t

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem appendBinary_prefix (conjunction : Bool) (C : Circuit) (a b : ℕ) :
    C.gates <+: (appendBinary conjunction C a b).gates := by
  cases conjunction
  · exact appendGate_prefix C ⟨.or,[a,b]⟩
  · exact appendGate_prefix C ⟨.and,[a,b]⟩

theorem foldBinary_prefix (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ) (indices : List ℕ) :
    C.gates <+: (foldBinary n conjunction C base indices).1.gates := by
  induction indices generalizing C base with
  | nil => exact List.prefix_refl _
  | cons i rest ih =>
    exact (appendBinary_prefix conjunction C base i).trans (ih _ _)

theorem foldBinary_size_exact (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ)
    (indices : List ℕ) : (foldBinary n conjunction C base indices).1.size = C.size + indices.length := by
  induction indices generalizing C base with
  | nil => simp [foldBinary]
  | cons i rest ih =>
    have step : (appendBinary conjunction C base i).size = C.size + 1 := by
      cases conjunction <;> simp [appendBinary]
    rw [foldBinary,ih,step,List.length_cons]
    omega

theorem emitCone_prefix {n : ℕ} (C : Circuit) (u : Input n) :
    C.gates <+: (emitCone C u).1.gates := foldBinary_prefix _ _ _ _ _

theorem emitCone_size_exact {n : ℕ} (C : Circuit) (u : Input n) :
    (emitCone C u).1.size = C.size + (coneIndices u).length := foldBinary_size_exact _ _ _ _ _

theorem emitCones_prefix {n : ℕ} (C : Circuit) (words : List (Input n)) :
    C.gates <+: (emitCones C words).1.gates := by
  induction words generalizing C with
  | nil => exact List.prefix_refl _
  | cons u rest ih => exact (emitCone_prefix C u).trans (ih (emitCone C u).1)

theorem emitCones_size_exact {n : ℕ} (C : Circuit) (words : List (Input n)) :
    (emitCones C words).1.size = C.size + (words.map (fun u => (coneIndices u).length)).sum := by
  induction words generalizing C with
  | nil => simp [emitCones]
  | cons u rest ih =>
    change (emitCones (emitCone C u).1 rest).1.size = C.size + _
    rw [ih,emitCone_size_exact,List.map_cons,List.sum_cons]
    omega

theorem supportConeTable {n m : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    ∃ (D : Circuit) (wire : {u : Input n // u ∈ support P N} → ℕ),
      C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ C.size + n*(support P N).card ∧ notCount D = notCount C ∧
      ∀ u, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u.val ≤ x := by
  classical
  let words := (support P N).toList
  let result := emitCones C words
  obtain ⟨newBasis,newReads,_,cost,neg,_,paired⟩ := emitCones_spec C words basis reads
  have available (u : {u : Input n // u ∈ support P N}) :
      ∃ i, i < nextWire (n+2) result.1 ∧
        ∀ x : Input n, value result.1 (withConstants x) i = true ↔ u.val ≤ x := by
    have member : u.val ∈ words := Finset.mem_toList.mpr u.property
    obtain ⟨j,point⟩ := List.mem_iff_get.mp member
    let k : Fin result.2.length := ⟨j.val,by rw [← paired.length_eq]; exact j.isLt⟩
    refine ⟨result.2.get k,?_⟩
    have atIndex := paired.get j.isLt k.isLt
    change result.2.get k < nextWire (n+2) result.1 ∧
      (∀ x : Input n, value result.1 (withConstants x) (result.2.get k) = true ↔ words.get j ≤ x) at atIndex
    simpa only [point] using atIndex
  refine ⟨result.1,fun u => (available u).choose,emitCones_prefix C words,newBasis,newReads,?_,neg,?_⟩
  · simpa only [words,Finset.length_toList] using cost
  · intro u
    exact (available u).choose_spec

theorem supportConeTable_total {n m : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    ∃ (D : Circuit) (wire : Input n → ℕ), C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ C.size + n*(support P N).card ∧ notCount D = notCount C ∧
      (∀ u ∈ support P N, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u ≤ x) ∧
      ∀ u ∉ support P N, wire u = n := by
  classical
  obtain ⟨D,w,extension,newBasis,newReads,cost,neg,semantic⟩ := supportConeTable P N C basis reads
  let wire (u : Input n) : ℕ := if h : u ∈ support P N then w ⟨u,h⟩ else n
  refine ⟨D,wire,extension,newBasis,newReads,cost,neg,?_,?_⟩
  · intro u member
    simpa [wire,member] using semantic ⟨u,member⟩
  · intro u absent
    simp [wire,absent]

theorem supportConeTable_empty {n m : ℕ} (P N : Input n → Fin m → Prop) :
    ∃ (D : Circuit) (wire : Input n → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ n*(support P N).card ∧ notCount D = 0 ∧
      (∀ u ∈ support P N, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u ≤ x) ∧
      ∀ u ∉ support P N, wire u = n := by
  obtain ⟨D,w,_,basis,reads,cost,neg,semantic,defaultWire⟩ :=
    supportConeTable_total P N emptyCircuit emptyCircuit_fanInTwo (emptyCircuit_readsBack (n+2))
  exact ⟨D,w,basis,reads,by simpa using cost,by simpa using neg,semantic,defaultWire⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem fold_or_true (indices : List ℕ) (bits : ℕ → Bool) (base : Bool) :
    indices.foldl (fun b i => b || bits i) base = true ↔
      base = true ∨ ∃ i ∈ indices, bits i = true := by
  induction indices generalizing base with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons,ih,Bool.or_eq_true_iff]
    constructor
    · rintro ((on | on) | ⟨j,mem,on⟩)
      · exact Or.inl on
      · exact Or.inr ⟨i,List.mem_cons_self ..,on⟩
      · exact Or.inr ⟨j,List.mem_cons_of_mem _ mem,on⟩
    · rintro (on | ⟨j,mem,on⟩)
      · exact Or.inl (Or.inl on)
      · rcases List.mem_cons.mp mem with rfl | restMem
        · exact Or.inl (Or.inr on)
        · exact Or.inr ⟨j,restMem,on⟩

theorem append_or_rows {n k : ℕ} (C : Circuit) (rows : Fin k → List ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (rowValid : ∀ i a, a ∈ rows i → a < nextWire (n+2) C) :
    ∃ (D : Circuit) (out : Fin k → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size = C.size + (∑ i : Fin k, (rows i).length) ∧
      (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔
        ∃ a ∈ rows i, value C (withConstants x) a = true := by
  induction k generalizing C with
  | zero =>
    exact ⟨C,Fin.elim0,basis,reads,List.prefix_rfl,rfl,by simp,fun i => Fin.elim0 i,
      fun _ i => Fin.elim0 i⟩
  | succ k ih =>
    let first := foldBinary (n+2) false C n (rows 0)
    have zeroLive : n < nextWire (n+2) C := by unfold nextWire; omega
    obtain ⟨hBasis,hReads,hLive,hSize,hNot,hEval⟩ :=
      foldBinary_spec (n+2) false C n (rows 0) basis reads zeroLive (rowValid 0)
    have firstPrefix : C.gates <+: first.1.gates := by
      unfold first
      apply foldBinary_prefix
    have tailValid (i : Fin k) (a : ℕ) (ha : a ∈ rows i.succ) :
        a < nextWire (n+2) first.1 :=
      (rowValid i.succ a ha).trans_le (nextWire_le_of_prefix firstPrefix)
    obtain ⟨D,tail,dBasis,dReads,dPrefix,dNot,dSize,dLive,dEval⟩ :=
      ih first.1 (fun i => rows i.succ) hBasis hReads tailValid
    let out : Fin (k+1) → ℕ := Fin.cases first.2 tail
    refine ⟨D,out,dBasis,dReads,firstPrefix.trans dPrefix,dNot.trans hNot,?_,?_,?_⟩
    · rw [dSize,Fin.sum_univ_succ]
      change first.1.size = C.size + (rows 0).length at hSize
      rw [hSize,Nat.add_assoc]
    · intro i
      refine Fin.cases ?_ (fun j => dLive j) i
      exact hLive.trans_le (nextWire_le_of_prefix dPrefix)
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · change value D (withConstants x) first.2 = true ↔ _
        have live : first.2 < nextWire (withConstants x).length first.1 := by
          simpa only [withConstants_length] using hLive
        rw [value_of_prefix dPrefix live]
        change value (foldBinary (n+2) false C n (rows 0)).1 (withConstants x)
          (foldBinary (n+2) false C n (rows 0)).2 = true ↔ _
        rw [(hEval (withConstants x) (withConstants_length x)).2,false_value]
        simp only [binaryValue,Bool.false_eq_true,ite_false,fold_or_true,false_or]
      · change value D (withConstants x) (tail j) = true ↔ _
        rw [dEval x j]
        constructor <;> rintro ⟨a,mem,on⟩
        · exact ⟨a,mem,((hEval (withConstants x) (withConstants_length x)).1 a
            (rowValid j.succ a mem)).symm.trans on⟩
        · exact ⟨a,mem,((hEval (withConstants x) (withConstants_length x)).1 a
            (rowValid j.succ a mem)).trans on⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem value_prefix_input {n : ℕ} {C D : Circuit}
    (extension : C.gates <+: D.gates) (x : Input n) {i : ℕ} (live : i < nextWire (n+2) C) :
    value D (withConstants x) i = value C (withConstants x) i :=
  value_of_prefix extension (by simpa only [withConstants_length] using live)

theorem append_suffix_or {n k : ℕ} (C : Circuit) (bucket : Fin k → ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) (live : ∀ i, bucket i < nextWire (n+2) C) :
    ∃ (D : Circuit) (out : Fin k → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size = C.size+k ∧ (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔
        ∃ j : Fin k, i ≤ j ∧ value C (withConstants x) (bucket j) = true := by
  induction k generalizing C with
  | zero => exact ⟨C,Fin.elim0,basis,reads,List.prefix_rfl,rfl,by simp,fun i => Fin.elim0 i,
      fun _ i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨B,tail,bBasis,bReads,bPrefix,bNot,bSize,bLive,bEval⟩ :=
      ih C (fun j => bucket j.succ) basis reads (fun j => live j.succ)
    let lower := if reaches : 0 < k then tail ⟨0,reaches⟩ else n
    have lowerLive : lower < nextWire (n+2) B := by
      unfold lower
      split
      · exact bLive _
      · unfold nextWire
        omega
    have lowerEval (x : Input n) : value B (withConstants x) lower = true ↔
        ∃ j : Fin k, value C (withConstants x) (bucket j.succ) = true := by
      unfold lower
      split
      · rename_i positive
        rw [bEval x ⟨0,positive⟩]
        constructor
        · rintro ⟨j,_,on⟩
          exact ⟨j,on⟩
        · rintro ⟨j,on⟩
          exact ⟨j,show (0 : ℕ) ≤ j.val from Nat.zero_le _,on⟩
      · rename_i empty
        rw [false_value]
        constructor
        · intro impossible
          contradiction
        · rintro ⟨j,_⟩
          exact (empty (Nat.zero_lt_of_lt j.isLt)).elim
    let D := appendOr B (bucket 0) lower
    let out : Fin (k+1) → ℕ := Fin.cases (nextWire (n+2) B) tail
    have headLive := (live 0).trans_le (nextWire_le_of_prefix bPrefix)
    have lastPrefix : B.gates <+: D.gates := appendGate_prefix _ _
    have wireGrowth : nextWire (n+2) D = nextWire (n+2) B + 1 := nextWire_appendGate _ _ _
    refine ⟨D,out,appendOr_fanInTwo bBasis,appendOr_readsBack bReads headLive lowerLive,
      bPrefix.trans lastPrefix,(appendOr_notCount _ _ _).trans bNot,?_,?_,?_⟩
    · change (appendOr B (bucket 0) lower).size = C.size + (k+1)
      rw [appendOr_size,bSize,Nat.add_assoc]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change nextWire (n+2) B < nextWire (n+2) D
        omega
      · exact (bLive j).trans_le (nextWire_le_of_prefix lastPrefix)
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · change value D (withConstants x) (nextWire (n+2) B) = true ↔
          ∃ j : Fin (k+1), 0 ≤ j ∧ value C (withConstants x) (bucket j) = true
        have evaluated := appendOr_new B (withConstants x) (bucket 0) lower
        simp only [withConstants_length] at evaluated
        rw [show value D (withConstants x) (nextWire (n+2) B) = _ from evaluated,
          Bool.or_eq_true_iff,value_prefix_input bPrefix x (live 0),lowerEval x]
        constructor
        · rintro (head | ⟨j,tailOn⟩)
          · exact ⟨0,le_rfl,head⟩
          · exact ⟨j.succ,show (0 : ℕ) ≤ j.succ.val from Nat.zero_le _,tailOn⟩
        · rintro ⟨j,_,on⟩
          refine Fin.cases ?_ (fun q => ?_) j on
          · exact Or.inl
          · intro tailOn
            exact Or.inr ⟨q,tailOn⟩
      · change value D (withConstants x) (tail j) = true ↔ _
        rw [value_prefix_input lastPrefix x (bLive j),bEval x j]
        constructor
        · rintro ⟨i,order,on⟩
          exact ⟨i.succ,Fin.succ_le_succ_iff.mpr order,on⟩
        · rintro ⟨i,order,on⟩
          refine Fin.cases ?_ (fun q => ?_) i order on
          · intro incompatible _
            change j.val+1 ≤ 0 at incompatible
            omega
          · intro comparable active
            exact ⟨q,Fin.succ_le_succ_iff.mp comparable,active⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private noncomputable def bucketRows {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ)
    (cone : Input n → ℕ) (i : Fin d) : List ℕ :=
  (rankBucket P N d (i.val+1)).toList.map cone

private theorem positive_bucket_cost {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ)
    (cone : Input n → ℕ) :
    (∑ i : Fin d, (bucketRows P N d cone i).length) ≤ (support P N).card := by
  have total : (∑ i : Fin (d+1), (rankBucket P N d i.val).card) = (support P N).card :=
    (Fin.sum_univ_eq_sum_range (fun k => (rankBucket P N d k).card) (d+1)).trans (rank_bucket_count P N d)
  rw [Fin.sum_univ_succ] at total
  have bound : (∑ i : Fin d, (rankBucket P N d (i.val+1)).card) ≤ (support P N).card :=
    (Nat.le_add_left _ _).trans total.le
  simpa [bucketRows] using bound

theorem append_thresholds {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ) (C : Circuit)
    (cone : Input n → ℕ) (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (coneLive : ∀ u ∈ support P N, cone u < nextWire (n+2) C)
    (coneValue : ∀ u ∈ support P N, ∀ x : Input n,
      value C (withConstants x) (cone u) = true ↔ u ≤ x) :
    ∃ (D : Circuit) (out : Fin d → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size ≤ C.size+(support P N).card+d ∧
      (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔ i.val+1 ≤ rank P N d x := by
  let rows := bucketRows P N d cone
  have liveRows (i : Fin d) (a : ℕ) (hm : a ∈ rows i) : a < nextWire (n+2) C := by
    obtain ⟨u,mem,rfl⟩ := List.mem_map.mp hm
    exact coneLive u ((mem_rankBucket P N d (i.val+1) u).mp (Finset.mem_toList.mp mem)).1
  obtain ⟨B,bucket,bBasis,bReads,bPrefix,bNot,bSize,bLive,bEval⟩ :=
    append_or_rows C rows basis reads liveRows
  have bucketEval (x : Input n) (i : Fin d) :
      value B (withConstants x) (bucket i) = true ↔ ∃ u ∈ rankBucket P N d (i.val+1), u ≤ x := by
    rw [bEval x i]
    constructor
    · rintro ⟨a,found,on⟩
      obtain ⟨u,mem,rfl⟩ := List.mem_map.mp found
      have occurrence := Finset.mem_toList.mp mem
      have original := ((mem_rankBucket P N d (i.val+1) u).mp occurrence).1
      exact ⟨u,occurrence,(coneValue u original x).mp on⟩
    · rintro ⟨u,mem,ux⟩
      have original := ((mem_rankBucket P N d (i.val+1) u).mp mem).1
      exact ⟨cone u,List.mem_map.mpr ⟨u,Finset.mem_toList.mpr mem,rfl⟩,
        (coneValue u original x).mpr ux⟩
  obtain ⟨D,out,dBasis,dReads,dPrefix,dNot,dSize,dLive,dEval⟩ :=
    append_suffix_or B bucket bBasis bReads bLive
  refine ⟨D,out,dBasis,dReads,bPrefix.trans dPrefix,dNot.trans bNot,?_,dLive,?_⟩
  · have budget : (∑ i : Fin d, (rows i).length) ≤ (support P N).card :=
      positive_bucket_cost P N d cone
    rw [dSize,bSize]
    omega
  · intro x i
    rw [dEval x i,threshold_buckets P N d (by omega : 0 < i.val+1) x]
    constructor
    · rintro ⟨j,ij,on⟩
      have below : i.val ≤ j.val := ij
      obtain ⟨u,mem,ux⟩ := (bucketEval x j).mp on
      exact ⟨j.val+1,by omega,by omega,u,mem,ux⟩
    · rintro ⟨k,ik,kd,u,mem,ux⟩
      let j : Fin d := ⟨k-1,by omega⟩
      have level : j.val+1 = k := by dsimp [j]; omega
      refine ⟨j,show i.val ≤ j.val from by omega,(bucketEval x j).mpr ?_⟩
      rw [level]
      exact ⟨u,mem,ux⟩

theorem threshold_antitone {n m d : ℕ} {P N : Input n → Fin m → Prop} {D : Circuit}
    {out : Fin d → ℕ}
    (sem : ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔ i.val+1 ≤ rank P N d x)
    (x : Input n) : Antitone (fun i => value D (withConstants x) (out i)) := by
  intro i j ij
  change value D (withConstants x) (out j) ≤ value D (withConstants x) (out i)
  have below : i.val ≤ j.val := ij
  cases high : value D (withConstants x) (out j)
  · simp
  · have low : value D (withConstants x) (out i) = true :=
      (sem x i).mpr (by have reach := (sem x j).mp high; omega)
    rw [low]

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)
open Thermometer (half middle pivot lowerSource upperSource lowerSlot upperSlot
  lowerWord upperWord folded folded_antitone decoded decoded_lower decoded_pivot decoded_upper
  decoded_correct half_lt_pow)

private theorem old_value {n : ℕ} {C D : Circuit} (ext : C.gates <+: D.gates)
    {x : List Bool} (length : x.length = n) {w : ℕ} (live : w < nextWire n C) :
    value D x w = value C x w :=
  value_of_prefix ext (by simpa only [length] using live)

private theorem pair_reads {n : ℕ} {C : Circuit} {a b : ℕ}
    (la : a < nextWire n C) (lb : b < nextWire n C) :
    ∀ i ∈ [a,b], i < nextWire n C := by
  intro i member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact la
  · exact lb

private theorem family_value {k n : ℕ} {C : Circuit} {gate : Fin k → Gate}
    (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire n C)
    (x : List Bool) (length : x.length = n) (j : Fin k) :
    value (appendFamily C gate) x (nextWire n C + j.val) =
      (gate j).op.eval ((gate j).inputs.map (value C x)) := by
  have valid : ∀ a b, b ∈ (gate a).inputs → b < nextWire x.length C := by
    rw [length]
    exact reads
  simpa only [length] using appendFamily_new (C := C) (gate := gate) (x := x) valid j

set_option maxHeartbeats 1700000 in
private theorem fold_taps {X : Type*} (input : X → List Bool) {n d : ℕ}
    (length : ∀ x, (input x).length = n) (positive : 0 < d) {C : Circuit}
    (fan : FanInTwo C) (back : ReadsBack n C)
    (falseWire : ℕ) (falseLive : falseWire < nextWire n C)
    (falseValue : ∀ x, value C (input x) falseWire = false)
    (taps : Fin d → ℕ) (live : ∀ i, taps i < nextWire n C) :
    ∃ (D : Circuit) (pivotWire : ℕ) (wires : Fin (half d) → ℕ),
      C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack n D ∧
      pivotWire < nextWire n D ∧ (∀ i, wires i < nextWire n D) ∧
      (∀ x, value D (input x) pivotWire = !value C (input x) (taps (pivot positive))) ∧
      (∀ x i, value D (input x) (wires i) =
        folded positive (fun j => value C (input x) (taps j)) i) ∧
      D.size = C.size + 1 + 2 * half d ∧ notCount D = notCount C + 1 := by
  let C0 := appendNot C (taps (pivot positive))
  let b := nextWire n C
  let low (i : Fin (half d)) := if i.val < middle d then taps (lowerSource i) else falseWire
  let ands (i : Fin (half d)) : Gate := ⟨.and,[b,low i]⟩
  let C1 := appendFamily C0 ands
  let mask (i : Fin (half d)) := nextWire n C0 + i.val
  let ors (i : Fin (half d)) : Gate := ⟨.or,[mask i,taps (upperSource positive i)]⟩
  let C2 := appendFamily C1 ors
  let output (i : Fin (half d)) := nextWire n C1 + i.val
  have e0 : C.gates <+: C0.gates := appendGate_prefix C _
  have e1 : C0.gates <+: C1.gates := appendFamily_prefix C0 ands
  have e2 : C1.gates <+: C2.gates := appendFamily_prefix C1 ors
  have e01 := e0.trans e1
  have e012 := e01.trans e2
  have bLive : b < nextWire n C0 := by
    simp [b,C0,appendNot]
  have lowLive (i : Fin (half d)) : low i < nextWire n C0 := by
    apply Nat.lt_of_lt_of_le _ (nextWire_le_of_prefix e0)
    unfold low
    split
    · exact live _
    · exact falseLive
  have andReads : ∀ j i, i ∈ (ands j).inputs → i < nextWire n C0 :=
    fun j => pair_reads bLive (lowLive j)
  have maskLive (i : Fin (half d)) : mask i < nextWire n C1 := by
    simpa only [mask,C1,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
  have orReads : ∀ j i, i ∈ (ors j).inputs → i < nextWire n C1 :=
    fun j => pair_reads (maskLive j) ((live _).trans_le (nextWire_le_of_prefix e01))
  have f0 : FanInTwo C0 := appendNot_fanInTwo fan
  have f1 : FanInTwo C1 := appendFamily_fanInTwo (gate := ands) f0 (by
    intro j
    change GateOp.and ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      ([b,low j] : List ℕ).length ≤ 2
    simp)
  have f2 : FanInTwo C2 := appendFamily_fanInTwo (gate := ors) f1 (by
    intro j
    change GateOp.or ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      ([mask j,taps (upperSource positive j)] : List ℕ).length ≤ 2
    simp)
  have r0 : ReadsBack n C0 := appendNot_readsBack back (live (pivot positive))
  have r1 : ReadsBack n C1 := appendFamily_readsBack r0 andReads
  have r2 : ReadsBack n C2 := appendFamily_readsBack r1 orReads
  have atPivot (x : X) : value C0 (input x) b = !value C (input x) (taps (pivot positive)) := by
    simpa only [C0,b,length x] using appendNot_new C (input x) (taps (pivot positive))
  have foldOn (x : X) (i : Fin (half d)) : value C2 (input x) (output i) =
      folded positive (fun j => value C (input x) (taps j)) i := by
    let w : Fin d → Bool := fun j => value C (input x) (taps j)
    have lowOn : value C0 (input x) (low i) = lowerWord w i := by
      by_cases before : i.val < middle d
      · simp only [low,lowerWord,ite_eq_left before]
        exact old_value e0 (length x) (live (lowerSource i))
      · simp only [low,lowerWord,ite_eq_right before]
        exact (old_value e0 (length x) falseLive).trans (falseValue x)
    have maskOn : value C1 (input x) (mask i) = (!w (pivot positive) && lowerWord w i) := by
      have eq := family_value (gate := ands) andReads (input x) (length x) i
      simpa [C1,mask,ands,GateOp.eval,atPivot x,lowOn,w] using eq
    have upperOn : value C1 (input x) (taps (upperSource positive i)) = upperWord positive w i :=
      old_value e01 (length x) (live (upperSource positive i))
    have eq := family_value (gate := ors) orReads (input x) (length x) i
    simpa [C2,output,ors,GateOp.eval,maskOn,upperOn,folded,w] using eq
  refine ⟨C2,b,output,e012,f2,r2,bLive.trans_le (nextWire_le_of_prefix (e1.trans e2)),
    ?_,?_,foldOn,?_,?_⟩
  · intro i
    simpa only [output,C2,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
  · intro x
    exact (old_value (e1.trans e2) (length x) bLive).trans (atPivot x)
  · dsimp only [C2,C1,C0]
    simp only [appendFamily_size,appendNot_size]
    omega
  · rw [show C2 = appendFamily C1 ors from rfl,
      appendFamily_notCount_eq (gate := ors) (by intro j; simp [ors]),
      show C1 = appendFamily C0 ands from rfl,
      appendFamily_notCount_eq (gate := ands) (by intro j; simp [ands])]
    simp [C0]

private def decoderGates {d : ℕ} (positive : 0 < d) (b falseWire : ℕ)
    (tail : Fin (half d) → ℕ) (i : Fin d) : Gate :=
  if before : i.val < middle d then ⟨.and,[b,tail (lowerSlot i before)]⟩
  else if eq : i.val = middle d then ⟨.or,[b,falseWire]⟩
  else ⟨.or,[b,tail (upperSlot positive i (by omega))]⟩

private theorem decoder_reads {n d : ℕ} (positive : 0 < d) {C : Circuit} {b f : ℕ}
    {tail : Fin (half d) → ℕ} (liveB : b < nextWire n C) (liveF : f < nextWire n C)
    (liveTail : ∀ j, tail j < nextWire n C) :
    ∀ j i, i ∈ (decoderGates positive b f tail j).inputs → i < nextWire n C := by
  intro j i member
  unfold decoderGates at member
  split at member
  · exact pair_reads liveB (liveTail _) i member
  · split at member
    · exact pair_reads liveB liveF i member
    · exact pair_reads liveB (liveTail _) i member

private theorem decoder_value {d : ℕ} (positive : 0 < d) (C : Circuit) (x : List Bool)
    (b f : ℕ) (tail : Fin (half d) → ℕ) (off : value C x f = false) (i : Fin d) :
    let g := decoderGates positive b f tail i
    g.op.eval (g.inputs.map (value C x)) =
      decoded positive (value C x b) (fun j => value C x (tail j)) i := by
  rcases lt_trichotomy i.val (middle d) with before | eq | after
  · rw [decoded_lower positive _ _ _ before]
    simp [decoderGates,before,GateOp.eval]
  · rw [decoded_pivot positive _ _ _ eq]
    simp [decoderGates,eq,off,GateOp.eval]
  · have lower : ¬ i.val < middle d := by omega
    have other : i.val ≠ middle d := by omega
    rw [decoded_upper positive _ _ _ after]
    simp [decoderGates,lower,other,GateOp.eval]

def InversionResult {X : Type*} (input : X → List Bool) (n r : ℕ)
    (C : Circuit) {d : ℕ} (taps : Fin d → ℕ) :=
  {data : Circuit × (Fin d → ℕ) × ℕ × ℕ //
    let D := data.1
    let output := data.2.1
    let binary := data.2.2.1
    let inversions := data.2.2.2
    (C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack n D) ∧
    (∀ i, output i < nextWire n D) ∧
    (binary ≤ 4*d ∧ inversions ≤ r) ∧
    (D.size = C.size + binary + inversions ∧ notCount D = notCount C + inversions) ∧
    ∀ x i, value D (input x) (output i) = !value C (input x) (taps i)}

namespace InversionResult

variable {X : Type*} {input : X → List Bool} {n r d : ℕ}
  {C : Circuit} {taps : Fin d → ℕ}

abbrev circuit (R : InversionResult input n r C taps) : Circuit := R.val.1

abbrev wires (R : InversionResult input n r C taps) : Fin d → ℕ := R.val.2.1

abbrev binary (R : InversionResult input n r C taps) : ℕ := R.val.2.2.1

abbrev inversions (R : InversionResult input n r C taps) : ℕ := R.val.2.2.2

theorem extension (R : InversionResult input n r C taps) : C.gates <+: R.circuit.gates :=
  R.property.1.1

theorem fanInTwo (R : InversionResult input n r C taps) : FanInTwo R.circuit :=
  R.property.1.2.1

theorem readsBack (R : InversionResult input n r C taps) : ReadsBack n R.circuit :=
  R.property.1.2.2

theorem valid (R : InversionResult input n r C taps) : ∀ i, R.wires i < nextWire n R.circuit :=
  R.property.2.1

theorem binaryBound (R : InversionResult input n r C taps) : R.binary ≤ 4*d :=
  R.property.2.2.1.1

theorem inversionsBound (R : InversionResult input n r C taps) : R.inversions ≤ r :=
  R.property.2.2.1.2

theorem size_eq (R : InversionResult input n r C taps) :
    R.circuit.size = C.size + R.binary + R.inversions := R.property.2.2.2.1.1

theorem count_eq (R : InversionResult input n r C taps) :
    notCount R.circuit = notCount C + R.inversions := R.property.2.2.2.1.2

theorem computes (R : InversionResult input n r C taps) :
    ∀ x i, value R.circuit (input x) (R.wires i) = !value C (input x) (taps i) :=
  R.property.2.2.2.2

end InversionResult

theorem InversionResult.nonnot_eq {X : Type*} {input : X → List Bool} {n r d : ℕ}
    {C : Circuit} {taps : Fin d → ℕ} (R : InversionResult input n r C taps) :
    R.circuit.size - notCount R.circuit = C.size - notCount C + R.binary := by
  have fits : notCount C ≤ C.size := List.length_filter_le _ _
  rw [R.size_eq,R.count_eq]
  omega

private theorem empty_inversion {X : Type*} (input : X → List Bool) {n r : ℕ}
    {C : Circuit} (fan : FanInTwo C) (back : ReadsBack n C) (taps : Fin 0 → ℕ) :
    Nonempty (InversionResult input n r C taps) := by
  exact ⟨⟨⟨C,taps,0,0⟩,⟨⟨List.prefix_rfl,fan,back⟩,fun i => Fin.elim0 i,
    ⟨by simp,by simp⟩,⟨rfl,rfl⟩,fun _ i => Fin.elim0 i⟩⟩⟩

set_option maxHeartbeats 2000000 in

theorem invert_taps {X : Type*} (input : X → List Bool) {n : ℕ}
    (length : ∀ x, (input x).length = n) {r d : ℕ} (bound : d < 2^r)
    {C : Circuit} (fan : FanInTwo C) (back : ReadsBack n C)
    (falseWire : ℕ) (falseLive : falseWire < nextWire n C)
    (falseValue : ∀ x, value C (input x) falseWire = false)
    (taps : Fin d → ℕ) (live : ∀ i, taps i < nextWire n C)
    (ordered : ∀ x, Antitone (fun i => value C (input x) (taps i))) :
    Nonempty (InversionResult input n r C taps) := by
  induction r generalizing d C with
  | zero =>
    have empty : d = 0 := by simpa using bound
    subst d
    exact empty_inversion input fan back taps
  | succ r ih =>
    by_cases positive : 0 < d
    · obtain ⟨F,pivotWire,foldWires,fExt,fFan,fBack,pivotValid,fValid,pivotValue,foldValue,fSize,fCount⟩ :=
        fold_taps input length positive fan back falseWire falseLive falseValue taps live
      have falseF := falseLive.trans_le (nextWire_le_of_prefix (n := n) fExt)
      have offF (x : X) : value F (input x) falseWire = false :=
        (old_value fExt (length x) falseLive).trans (falseValue x)
      have foldOrdered (x : X) : Antitone (fun i => value F (input x) (foldWires i)) := by
        rw [funext (foldValue x)]
        exact folded_antitone positive (ordered x)
      obtain ⟨R⟩ := ih (half_lt_pow bound) fFan fBack falseF offF foldWires fValid foldOrdered
      let gates := decoderGates positive pivotWire falseWire R.wires
      let D := appendFamily R.circuit gates
      let output (i : Fin d) := nextWire n R.circuit + i.val
      have step := appendFamily_prefix R.circuit gates
      have preserve := nextWire_le_of_prefix (n := n) R.extension
      have reads := decoder_reads positive (pivotValid.trans_le preserve)
        (falseF.trans_le preserve) R.valid
      have noNot : ∀ j, (gates j).op ≠ .not := by
        intro j
        change (decoderGates positive pivotWire falseWire R.wires j).op ≠ .not
        unfold decoderGates
        split
        · simp
        · split <;> simp
      have basis : FanInTwo D := appendFamily_fanInTwo (gate := gates) R.fanInTwo (by
        intro j
        change (decoderGates positive pivotWire falseWire R.wires j).op ∈
          ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
          (decoderGates positive pivotWire falseWire R.wires j).inputs.length ≤ 2
        unfold decoderGates
        split
        · simp
        · split <;> simp)
      refine ⟨⟨⟨D,output,2*half d+R.binary+d,1+R.inversions⟩,
        ⟨⟨fExt.trans (R.extension.trans step),basis,appendFamily_readsBack R.readsBack reads⟩,
          ?_,⟨?_,?_⟩,⟨?_,?_⟩,?_⟩⟩⟩
      · intro i
        simpa only [D,output,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
      · change 2*half d + R.binary + d ≤ 4*d
        have rhs := R.binaryBound
        have halfBound : 2*half d ≤ d := by unfold half; omega
        omega
      · change 1 + R.inversions ≤ r + 1
        have rhs := R.inversionsBound
        omega
      · change D.size = C.size + (2*half d + R.binary + d) + (1 + R.inversions)
        rw [show D.size = R.circuit.size + d from appendFamily_size _ _, R.size_eq,fSize]
        omega
      · change notCount D = notCount C + (1 + R.inversions)
        rw [show notCount D = notCount R.circuit from appendFamily_notCount_eq noNot,R.count_eq,fCount]
        omega
      · intro x i
        have pivotOn : value R.circuit (input x) pivotWire =
            !value C (input x) (taps (pivot positive)) :=
          (old_value R.extension (length x) pivotValid).trans (pivotValue x)
        have off : value R.circuit (input x) falseWire = false :=
          (old_value R.extension (length x) falseF).trans (offF x)
        have tailOn (j : Fin (half d)) : value R.circuit (input x) (R.wires j) =
            !(folded positive (fun k => value C (input x) (taps k)) j) := by
          rw [R.computes,foldValue]
        have bits := family_value (gate := gates) reads (input x) (length x) i
        change value D (input x) (output i) = _ at bits
        rw [bits,decoder_value positive _ _ _ _ _ off,pivotOn]
        exact decoded_correct positive (ordered x) tailOn i
    · have empty : d = 0 := by omega
      subst d
      exact empty_inversion input fan back taps

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private noncomputable def ceilingWire {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (complement : Fin d → ℕ) (u : Input n) : ℕ :=
  if below : rank P N d u < d then complement ⟨rank P N d u,below⟩ else n+1

private theorem ceilingWire_valid {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (C : Circuit) (complement : Fin d → ℕ) (u : Input n)
    (valid : ∀ i, complement i < nextWire (n+2) C) :
    ceilingWire P N complement u < nextWire (n+2) C := by
  unfold ceilingWire
  split
  · exact valid _
  · unfold nextWire
    omega

private theorem ceilingWire_value {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (C : Circuit) (complement : Fin d → ℕ)
    (sem : ∀ (i : Fin d) (x : Input n), value C (withConstants x) (complement i) = true ↔
      ¬ i.val+1 ≤ rank P N d x) (u x : Input n) :
    value C (withConstants x) (ceilingWire P N complement u) = true ↔
      ¬ rank P N d u+1 ≤ rank P N d x := by
  unfold ceilingWire
  split
  · exact sem _ x
  · rename_i notBelow
    have atTop : rank P N d u = d := by
      have cap := rank_bound P N d u
      omega
    have noHigher : ¬ rank P N d u+1 ≤ rank P N d x := by
      rw [atTop]
      have cap := rank_bound P N d x
      omega
    exact ⟨fun _ => noHigher,fun _ => true_value C x⟩

set_option maxHeartbeats 1400000 in

theorem append_taps {n m d : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (cone : Input n → ℕ) (complement : Fin d → ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (coneValid : ∀ u ∈ support P N, cone u < nextWire (n+2) C)
    (coneValue : ∀ u ∈ support P N, ∀ x : Input n, value C (withConstants x) (cone u) = true ↔ u ≤ x)
    (complementValid : ∀ i, complement i < nextWire (n+2) C)
    (complementValue : ∀ (i : Fin d) (x : Input n),
      value C (withConstants x) (complement i) = true ↔ ¬ i.val+1 ≤ rank P N d x)
    (bounded : ∀ x, ¬ Reach P N (d+1) x) :
    ∃ (D : Circuit) (tap : Fin m → Fin (n+2+D.size)),
      FanInTwo D ∧ ReadsBack (n+2) D ∧ D.output < n+2+D.size ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size ≤ C.size+(support P N).card+(positivePairs P).card ∧
      ∀ (x : Input n) (j : Fin m),
        (P x j → value D (withConstants x) (tap j).val = true) ∧
        (N x j → value D (withConstants x) (tap j).val = false) := by
  classical
  let words := (support P N).toList
  let gate (i : Fin words.length) : Gate := ⟨.and,[cone words[i],ceilingWire P N complement words[i]]⟩
  let guarded := appendFamily C gate
  let term (u : Input n) : ℕ := nextWire (n+2) C + words.idxOf u
  have gateReads (i : Fin words.length) (wire : ℕ) (used : wire ∈ (gate i).inputs) :
      wire < nextWire (n+2) C := by
    have present : words[i] ∈ support P N := Finset.mem_toList.mp (List.getElem_mem i.isLt)
    change wire ∈ [cone words[i],ceilingWire P N complement words[i]] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl | rfl
    · exact coneValid _ present
    · exact ceilingWire_valid P N C complement _ complementValid
  have guardedBasis : FanInTwo guarded := by
    apply appendFamily_fanInTwo basis
    intro i
    change GateOp.and ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (2 : ℕ) ≤ 2
    simp
  have guardedReads : ReadsBack (n+2) guarded := appendFamily_readsBack (gate := gate) reads gateReads
  have guardedCost : guarded.size = C.size+(support P N).card := by simp [guarded,words]
  have guardedNot : notCount guarded = notCount C := by
    apply appendFamily_notCount_eq
    intro i
    simp [gate]
  have termValid (u : Input n) (present : u ∈ support P N) : term u < nextWire (n+2) guarded := by
    have found : words.idxOf u < words.length := List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr present)
    change nextWire (n+2) C + words.idxOf u < nextWire (n+2) (appendFamily C gate)
    rw [appendFamily_nextWire]
    exact Nat.add_lt_add_left found _
  have termValue (u : Input n) (present : u ∈ support P N) (x : Input n) :
      value guarded (withConstants x) (term u) = true ↔ guardedCone P N d u x := by
    let i : Fin words.length := ⟨words.idxOf u,List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr present)⟩
    have point : words[i] = u := List.getElem_idxOf i.isLt
    have evaluated := appendFamily_new (C := C) (gate := gate) (x := withConstants x)
      (by simpa only [withConstants_length] using gateReads) i
    rw [withConstants_length] at evaluated
    have equation : value guarded (withConstants x) (term u) =
      (value C (withConstants x) (cone words[i]) &&
        value C (withConstants x) (ceilingWire P N complement words[i])) := by
      simpa [guarded,term,i,gate,GateOp.eval] using evaluated
    rw [point] at equation
    change value guarded (withConstants x) (term u) = true ↔
      u ≤ x ∧ ¬ rank P N d u+1 ≤ rank P N d x
    rw [equation,Bool.and_eq_true,coneValue u present x,
      ceilingWire_value P N C complement complementValue u x]
  let rows (j : Fin m) : List ℕ := (positiveInputs P j).toList.map term
  have validRows : ∀ (j : Fin m) a, a ∈ rows j → a < nextWire (n+2) guarded := by
    intro j a member
    obtain ⟨u,present,rfl⟩ := List.mem_map.mp member
    exact termValid u (positive_input_support P N (Finset.mem_toList.mp present))
  obtain ⟨D,out,finalBasis,finalReads,finalPrefix,finalNot,finalSize,outValid,outValue⟩ :=
    append_or_rows guarded rows guardedBasis guardedReads validRows
  have rowCost : (∑ j : Fin m, (rows j).length) = (positivePairs P).card := by
    simpa [rows] using positive_incidence_count P
  have realized (x : Input n) (j : Fin m) :
      value D (withConstants x) (out j) = true ↔ tapAccepts P N d x j := by
    rw [outValue]
    constructor
    · rintro ⟨a,member,active⟩
      obtain ⟨u,present,rfl⟩ := List.mem_map.mp member
      have positive := Finset.mem_toList.mp present
      exact ⟨u,positive,(termValue u (positive_input_support P N positive) x).mp active⟩
    · rintro ⟨u,positive,active⟩
      exact ⟨term u,List.mem_map.mpr ⟨u,Finset.mem_toList.mpr positive,rfl⟩,
        (termValue u (positive_input_support P N positive) x).mpr active⟩
  let taps (j : Fin m) : Fin (n+2+(withOutput D 0).size) := ⟨out j,outValid j⟩
  refine ⟨withOutput D 0,taps,finalBasis,finalReads,?_,
    (appendFamily_prefix C gate).trans finalPrefix,finalNot.trans guardedNot,?_,?_⟩
  · simp only [withOutput_output,withOutput_size]
    omega
  · rw [withOutput_size,finalSize,guardedCost,rowCost]
  · intro x j
    change (P x j → value D (withConstants x) (out j) = true) ∧
      (N x j → value D (withConstants x) (out j) = false)
    refine ⟨fun positive => (realized x j).mpr (tap_accepts_positive P N d positive),?_⟩
    intro negative
    exact Bool.eq_false_iff.mpr fun active =>
      tap_rejects_negative P N bounded negative ((realized x j).mp active)

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def Fits {n m : ℕ} (P N : Input n → Fin m → Prop) (r : ℕ) (cost : ℕ → Prop) : Prop :=
  ∃ (C : Circuit) (tap : Fin m → Fin (n+2+C.size)),
    FanInTwo C ∧ ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧ notCount C ≤ r ∧
    cost (C.size-notCount C) ∧ ∀ (x : Input n) (j : Fin m),
      (P x j → value C (withConstants x) (tap j).val = true) ∧
      (N x j → value C (withConstants x) (tap j).val = false)

theorem upper_fits {n m r d : ℕ} (P N : Input n → Fin m → Prop)
    (bound : d < 2^r) (bounded : ∀ x, ¬ Reach P N (d+1) x) :
    Fits P N r (fun b => b ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d) := by
  obtain ⟨A,cone,aBasis,aReads,aSize,aNot,aSem,_⟩ := supportConeTable_empty P N
  obtain ⟨B,thresholds,bBasis,bReads,bExtends,bNot,bSize,bLive,bSem⟩ :=
    append_thresholds P N d A cone aBasis aReads
      (fun u hu => (aSem u hu).1) (fun u hu => (aSem u hu).2)
  have falseLive : n < nextWire (n+2) B := by unfold nextWire; omega
  obtain ⟨I⟩ := invert_taps (withConstants (n := n)) withConstants_length bound
    bBasis bReads n falseLive (false_value B) thresholds bLive (threshold_antitone bSem)
  have extension : A.gates <+: I.circuit.gates := bExtends.trans I.extension
  have coneLive (u : Input n) (hu : u ∈ support P N) :
      cone u < nextWire (n+2) I.circuit :=
    (aSem u hu).1.trans_le (nextWire_le_of_prefix extension)
  have coneValue (u : Input n) (hu : u ∈ support P N) (x : Input n) :
      value I.circuit (withConstants x) (cone u) = true ↔ u ≤ x := by
    have live : cone u < nextWire (withConstants x).length A := by
      rw [withConstants_length]
      exact (aSem u hu).1
    rw [value_of_prefix extension live]
    exact (aSem u hu).2 x
  have complementValue (i : Fin d) (x : Input n) :
      value I.circuit (withConstants x) (I.wires i) = true ↔ ¬ i.val+1 ≤ rank P N d x := by
    rw [I.computes, ← bSem x i]
    cases value B (withConstants x) (thresholds i) <;> decide
  obtain ⟨C,tap,cBasis,cReads,cOut,_,cNot,cSize,labels⟩ :=
    append_taps P N I.circuit cone I.wires I.fanInTwo I.readsBack
      coneLive coneValue I.valid complementValue bounded
  have bZero : notCount B = 0 := bNot.trans aNot
  have cInversions : notCount C = I.inversions := by
    rw [cNot,I.count_eq,bZero,Nat.zero_add]
  have cBinary : C.size-notCount C ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d := by
    have inversionSize := I.size_eq
    have binaryBudget := I.binaryBound
    rw [cInversions,Nat.add_mul]
    omega
  exact ⟨C,tap,cBasis,cReads,cOut,cInversions.le.trans I.inversionsBound,cBinary,labels⟩

theorem solve_fall_1228 (n m r : ℕ) (P N : Input n → Fin m → Prop) :
    (Fits P N r (fun _ => True) ↔ ∀ x, ¬ Reach P N (2^r) x) ∧
    ∀ d : ℕ, d < 2^r → (∀ x, ¬ Reach P N (d+1) x) →
      Fits P N r (fun b => b ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d) := by
  constructor
  · constructor
    · rintro ⟨C,tap,basis,_,_,budget,_,labels⟩
      exact no_packing_of_taps (fun j => (tap j).val) basis budget labels
    · intro bounded
      have positive : 0 < (2:ℕ)^r := Nat.pow_pos (by decide)
      have below : (2:ℕ)^r-1 < 2^r := by omega
      have successor : (2:ℕ)^r-1+1 = 2^r := by omega
      have bounded' : ∀ x, ¬ Reach P N ((2:ℕ)^r-1+1) x := by simpa only [successor] using bounded
      obtain ⟨C,tap,basis,reads,output,budget,_,labels⟩ := upper_fits P N below bounded'
      exact ⟨C,tap,basis,reads,output,budget,True.intro,labels⟩
  · intro d bound bounded
    exact upper_fits P N bound bounded

end PEqualNP.Outside.L_lib_1435_aux.Packing

namespace PEqualNP.Outside.L_lib_1435_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_lib_1435_aux.Wire PEqualNP.Outside.L_lib_1435_aux.Drivers
open PEqualNP.NotBracket (notCount)
theorem rewire (s r : ℕ) (f : ℕ → ℕ) (bounds : ∀ k,k<r+2 → f k<s+2) (C : Circuit) (hv : Valid r C) :
    ∃ S : Circuit, Valid s S ∧ notCount S=notCount C ∧ S.size=C.size ∧
       ∀ x y : List Bool,x.length=s+2 → y.length=r+2 → (∀k,k<r+2 → x.getD (f k) false=y.getD k false) →
       S.eval x=C.eval y := by
  obtain ⟨fan,back,hout⟩ := hv
  let ρ (i : ℕ) := if i<r+2 then f i else s+2+(i-(r+2))
  let S : Circuit := ⟨C.gates.map (remap ρ),ρ C.output⟩
  have sz : S.size=C.size := by simp [S,Circuit.size]
  have hg (j) : gateAt S j=remap ρ (gateAt C j) := gateAt_map _ _ _ j
  have hρ (k j : ℕ) (h : k<r+2+j) : ρ k<s+2+j := by
    dsimp [ρ]; split <;> rename_i test
    · have := bounds k test; omega
    · omega
  have hS : ReadsBack (s+2) S := by
    intro j hj i hi
    rw [hg] at hi
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
    exact hρ _ _ (back j (by simpa [S] using hj) k hk)
  refine ⟨S,⟨?_,hS,?_⟩,notCount_map _ _ _ _,sz,?_⟩
  · intro g mem
    obtain ⟨g0,inC,rfl⟩ := List.mem_map.mp mem
    simpa [remap] using fan g0 inC
  · change ρ C.output<s+2+S.size
    rw [sz]
    exact hρ _ _ hout
  · intro x y lx ly seed
    have key (k) : k<r+2+C.size → (S.wires x).getD (ρ k) false=(C.wires y).getD k false := by
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        by_cases var : k<r+2
        · change (run S.gates x).getD _ _=(run C.gates y).getD _ _
          rw [getD_run _ _ _ (by rw [lx]; exact hρ k 0 var),getD_run _ _ _ (by omega)]
          simpa [ρ,var] using seed k var
        · obtain ⟨j,rfl⟩ : ∃j,k=r+2+j := ⟨k-(r+2),by omega⟩
          have eq : ρ (r+2+j)=s+2+j := by dsimp [ρ]; split_ifs <;> omega
          have lj : j<C.gates.length := by change j<C.size; omega
          rw [eq,wire_gate S _ hS x lx j (by rw [sz]; exact lj),wire_gate C _ back y ly j lj,hg]
          simp only [remap,List.map_map]
          congr 1
          apply List.map_congr_left
          intro i m
          have hi := back j lj i m
          exact ih i (by omega) (by omega)
    exact key _ hout
end PEqualNP.Outside.L_lib_1435_aux

namespace PEqualNP.Outside.L_lib_1435_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_1435_aux.Wire PEqualNP.Outside.L_lib_1435_aux.Prefix
open PEqualNP.NotBracket (notCount)
def slice (n off : ℕ) (Y : Finset ℕ) := (Finset.range n).filter (fun k => off+k∈Y)
theorem shift (n off : ℕ) (C : Circuit) (v : Valid n C) :
    ∃D : Circuit,Valid (off+n) D ∧ notCount D=notCount C ∧ D.size=C.size ∧
      ∀Y,D.eval (input (off+n) Y)=C.eval (input n (slice n off Y)) := by
  obtain ⟨D,ok,ng,sz,sem⟩ := rewire (off+n) n (fun k => off+k) (by intros; omega) C v
  refine ⟨D,ok,ng,sz,fun Y => sem _ _ (by simp [input]) (by simp [input]) ?_⟩
  intro k hk
  by_cases var : k<n
  · rw [inputAt _ _ _ (by omega),inputAt _ _ _ var]
    simp [slice,var]
  · rcases (by omega : k=n ∨ k=n+1) with rfl|rfl
    · rw [inputFalse,inputFalse]
    · rw [←Nat.add_assoc,inputTrue,inputTrue]

theorem fixedPins (s r : ℕ) (sr : s ≤ r) (A : Finset ℕ) (far : ∀x∈A,s ≤ x) (C : Circuit) (v : Valid r C) :
    ∃D : Circuit,Valid s D ∧ notCount D=notCount C ∧ D.size=C.size ∧
      ∀X,X ⊆ Finset.range s → D.eval (input s X)=C.eval (input r (X∪A)) := by
  let f (k : ℕ) := if k<s then k else if k<r then if k∈A then s+1 else s else s+(k-r)
  obtain ⟨D,ok,ng,sz,sem⟩ := rewire s r f (by intro k hk; dsimp [f]; split_ifs <;> omega) C v
  refine ⟨D,ok,ng,sz,fun X xs => sem _ _ (by simp [input]) (by simp [input]) ?_⟩
  intro k hk
  by_cases small : k<s
  · have miss : k∉A := fun h => small.not_ge (far k h)
    simp only [f,small,ite_true,inputAt _ _ _ small,inputAt _ _ _ (show k<r by omega),Finset.mem_union,miss,or_false]
  · have miss : k∉X := fun h => small (Finset.mem_range.mp (xs h))
    by_cases var : k<r
    · dsimp only [f]
      rw [if_neg small,if_pos var,inputAt _ _ _ var]
      by_cases high : k∈A
      · rw [if_pos high,inputTrue]; simp [high]
      · rw [if_neg high,inputFalse]; simp [high,miss]
    · rcases (by omega : k=r ∨ k=r+1) with rfl|rfl
      · simp only [f,small,var,ite_false,Nat.sub_self,Nat.add_zero,inputFalse]
      · simp only [f,small,var,ite_false,Nat.add_sub_cancel_left,inputTrue]

theorem tagDecoder (h off : ℕ) (N : ℕ) (eq : N=2^h) (f : Fin N → Bool) :
    ∃D : Circuit,Valid (off+N) D ∧ notCount D ≤ h ∧ D.size-notCount D ≤ 6*N ∧
      ∀Y,∀i : Fin N,PEqualNP.Outside.L_lib_1435_aux.Tree.cell h (i.cast eq) (slice N off Y) →
        D.eval (input (off+N) Y)=f i := by
  subst N
  obtain ⟨C,vc,nc,sc,ev⟩ := PEqualNP.Outside.L_lib_1435_aux.Tree.part4 h f
  obtain ⟨D,vd,nd,sd,sim⟩ := shift _ off C vc
  refine ⟨D,vd,nd.le.trans nc,by simpa [nd,sd] using sc,?_⟩
  intro Y i cell
  rw [sim]
  exact ev _ (Finset.filter_subset ..) i cell
end PEqualNP.Outside.L_lib_1435_aux

namespace PEqualNP.Outside.L_lib_1435_aux
open PEqualNP.Outside.L_lib_1435_aux.Cells
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_1435_aux.Wire
abbrev M (a : ℕ) := 4*2^a
abbrev off (a d e : ℕ) := d+4*e+2*M a
abbrev n (a d e : ℕ) := off a d e+M a
abbrev Pins (a : ℕ) := Fin (M a) → Fin 3 → Bool → Finset ℕ
def Cell (r : ℕ) (p : Pins a) (s : Fin (M a)) (j : Fin 3) (Y : Finset ℕ) :=
  Y ⊆ Finset.range r ∧ p s j true ⊆ Y ∧ Disjoint (p s j false) Y
def Fit (r b cost : ℕ) (p : Pins a) :=
  ∃D : Circuit,Valid r D ∧ PEqualNP.NotBracket.notCount D ≤ b ∧ D.size-PEqualNP.NotBracket.notCount D ≤ cost ∧
    ∀s j Y,Cell r p s j Y → D.eval (input r Y)=decide (s.val % 2=0)
theorem width (a : ℕ) : M a=2^(a+2) := by unfold M; ring
theorem tagged (L : Fin (M a) → Fin 3 → Fin e × Bool) (p : Pins a)
    (hp : ∀s j v x,x∈p s j v ↔ PM a d e L s j v x)
    (i j Y) (c : Cell (n a d e) p i j Y) :
    PEqualNP.Outside.L_lib_1435_aux.Tree.cell (a+2) (i.cast (width a)) (slice (M a) (off a d e) Y) := by
  have pin {v : Bool} {q} (hq : q∈PEqualNP.Outside.L_lib_1435_aux.Tree.path (a+2) i.val v) :
      q<M a ∧ off a d e+q∈p i j v := by
    obtain ⟨u,mem,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ran,bit⟩ := Finset.mem_filter.mp mem
    have small := Finset.mem_range.mp ran
    exact ⟨piv_lt a i.val u i.isLt small,(hp ..).mpr (Or.inr (Or.inr (Or.inr ⟨u,small,(dec_iff _ _).mp bit,rfl⟩)))⟩
  constructor
  · intro q h
    have ⟨lt,yes⟩ := pin h
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr lt,c.2.1 yes⟩
  · apply Finset.disjoint_left.mpr
    intro q h neg
    exact Finset.disjoint_left.mp c.2.2 (pin h).2 (Finset.mem_filter.mp neg).2
theorem cellOrdered (L : Fin (M a) → Fin 3 → Fin e × Bool) (p : Pins a)
    (hp : ∀s j v x,x∈p s j v ↔ PM a d e L s j v x)
    {i k j t X Y} (xy : X ⊆ Y) (cx : Cell (n a d e) p i j X) (cy : Cell (n a d e) p k t Y) : i ≤ k := by
  apply PEqualNP.Outside.L_lib_1435_aux.Tree.part3 (a+2) _ _ (i.cast (width a)) (k.cast (width a)) _ (tagged L p hp _ _ _ cx) (tagged L p hp _ _ _ cy)
  intro z hz
  obtain ⟨few,yes⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨few,xy yes⟩
theorem slack (L : Fin (M a) → Fin 3 → Fin e × Bool) (p : Pins a)
    (hp : ∀s j v x,x∈p s j v ↔ PM a d e L s j v x) : Fit (n a d e) (a+2) (6*M a) p := by
  obtain ⟨D,v,n,c,ok⟩ := tagDecoder (a+2) (off a d e) (M a) (width a) (fun i => decide (i.val % 2=0))
  exact ⟨D,v,n,c,fun i j Y h => ok Y i (tagged L p hp _ _ _ h)⟩
end PEqualNP.Outside.L_lib_1435_aux

namespace PEqualNP.Outside.L_lib_1435_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_1435_aux.Wire
open PEqualNP.Outside.L_lib_1435_aux.Cells
open PEqualNP.Outside.L_lib_1435_aux.Packing (Reach solve_fall_1228)
def obs (x : Fin r → Bool) := ((Finset.univ.filter (fun i : Fin r => x i=true)).map Fin.valEmbedding)
def word (r : ℕ) (X : Finset ℕ) := fun i : Fin r => decide (i.val∈X)
theorem obsWord (X : Finset ℕ) (h : X ⊆ Finset.range r) : obs (word r X)=X := by
  ext k
  simp only [obs,word,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq,Fin.valEmbedding_apply]
  constructor
  · rintro ⟨v,yes,rfl⟩; exact yes
  · intro yes; exact ⟨⟨k,Finset.mem_range.mp (h yes)⟩,yes,rfl⟩
theorem obsMono {x y : Fin r → Bool} (h : x ≤ y) : obs x ⊆ obs y := by
  apply Finset.map_subset_map.mpr
  intro i mem
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Bool.le_iff_imp.mp (h i) (Finset.mem_filter.mp mem).2⟩

abbrev Row (a : ℕ) := Fin (M a) × Fin 3 × Finset ℕ
def Good (p : Pins a) (r : ℕ) (u : Row a) := Cell r p u.1 u.2.1 u.2.2
def Mark (p : Pins a) (r : ℕ) (v : ℕ) (x : Fin r → Bool) (_ : Fin 1) :=
    ∃ i j, i.val % 2=v ∧ Cell r p i j (obs x)
def TraceRows (r : ℕ) (p : Pins a) (k : ℕ) (top : Finset ℕ) :=
  ∃z : ℕ → Row a, (∀i,i<2*k → Good p r (z i) ∧ (z i).1.val % 2=i%2 ∧ (z i).2.2 ⊆ top) ∧
    ∀i j,i ≤ j → j<2*k → (z i).2.2 ⊆ (z j).2.2

theorem extendRows (p : Pins a) (lo hi : Row a) (top mid : Finset ℕ) (k : ℕ)
    (old : TraceRows r p k mid) (goodLo : Good p r lo) (goodHi : Good p r hi)
    (elo : lo.1.val % 2=0) (ehi : hi.1.val % 2=1)
    (before : mid ⊆ lo.2.2) (up : lo.2.2 ⊆ hi.2.2) (endBound : hi.2.2 ⊆ top) :
    TraceRows r p (k+1) top := by
  obtain ⟨z,desc,ord⟩ := old
  let w (i : ℕ) := if i<2*k then z i else if i=2*k then lo else hi
  refine ⟨w,?_,?_⟩
  · intro i bound
    by_cases base : i<2*k
    · simpa [w,base] using And.intro (desc i base).1
        (And.intro (desc i base).2.1 ((desc i base).2.2.trans (before.trans (up.trans endBound))))
    · by_cases eq : i=2*k
      · subst i
        simpa [w,elo] using And.intro goodLo (up.trans endBound)
      · have mod : i%2=1 := by omega
        simpa [w,base,eq,ehi,mod] using And.intro goodHi endBound
  · intro i j ij bound
    by_cases hj : j<2*k
    · have h := ord i j ij hj
      simpa [w,hj,show i<2*k by omega] using h
    · by_cases h : i<2*k
      · have hit := (desc i h).2.2.trans before
        by_cases eq : j=2*k <;> simp [w,h,hj,eq,hit,hit.trans up]
      · dsimp only [w]
        rw [if_neg h,if_neg hj]
        split_ifs <;> first | exact fun _ h => h | exact up | omega

theorem packing (p : Pins a) (r k : ℕ) (x : Fin r → Bool) (h : Reach (Mark p r 0) (Mark p r 1) k x) :
    TraceRows r p k (obs x) := by
  induction k generalizing x with
  | zero =>
    refine ⟨fun _ => (⟨0,by unfold M; positivity⟩,0,∅),by simp,by simp⟩
  | succ k ih =>
    obtain ⟨u,v,j,prev,uv,vx,⟨i₁,j₁,e₁,yes⟩,⟨i₂,j₂,e₂,no⟩⟩ := h
    exact extendRows p (i₁,j₁,obs u) (i₂,j₂,obs v) _ (obs u) k (ih u prev)
      yes no e₁ e₂ (fun _ h => h) (obsMono uv) (obsMono vx)

theorem strictAdjacent {n m : ℕ} {f : Fin n → Fin m} (h : ∀i j : Fin n,i.val+1=j.val → f i<f j) : StrictMono f := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ t => exact Fin.strictMono_iff_lt_succ.mpr (fun i => h i.castSucc i.succ rfl)

theorem fullStages (L : Fin (M a) → Fin 3 → Fin e × Bool) (p : Pins a)
    (hp : ∀s j v x,x∈p s j v ↔ PM a d e L s j v x) (top)
    (t : TraceRows (n a d e) p (2^(a+1)) top) :
    ∃ (Y : Fin (M a) → Finset ℕ) (v : Fin (M a) → Fin 3),Monotone Y ∧ ∀s,Cell (n a d e) p s (v s) (Y s) := by
  obtain ⟨z,desc,ord⟩ := t
  have size : 2*2^(a+1)=M a := by unfold M; ring
  rw [size] at desc ord
  let f (i : Fin (M a)) := (z i.val).1
  have sm : StrictMono f := by
    apply strictAdjacent
    intro i j ij
    have x := desc i.val i.isLt
    have y := desc j.val j.isLt
    apply lt_of_le_of_ne (cellOrdered L p hp (ord _ _ (by omega : i.val ≤ j.val) j.isLt) x.1 y.1)
    intro eq
    have h := congrArg Fin.val eq
    change (z i.val).1.val=(z j.val).1.val at h
    have xmod := x.2.1
    have ymod := y.2.1
    omega
  have idf : f=id := by
    funext i
    apply le_antisymm _ (sm.id_le i)
    simpa using ((Fin.rev_strictAnti.comp_strictMono sm).comp Fin.rev_strictAnti).id_le (Fin.rev i)
  refine ⟨fun i => (z i.val).2.2,fun i => (z i.val).2.1,fun _ j h => ord _ _ h j.isLt,?_⟩
  intro i
  have eq : (z i.val).1=i := congrFun idf i
  have c := (desc i.val i.isLt).1
  unfold Good at c
  rw [eq] at c
  exact c
end PEqualNP.Outside.L_lib_1435_aux

namespace PEqualNP.Outside.L_lib_1435_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_lib_1435_aux.Wire PEqualNP.Outside.L_lib_1435_aux.Cells
open PEqualNP.Outside.L_lib_1435_aux.Packing (Reach solve_fall_1228 value withConstants)
theorem enough (L : Fin (M a) → Fin 3 → Fin e × Bool) (p : Pins a)
    (hp : ∀s j v x,x∈p s j v ↔ PM a d e L s j v x)
    (absent : ¬ ∃ (Y : Fin (M a) → Finset ℕ) (v : Fin (M a) → Fin 3),Monotone Y ∧ ∀s,Cell (n a d e) p s (v s) (Y s)) :
    ∃cost,Fit (n a d e) (a+1) cost p := by
  let r := n a d e
  obtain ⟨C,tap,fan,back,_,neg,_,outputs⟩ :=
    (solve_fall_1228 r 1 (a+1) (Mark p r 0) (Mark p r 1)).1.mpr (by
      intro x reach
      exact absent (fullStages L p hp _ (packing p r _ x reach)))
  let D : Circuit := ⟨C.gates,(tap 0).val⟩
  refine ⟨_,D,⟨fan,back,(tap 0).isLt⟩,neg,le_rfl,?_⟩
  intro s j Y c
  have eq := obsWord Y c.1
  have rep := outputs (word r Y) 0
  change value C (withConstants (word r Y)) (tap 0).val=_
  by_cases even : s.val % 2=0
  · simpa only [even,decide_true] using rep.1 ⟨s,j,even,by rw [eq]; exact c⟩
  · have odd : s.val % 2=1 := by omega
    simpa only [even,decide_false] using rep.2 ⟨s,j,odd,by rw [eq]; exact c⟩
end PEqualNP.Outside.L_lib_1435_aux

open PEqualNP.Outside.L_lib_1435_aux.Drivers PEqualNP.Outside.L_lib_1435_aux.Prefix
namespace PEqualNP.Outside.L_lib_1435_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.NotBracket (notCount)
open PEqualNP.Outside.L_lib_1435_aux.Wire
def rank (D : Circuit) (x : List Bool) := driverNumber (code D.gates x)
theorem rankBound (D : Circuit) (x) : rank D x < 2^notCount D := by
  simpa only [rank,code_len,mark_count] using driver_bound (code D.gates x)
theorem rankMono (v : FanInTwo D) (o : ordered x y) : rank D x ≤ rank D y :=
  driver_mono _ (fun g h => (v g h).1) o
theorem firstHigh (D : Circuit) (x) (budget : notCount D ≤ a+1) (high : 2^a ≤ rank D x) :
    (code D.gates x).getD 0 false=false := by
  have len : (code D.gates x).length ≤ a+1 := by rw [code_len,mark_count]; exact budget
  unfold rank at high
  cases h : code D.gates x with
  | nil => simp [h,driverNumber] at high
  | cons b tail =>
    have small : tail.length ≤ a := by simpa [h] using len
    have cap := (driver_bound tail).trans_le (Nat.pow_le_pow_right (by decide) small)
    rw [h] at high
    cases b <;> simp_all [driverNumber] <;> omega
theorem firstLow (D : Circuit) (x) (budget : notCount D ≤ a+1) (low : rank D x+2^a < 2^notCount D) :
    (code D.gates x).getD 0 false=true := by
  have full : notCount D=a+1 := by
    by_contra denied
    have cap : 2^notCount D ≤ 2^a := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [full,pow_succ] at low
  exact dn_top _ a (by change rank D x < 2^a; omega) 0 (by rw [code_len,mark_count,full]; omega)
theorem halfRank {a : ℕ} {p : Pins a} {D : Circuit} (v : FanInTwo D) {H start r : ℕ} (hpos : 0<H) (ev : ∀i j Y,Cell r p i j Y → D.eval (input r Y)=decide (i.val % 2=0))
    (startEven : start % 2=0) (endBound : start+2*H ≤ M a) (Y : Fin (M a) → Finset ℕ) (J : Fin (M a) → Fin 3)
    (ym : Monotone Y) (inCell : ∀i,start ≤ i.val → i.val<start+2*H → Cell r p i (J i) (Y i)) :
    rank D (input r (Y ⟨start,by omega⟩))+H ≤ rank D (input r (Y ⟨start+2*H-1,by omega⟩)) := by
  let I (k : ℕ) : Fin (M a) := ⟨min (start+k) (M a-1),by omega⟩
  let z (k : ℕ) := input r (Y (I k))
  have val (k) (hk : k<2*H) : (I k).val=start+k := Nat.min_eq_left (by omega)
  have ord (i j) (ij : i ≤ j) : ordered (z i) (z j) :=
    orderedInput r (ym (show I i ≤ I j from min_le_min_right _ (Nat.add_le_add_left ij start)))
  have output (k) (hk : k<2*H) : D.eval (z k)=decide ((start+k)%2=0) := by
    have c := inCell (I k) (by rw [val k hk]; omega) (by rw [val k hk]; omega)
    simpa only [z,val k hk] using ev _ _ _ c
  have step (i) (hi : i<H) : rank D (z (2*i))+1 ≤ rank D (z (2*i+1)) := by
    apply dn_step _ (fun g h => (v g h).1) (ord _ _ (by omega)) D.output
    · change D.eval _=true
      rw [output _ (by omega),decide_eq_true (by omega)]
    · change D.eval _=false
      rw [output _ (by omega),decide_eq_false (by omega)]
  have asc (i) (hi : i<H) : rank D (z 0)+(i+1) ≤ rank D (z (2*i+1)) := by
    induction i with
    | zero => exact step 0 hi
    | succ i ih =>
      have b := ih (by omega)
      have nxt := rankMono v (ord (2*i+1) (2*(i+1)) (by omega))
      have c := step (i+1) hi
      omega
  have endRank := asc (H-1) (by omega)
  have eq₀ : I 0=⟨start,by omega⟩ := Fin.ext (by rw [val 0 (by omega)]; simp)
  have eq₁ : I (2*(H-1)+1)=⟨start+2*H-1,by omega⟩ := Fin.ext (by rw [val _ (by omega)]; dsimp; omega)
  simpa only [z,eq₀,eq₁,show H-1+1=H by omega] using endRank
end PEqualNP.Outside.L_lib_1435_aux

namespace PEqualNP.Outside.L_lib_1435_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_lib_1435_aux.Wire PEqualNP.Outside.L_lib_1435_aux.Prefix PEqualNP.Outside.L_lib_1435_aux.Cells
def ones (a d e : ℕ) := Finset.Ico d (d+2*e) ∪ Finset.Ico (d+4*e) (d+4*e+4*2^a) ∪
  (Finset.Icc 1 (2*2^a-1)).image (fun j => off a d e+j)
def cut (a d e : ℕ) (X : Finset ℕ) := X∪ones a d e
theorem cutDesc (a d e : ℕ) (X : Finset ℕ) (x) : x∈cut a d e X ↔ CM a d e X x := by
  simp only [cut,ones,CM,off,M,Finset.mem_union,Finset.mem_image,Finset.mem_Ico,Finset.mem_Icc,or_assoc]
  refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr Iff.rfl ?_))
  constructor
  · rintro ⟨j,⟨l,h⟩,rfl⟩; exact ⟨j,l,h,rfl⟩
  · rintro ⟨j,l,h,rfl⟩; exact ⟨j,⟨l,h⟩,rfl⟩
theorem farOnes (a d e : ℕ) (x) (h : x∈ones a d e) : d ≤ x := by
  have hk : CM a d e ∅ x := (cutDesc a d e ∅ x).mp (Finset.mem_union_right _ h)
  rcases hk with zero|⟨l,_⟩|⟨l,_⟩|⟨q,_,_,rfl⟩ <;> first | simp at zero | omega
def Yes (d : ℕ) (L : Fin (M a) → Fin 3 → Fin e × Bool) (X : Finset ℕ) :=
  ∃w : Fin e → Bool,(∀s : Fin (M a),s.val<2*2^a → ∃j,w (L s j).1=(L s j).2) ∧
    ∀i : Fin e,i.val<d → w i=true → i.val∈X
def No (d : ℕ) (L : Fin (M a) → Fin 3 → Fin e × Bool) (X : Finset ℕ) :=
  ∃w : Fin e → Bool,(∀s : Fin (M a),¬s.val<2*2^a → ∃j,w (L s j).1=(L s j).2) ∧
    ∀i : Fin e,i.val<d → w i=true → i.val∉X

theorem sides (L : Fin (M a) → Fin 3 → Fin e × Bool) (p : Pins a)
    (hp : ∀s j v x,x∈p s j v ↔ PM a d e L s j v x) (D : Circuit) (fan : FanInTwo D)
    (ev : ∀i j Y,Cell (n a d e) p i j Y → D.eval (input (n a d e) Y)=decide (i.val % 2=0))
    (X : Finset ℕ) (xs : X ⊆ Finset.range d) :
    let raw := input (n a d e) (cut a d e X)
    (Yes d L X → 2^a ≤ rank D raw) ∧ (No d L X → rank D raw+2^a < 2^PEqualNP.NotBracket.notCount D) := by
  intro raw
  let H := 2^a
  have hpos : 0<H := Nat.two_pow_pos _
  have size : M a=4*H := rfl
  constructor
  · rintro ⟨w,sat,pos⟩
    obtain ⟨Y,J,ym,ok⟩ := pos_chainT hp (cutDesc a d e) X xs w sat pos
    have last : 0+2*H-1<M a := by omega
    have ascent := halfRank (p:=p) fan (H:=H) (start:=0) hpos ev (by decide) (by omega) Y J ym
      (fun i _ hi => (ok i (by omega)).1)
    have upper := (ok ⟨0+2*H-1,last⟩ (by dsimp; omega)).2
    have rankEnd := rankMono fan (orderedInput (n a d e) upper)
    change rank D (input _ (Y _)) ≤ rank D raw at rankEnd
    omega
  · rintro ⟨w,sat,neg⟩
    obtain ⟨Y,J,ym,ok⟩ := neg_chainF hp (cutDesc a d e) X xs w sat neg
    have first : 2*H<M a := by omega
    have ascent := halfRank (p:=p) fan (H:=H) (start:=2*H) hpos ev (by omega) (by omega) Y J ym
      (fun i lo _ => (ok i (by omega)).1)
    have lower := (ok ⟨2*H,first⟩ (by simp [H])).2
    have rankStart := rankMono fan (orderedInput (n a d e) lower)
    change rank D raw ≤ rank D (input _ (Y _)) at rankStart
    exact (Nat.add_le_add_right rankStart H).trans_lt (ascent.trans_lt (rankBound _ _))
end PEqualNP.Outside.L_lib_1435_aux

namespace PEqualNP.Outside.L_lib_1435_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_lib_1435_aux.Wire PEqualNP.Outside.L_lib_1435_aux.Prefix PEqualNP.Outside.L_lib_1435_aux.Cells
open PEqualNP.NotBracket (notCount)
def Sep (d cost : ℕ) (P N : Finset ℕ → Prop) :=
  ∃S : Circuit,Valid d S ∧ notCount S=0 ∧ S.size ≤ cost ∧ ∀X ⊆ Finset.range d,
    (P X → S.eval (input d X)=true) ∧ (N X → S.eval (input d X)=false)
theorem separate (L : Fin (M a) → Fin 3 → Fin e × Bool) (p : Pins a)
    (hp : ∀s j v x,x∈p s j v ↔ PM a d e L s j v x) :
    Fit (n a d e) (a+1) cost p → Sep d cost (Yes d L) (No d L) := by
  rintro ⟨D,vd,ng,c,ev⟩
  let r := n a d e
  obtain ⟨C,vc,nc,sc,run⟩ := readFirst r D vd
  obtain ⟨S,vs,ns,ss,ok⟩ := fixedPins d r (by dsimp [r,n,off]; omega) (ones a d e) (farOnes a d e) C vc
  refine ⟨S,vs,ns.trans nc,ss.le.trans (sc.trans c),?_⟩
  intro X xs
  have span := sides L p hp D vd.1 ev X xs
  rw [ok _ xs,run]
  constructor
  · intro yes
    have b := firstHigh D _ ng (span.1 yes)
    dsimp only [cut] at b
    change (!((PEqualNP.Outside.L_lib_1435_aux.Drivers.code D.gates (input (n a d e) (X∪ones a d e))).getD 0 false)) = _
    rw [b]; rfl
  · intro no
    have b := firstLow D _ ng (span.2 no)
    dsimp only [cut] at b
    change (!((PEqualNP.Outside.L_lib_1435_aux.Drivers.code D.gates (input (n a d e) (X∪ones a d e))).getD 0 false)) = _
    rw [b]; rfl
theorem solve (L : Fin (M a) → Fin 3 → Fin e × Bool) (p : Pins a)
    (hp : ∀s j v x,x∈p s j v ↔ PM a d e L s j v x) :
    ((∃cost,Fit (n a d e) (a+1) cost p) ↔ ∀X ⊆ Finset.range d,Yes d L X → ¬No d L X) ∧
    (∀cost,Fit (n a d e) (a+1) cost p → Sep d cost (Yes d L) (No d L)) ∧
    ((∃X ⊆ Finset.range d, Yes d L X ∨ No d L X) → ∀cost, ¬Fit (n a d e) a cost p) ∧
    Fit (n a d e) (a+2) (6*M a) p := by
  refine ⟨⟨?_,?_⟩,fun _ => separate L p hp,?_,slack L p hp⟩
  · rintro ⟨c,fit⟩ X xs y n'
    obtain ⟨S,_,_,_,test⟩ := separate L p hp fit
    exact Bool.noConfusion (((test X xs).1 y).symm.trans ((test X xs).2 n'))
  · intro disjoint
    apply enough L p hp
    intro seq
    obtain ⟨X,xs,yes,no⟩ := (conj4 hp (cutDesc a d e)).mp seq
    exact disjoint X xs yes no
  · rintro ⟨X,xs,caseX⟩ c ⟨D,vd,ng,sz,ev⟩
    have span := sides L p hp D vd.1 ev X xs
    have cap : 2^notCount D ≤ 2^a := Nat.pow_le_pow_right (by decide) ng
    rcases caseX with yes|no
    · exact (span.1 yes).not_gt ((rankBound _ _).trans_le cap)
    · have contra := span.2 no
      omega
end PEqualNP.Outside.L_lib_1435_aux

namespace PEqualNP.Outside.L_lib_1435_aux
open PEqualNP.Outside.L_lib_1435_aux.Wire
theorem truthYes (Q : Prop) : truth Q=true ↔ Q := by simp [truth]
theorem truthNo (Q : Prop) : truth Q=false ↔ ¬Q := by simp [truth]
end PEqualNP.Outside.L_lib_1435_aux
open PEqualNP.Outside.L_lib_1435_aux PEqualNP.Outside.L_lib_1435_aux.Cells PEqualNP.Outside.L_lib_1435_aux.Wire in
theorem PEqualNP.Outside.L_lib_1435 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let bits := fun (r : Nat) (Y : Finset Nat) => List.ofFn (fun j : Fin r => decide (j.val ∈ Y)) ++ [false,true]
let valid := fun (r : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧ D.output < r+2+D.size
let pivot := fun (s j : Nat) => (2*(s/(2^(j+1)))+1)*2^j
let path := fun (h s : Nat) (v : Bool) =>
  ((Finset.range h).filter (fun j => decide (s/2^j % 2=1)=v)).image (pivot s)
∀ (a d e : Nat) (L : Fin (4*2^a) → Fin 3 → Fin e × Bool), d ≤ e →
  let H := 2^a
  let M := 4*H
  let off := d+4*e+2*M
  let r := off+M
  let pins := fun (s : Fin M) (j : Fin 3) (v : Bool) =>
    let l := L s j
    let left := decide (s.val<2*H)
    let z := d+(if left then 0 else 2*e)+2*l.1.val
    let lit := z+(if l.2=v then 1 else 0)
    let pub : Finset Nat := if l.1.val<d ∧ l.2=true ∧ left=v then {l.1.val} else ∅
    let selector := ((Finset.range 2).filter (fun k => decide (j.val/2^k % 2=1)=v)).image (fun k => d+4*e+2*s.val+k)
    insert lit (pub ∪ selector ∪ (path (a+2) s.val v).image (fun i => off+i))
  let cell := fun (s : Fin M) (j : Fin 3) (Y : Finset Nat) =>
    Y ⊆ Finset.range r ∧ pins s j true ⊆ Y ∧ Disjoint (pins s j false) Y
  let sat := fun (side : Bool) (w : Fin e → Bool) =>
    ∀ s : Fin M, decide (s.val<2*H)=side → ∃ j, w (L s j).1=(L s j).2
  let pos := fun X : Finset Nat => ∃ w, sat true w ∧ ∀ i : Fin e, i.val<d → w i=true → i.val ∈ X
  let neg := fun X : Finset Nat => ∃ w, sat false w ∧ ∀ i : Fin e, i.val<d → w i=true → i.val ∉ X
  let fit := fun (b p : Nat) => ∃ D : PEqualNP.CircuitLowerBounds.Circuit, valid r D ∧
    PEqualNP.NotBracket.notCount D ≤ b ∧ D.size-PEqualNP.NotBracket.notCount D ≤ p ∧
    ∀ s j Y, cell s j Y → D.eval (bits r Y)=decide (s.val % 2=0)
  let sep := fun (p : Nat) => ∃ S : PEqualNP.CircuitLowerBounds.Circuit, valid d S ∧
    PEqualNP.NotBracket.notCount S=0 ∧ S.size ≤ p ∧
    ∀ X ⊆ Finset.range d, (pos X → S.eval (bits d X)=true) ∧ (neg X → S.eval (bits d X)=false)
  ((∃ p, fit (a+1) p) ↔ ∀ X ⊆ Finset.range d, pos X → ¬neg X) ∧
  (∀ p, fit (a+1) p → sep p) ∧
  ((∃ X ⊆ Finset.range d, pos X ∨ neg X) → ∀ p, ¬fit a p) ∧
  fit (a+2) (6*M)) := by
  intro bits valid pivot path a d e L hde H M off r pins cell sat pos neg fit sep
  have hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x := by
    intro s j v x
    simp only [pins, path, pivot, PM, H, M, off, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range, dec_iff, or_assoc]
    refine or_congr ?_ (or_congr ?_ (or_congr ?_ ?_))
    · by_cases hs : s.val < 2*2^a <;> by_cases hb : (L s j).2 = v <;> simp [hs, hb]
    · split_ifs with h <;> simp [h]
    · constructor
      · rintro ⟨k, ⟨h1, h2⟩, rfl⟩; exact ⟨k, h1, h2, rfl⟩
      · rintro ⟨k, h1, h2, rfl⟩; exact ⟨k, ⟨h1, h2⟩, rfl⟩
    · constructor
      · rintro ⟨_, ⟨k, ⟨h1, h2⟩, rfl⟩, rfl⟩; exact ⟨k, h1, h2, rfl⟩
      · rintro ⟨k, h1, h2, rfl⟩; exact ⟨_, ⟨k, ⟨h1, h2⟩, rfl⟩, rfl⟩
  clear_value pins
  have answer := PEqualNP.Outside.L_lib_1435_aux.solve L pins hp
  simpa only [fit,sep,cell,sat,pos,neg,r,off,M,H,bits,valid,PEqualNP.Outside.L_lib_1435_aux.Fit,PEqualNP.Outside.L_lib_1435_aux.Sep,
    Cell,Yes,No,Valid,input,n,PEqualNP.Outside.L_lib_1435_aux.off,PEqualNP.Outside.L_lib_1435_aux.M,
    decide_eq_true_eq,decide_eq_false_iff_not,normTruth,truthYes,truthNo] using answer

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43982

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276813544 * 2 ^ 32 + 4276791432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x002018680424d501#64 ++ 0x40002018680424d5#64 ++ 0x09e038f80c7fffff#64 ++ 0xb809e038f80c7fff#64 : BitVec 256),
   (0x1290c31431922a2c#64 ++ 0x801290c31431922a#64 ++ 0x3691c71c73923f77#64 ++ 0x7a3691c71c73923f#64 : BitVec 256),
   (0x451605a582e34c49#64 ++ 0x01451605a582e34c#64 ++ 0xc71e07e783e3ccee#64 ++ 0xedc71e07e783e3cc#64 : BitVec 256),
   (0xa81b6806dc03b00e#64 ++ 0x02a81b6806dc03b0#64 ++ 0xf81ff807fc03f0dd#64 ++ 0xf7f81ff807fc03f0#64 : BitVec 256),
   (0xffc000036b580070#64 ++ 0x08ffc000036b5800#64 ++ 0xffe00007fffc00c3#64 ++ 0xf9ffe00007fffc00#64 : BitVec 256),
   (0xffedb6d800000080#64 ++ 0x04ffedb6d8000000#64 ++ 0xfffffff80000003f#64 ++ 0xe6fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80c7fffff 0xb809e038f80c7fff

def z1 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c73923f77 0x7a3691c71c73923f

def z2 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3ccee 0xedc71e07e783e3cc

def z3 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc03f0dd 0xf7f81ff807fc03f0

def z4 : W := mkw 0xffc0000000000000 0x00ffc00000000000 0xffe000000c7c00c3 0xf8ffe000000c7c00

def z5 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe00007fffc00c3 0xf9ffe00007fffc00

def z6 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff80000003f 0xe6fffffff8000000

def z7 : W := mkw 0xed4000034a480050 0x08ed4000034a4800 0xc96000038c6c0080 0x81c96000038c6c00

def z8 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffffffc00ff 0xfffffffffffffc00

def z9 : W := mkw 0x4504048000000000 0x0045040480000000 0x070007e000000022 0x00070007e0000000

def z10 : W := mkw 0xa82938680424d501 0x40a82938680424d5 0xf9fff8f80c7fffff 0xfef9fff8f80c7fff

def z11 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x001ffff80000003c 0x06001ffff8000000

def z12 : W := mkw 0x4512012582e34c49 0x014512012582e34c 0xc700000783e3ccc2 0xe9c700000783e3cc

def z13 : W := mkw 0xffcda69000000080 0x04ffcda690000000 0xffffc70000000003 0xe6ffffc700000000

def z14 : W := mkw 0x57c0000123580070 0x0857c00001235800 0x37e0000473fc0043 0x7837e0000473fc00

def z15 : W := mkw 0xffc405a36bf84c71 0x09ffc405a36bf84c 0xffe007e7fffc0ce3 0xf9ffe007e7fffc0c

def z16 : W := mkw 0xbae9b25800000080 0x04bae9b258000000 0x38e1f81800000011 0x0238e1f818000000

def z17 : W := mkw 0x00124806dc03b00e 0x0200124806dc03b0 0x00000007fc03f0c0 0x1100000007fc03f0

def z18 : W := mkw 0x57e496d800000080 0x0457e496d8000000 0x07e007f800000022 0x0007e007f8000000

def z19 : W := mkw 0x1280821021100020 0x0012808210211000 0x3691c71c73900077 0x7a3691c71c739000

def z20 : W := mkw 0xa80b2802cc019002 0x02a80b2802cc0190 0xc80e38038c01c088 0x85c80e38038c01c0

def z21 : W := mkw 0xba9beb16fd93ba2e 0x82ba9beb16fd93ba 0xfe9fff1fff93ffff 0xfffe9fff1fff93ff

def z22 : W := mkw 0xed6d34c800000080 0x04ed6d34c8000000 0xc96e38e000000008 0x84c96e38e0000000

def z23 : W := mkw 0xfffdf7dc31922aac 0x84fffdf7dc31922a 0xfffffffc73923f7f 0xfefffffffc73923f

def z24 : W := mkw 0x000405a000a04c01 0x01000405a000a04c 0x000007e000000c20 0x00000007e000000c

def z25 : W := mkw 0x0020106800244501 0x4000201068002445 0x09e000f80c7c0fe3 0xb809e000f80c7c0f

def z26 : W := mkw 0x4516058582c30848 0x014516058582c308 0xc61e070783820c66 0x6dc61e070783820c

def z27 : W := mkw 0xed4000034a480050 0x08ed4000034a4800 0xc9e000038c7c00c3 0xb9c9e000038c7c00

def z28 : W := mkw 0xfffff6ded803208e 0x06fffff6ded80320 0xfffffffff000003f 0xe7fffffffff00000

def z29 : W := mkw 0xffd0c3177bda2a7c 0x88ffd0c3177bda2a 0xf611c707f3800000 0x43f611c707f38000

def z30 : W := mkw 0x002018680424d501 0x40002018680424d5 0x08e038f80c1fff3d 0x1008e038f80c1fff

def z31 : W := mkw 0x001605a480a34c09 0x01001605a480a34c 0x001e07e00003cc2c 0x04001e07e00003cc

def z32 : W := mkw 0xbac0000269180030 0x08bac00002691800 0x38e000007c1c0001 0x1038e000007c1c00

def z33 : W := mkw 0x002018680424d501 0x40002018680424d5 0x096038e00c6dc088 0x80096038e00c6dc0

def z34 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3611c70473800000 0x423611c704738000

def z35 : W := mkw 0x0010c31410822a0c 0x800010c31410822a 0x0011c70000000000 0x020011c700000000

def z36 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x09fffff80000003f 0xa609fffff8000000

def z37 : W := mkw 0x0010c31410822a0c 0x800010c31410822a 0x0611c71c03823f76 0x6a0611c71c03823f

def z38 : W := mkw 0x00124806dc03b00e 0x0200124806dc03b0 0xc01e0007fc03f0cc 0xf5c01e0007fc03f0

def z39 : W := mkw 0xa809200000000000 0x00a8092000000000 0xf81ff8000000001d 0xe6f81ff800000000

def z40 : W := mkw 0xbae9b25a691800b0 0x0cbae9b25a691800 0x38e1f8187c1c0011 0x1238e1f8187c1c00

def z41 : W := mkw 0x1280831021900a20 0x801280831021900a 0x0680071803900f22 0x080680071803900f

def z42 : W := mkw 0x5796c7b5b3f36e6d 0x815796c7b5b3f36e 0xf79fc7fff3f3ffff 0xfff79fc7fff3f3ff

def z43 : W := mkw 0x1280c31031902a24 0x801280c31031902a 0x3681c71873903f33 0x1a3681c71873903f

def z44 : W := mkw 0xffdb6807ff5bb07e 0x0affdb6807ff5bb0 0xfffff807fffff0df 0xfffffff807fffff0

def z45 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xff7fffe000000008 0xc6ff7fffe0000000

def z46 : W := mkw 0x452414c800000000 0x00452414c8000000 0xcffe3ff80000003f 0xe4cffe3ff8000000

def z47 : W := mkw 0x0020104800000000 0x0000201048000000 0x000038f80000003c 0x00000038f8000000

def z48 : W := mkw 0x000000036b580070 0x08000000036b5800 0x00000007f3800000 0x0100000007f38000

def z49 : W := mkw 0x002018680424d501 0x40002018680424d5 0x096038e00c6ff0dd 0xb0096038e00c6ff0

def z50 : W := mkw 0xfffffededc03b08e 0x06fffffededc03b0 0xfffffffffc03f0ff 0xf7fffffffffc03f0

def z51 : W := mkw 0x4516048480030008 0x0045160484800300 0xc71e07e78003c0ee 0xe5c71e07e78003c0

def z52 : W := mkw 0xffe018680424d501 0x40ffe018680424d5 0xffe038f80c7fffff 0xf8ffe038f80c7fff

def z53 : W := mkw 0xa81b6006d803200e 0x02a81b6006d80320 0xf01fc007f0000000 0x47f01fc007f00000

def z54 : W := mkw 0x12a0da783534f725 0xc012a0da783534f7 0x39e1f8f87c7fffff 0xba39e1f8f87c7fff

def z55 : W := mkw 0xa81040065802200c 0x00a8104006580220 0xf811c007fc0230d5 0xf3f811c007fc0230

def z56 : W := mkw 0x0009200000000000 0x0000092000000000 0x001ff8000000001c 0x06001ff800000000

def z57 : W := mkw 0x0016c7b490a36e0d 0x810016c7b490a36e 0x001fc7f80003ff3c 0x06001fc7f80003ff

def z58 : W := mkw 0xffedf6d8311022a4 0x84ffedf6d8311022 0xfffffff87010333f 0xf6fffffff8701033

def z59 : W := mkw 0x1280000021100020 0x0012800000211000 0x3680000473900043 0x7836800004739000

def z60 : W := mkw 0xbac968027d18b036 0x0abac968027d18b0 0x38e1f8007c1c3011 0x1238e1f8007c1c30

def z61 : W := mkw 0xa800000248000000 0x00a8000002480000 0xf9e00007fc7c00c3 0xf9f9e00007fc7c00

def z62 : W := mkw 0x4514058400820808 0x0045140584008208 0xc71e07e403820c6e 0xecc71e07e403820c

def z63 : W := mkw 0xa80968025c00b006 0x02a80968025c00b0 0xf801f807fc0030d1 0xf3f801f807fc0030

def z64 : W := mkw 0x451f6da596e3fc4f 0x03451f6da596e3fc 0xc71fffe783e3fcfe 0xefc71fffe783e3fc

def z65 : W := mkw 0xffedbed804009080 0x04ffedbed8040090 0xfffffff80c03f0ff 0xf6fffffff80c03f0

def z66 : W := mkw 0x129040043112202c 0x0012904004311220 0x3691c00473923057 0x7a3691c004739230

def z67 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000003c0cc 0xa0000000000003c0

def z68 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3611c71c73823f34 0x423611c71c73823f

def z69 : W := mkw 0x0000000000000000 0x0000000000000000 0x09e000000c7c00c3 0xb809e000000c7c00

def z70 : W := mkw 0xffe0186b6f7cd571 0x48ffe0186b6f7cd5 0xffe038ffffffffff 0xf9ffe038ffffffff

def z71 : W := mkw 0x0010010400820808 0x0000100104008208 0x0010070000020c24 0x000010070000020c

def z72 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff800123f7f 0xfefffffff800123f

def z73 : W := mkw 0x000008200424d501 0x40000008200424d5 0x000000000c7fffc0 0x18000000000c7fff

def z74 : W := mkw 0x1292c314b1932a2c 0x801292c314b1932a 0xf69fc71ff393ffff 0xfff69fc71ff393ff

def z75 : W := mkw 0x4500000102400040 0x0045000001024000 0xc700000783e000c2 0xe9c700000783e000

def z76 : W := mkw 0xffd605a7ebfb4c79 0x09ffd605a7ebfb4c 0xfffe07e7ffffccef 0xfdfffe07e7ffffcc

def z77 : W := mkw 0x00120127ebfb4c79 0x0900120127ebfb4c 0x00000007ffffccc0 0x1900000007ffffcc

def z78 : W := mkw 0x0020106800244501 0x4000201068002445 0x09e038f8007c0f3f 0xa809e038f8007c0f

def z79 : W := mkw 0xffc008236f7cd571 0x48ffc008236f7cd5 0xffe00007ffffffc3 0xf9ffe00007ffffff

def z80 : W := mkw 0xbaedb6d800000080 0x04baedb6d8000000 0x38fffff80000003d 0x0638fffff8000000

def z81 : W := mkw 0x4504048000000000 0x0045040480000000 0xc61e070000000000 0x44c61e0700000000

def z82 : W := mkw 0x0020106800244501 0x4000201068002445 0x01e000f8007c0f22 0x0801e000f8007c0f

def z83 : W := mkw 0xffc604a3eb794471 0x09ffc604a3eb7944 0xffee00e7fffdc0cb 0xfdffee00e7fffdc0

def z84 : W := mkw 0xa809200000000000 0x00a8092000000000 0xc80e380000000008 0x84c80e3800000000

def z85 : W := mkw 0x002018680424d501 0x40002018680424d5 0x096038f80c6fffbc 0x80096038f80c6fff

def z86 : W := mkw 0x001b68049403b00e 0x02001b68049403b0 0x301ff8047003f05d 0x76301ff8047003f0

def z87 : W := mkw 0x002018680424d501 0x40002018680424d5 0x010038f80063fffe 0xa8010038f80063ff

def z88 : W := mkw 0x45361ded86e7dd49 0x4145361ded86e7dd 0xcffe3fff8fffffff 0xfdcffe3fff8fffff

def z89 : W := mkw 0x450405a102e04c41 0x01450405a102e04c 0x070007e003e00c22 0x08070007e003e00c

def z90 : W := mkw 0x001040041002200c 0x0000104004100220 0x3011c00470023055 0x723011c004700230

def z91 : W := mkw 0x0010012400a24c09 0x000010012400a24c 0x071007e403e3ccee 0xe8071007e403e3cc

def z92 : W := mkw 0x450605a182e14c41 0x01450605a182e14c 0xc70e07e383e1ccaa 0x8dc70e07e383e1cc

def z93 : W := mkw 0xffedb6d9235800f0 0x0cffedb6d9235800 0xfffffff803fc003f 0xeefffffff803fc00

def z94 : W := mkw 0x003ffedc9403b08e 0x06003ffedc9403b0 0x001ffff80003f03c 0x06001ffff80003f0

def z95 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf01ff807f003f01c 0x47f01ff807f003f0

def z96 : W := mkw 0x57c000036b580070 0x0857c000036b5800 0x07e00007fffc00c2 0x1907e00007fffc00

def z97 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000000100043 0x3800800000001000

def z98 : W := mkw 0x0000000000000000 0x0000000000000000 0x08e000000c1c0001 0x1008e000000c1c00

def z99 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf9fff807fc7ff0df 0xfff9fff807fc7ff0

def z100 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe0001ffffe3ff7 0xf9ffe0001ffffe3f

def z101 : W := mkw 0xffe0186b6f7cd571 0x48ffe0186b6f7cd5 0xffe038e7fffdc0cb 0xf9ffe038e7fffdc0

def z102 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3ff1c71c7ffe3ff7 0xfa3ff1c71c7ffe3f

def z103 : W := mkw 0x001b68049403b00e 0x02001b68049403b0 0xc01ff8078003f0dc 0xe7c01ff8078003f0

def z104 : W := mkw 0xfffdf7df7bda2afc 0x8cfffdf7df7bda2a 0xfffffffffffe3fff 0xfffffffffffffe3f

def z105 : W := mkw 0xed6d34cb4a4800d0 0x0ced6d34cb4a4800 0xc96e38e38c6c0088 0x85c96e38e38c6c00

def z106 : W := mkw 0x0020184804049100 0x4000201848040491 0x08e038180c1c3311 0x1008e038180c1c33

def z107 : W := mkw 0x4516058582c30848 0x014516058582c308 0xc61e070783800000 0x45c61e0707838000

def z108 : W := mkw 0x0000080004009000 0x0000000800040090 0x000000000c03f0c0 0x10000000000c03f0

def z109 : W := mkw 0xffedb6db4a4800d0 0x0cffedb6db4a4800 0xfffffffb8c6c00bf 0xe7fffffffb8c6c00

def z110 : W := mkw 0x0000000102400040 0x0000000001024000 0x0000000783e000c0 0x090000000783e000

def z111 : W := mkw 0xffcda69000000080 0x04ffcda690000000 0xf61fc70000000000 0x46f61fc700000000

def z112 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80c7c3f33 0x1809e038f80c7c3f

def z113 : W := mkw 0xed1f6c86dc03b00e 0x02ed1f6c86dc03b0 0xff1fffe7fc03f0ff 0xf7ff1fffe7fc03f0

def z114 : W := mkw 0xbabbfb7efdb7ff2f 0xc2babbfb7efdb7ff 0xffffffffffffffff 0xffffffffffffffff

def z115 : W := mkw 0x000008200424d501 0x40000008200424d5 0x000000000c6dc080 0x00000000000c6dc0

def z116 : W := mkw 0xffedb6d9024000c0 0x04ffedb6d9024000 0xffffffff83e000ff 0xefffffffff83e000

def z117 : W := mkw 0xffd60587ebdb0878 0x09ffd60587ebdb08 0xfffe0707fffc00c3 0xfdfffe0707fffc00

def z118 : W := mkw 0xffd605a7ebfb4c79 0x09ffd605a7ebfb4c 0xf71e07e7f3e3ccee 0xedf71e07e7f3e3cc

def z119 : W := mkw 0xffdfee96dc03b08e 0x06ffdfee96dc03b0 0xfe1fff07fc03f0dd 0xf7fe1fff07fc03f0

def z120 : W := mkw 0x0030db7c14a6ff0d 0xc00030db7c14a6ff 0x09f1fff80c7fffff 0xba09f1fff80c7fff

def z121 : W := mkw 0xffc082136b580070 0x08ffc082136b5800 0xfff1c71ffffc00f7 0xfbfff1c71ffffc00

def z122 : W := mkw 0x1290831400820808 0x0012908314008208 0x3691c71c03820c77 0x6a3691c71c03820c

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080001800123f77 0x380080001800123f

def z124 : W := mkw 0xffd0c3177bda2a7c 0x88ffd0c3177bda2a 0xfff1c71ffffe3ff7 0xfbfff1c71ffffe3f

def z125 : W := mkw 0xbac0000269180030 0x08bac00002691800 0x3000000070000000 0x0030000000700000

def z126 : W := mkw 0x1280c21031102224 0x801280c210311022 0x3081c01870103311 0x123081c018701033

def z127 : W := mkw 0x450604a182614441 0x01450604a1826144 0xc10e00e38061c088 0x85c10e00e38061c0

def z128 : W := mkw 0x0029b25800000080 0x040029b258000000 0x0001f81800000010 0x020001f818000000

def z129 : W := mkw 0xa80b2002c8010002 0x02a80b2002c80100 0xc00e000380000000 0x05c00e0003800000

def z130 : W := mkw 0x57e497d821900aa0 0x8457e497d821900a 0x07e007f803900f22 0x0807e007f803900f

def z131 : W := mkw 0x002dbef80424d581 0x44002dbef80424d5 0x09fffff80c7fffff 0xbe09fffff80c7fff

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080001800100f22 0x080080001800100f

def z133 : W := mkw 0x00124927dee3fc4f 0x0300124927dee3fc 0x00000007ffe3fcc0 0x1900000007ffe3fc

def z134 : W := mkw 0xed1f6da7dee3fc4f 0x03ed1f6da7dee3fc 0xff1fffe7ffe3fcff 0xffff1fffe7ffe3fc

def z135 : W := mkw 0x0012012582e34c49 0x010012012582e34c 0x0000000783e3ccc0 0x090000000783e3cc

def z136 : W := mkw 0x000008200424d501 0x40000008200424d5 0x09e000000c7fffc3 0xb809e000000c7fff

def z137 : W := mkw 0x0016058480830808 0x0100160584808308 0x001e070000000000 0x04001e0700000000

def z138 : W := mkw 0x57c0000123580070 0x0857c00001235800 0x07e0000003fc0002 0x0807e0000003fc00

def z139 : W := mkw 0x4504048102400040 0x0045040481024000 0xc71e07e783e000ee 0xedc71e07e783e000

def z140 : W := mkw 0x0032586edc27f50f 0x420032586edc27f5 0x09e038fffc7fffff 0xb909e038fffc7fff

def z141 : W := mkw 0x57e49ef80424d581 0x4457e49ef80424d5 0x0fe03ff80c7fffff 0xb80fe03ff80c7fff

def z142 : W := mkw 0x001248049403b00e 0x02001248049403b0 0x000000000003f000 0x00000000000003f0

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x01000000006000c2 0xa801000000006000

def z144 : W := mkw 0x001b68049403b00e 0x02001b68049403b0 0x081ff8000c03f0dd 0xb6081ff8000c03f0

def z145 : W := mkw 0x45160da586e7dd49 0x4145160da586e7dd 0xc71e07e78fffffee 0xfdc71e07e78fffff

def z146 : W := mkw 0x0010010400820808 0x0000100104008208 0x0610070403820c66 0x680610070403820c

def z147 : W := mkw 0xba89ea127d10b226 0x82ba89ea127d10b2 0x3881f8187c103311 0x123881f8187c1033

def z148 : W := mkw 0x57e496d800000080 0x0457e496d8000000 0x37f1c7f800000037 0x6237f1c7f8000000

def z149 : W := mkw 0xa81b6826dc23f40f 0x02a81b6826dc23f4 0xf91ff8e7fc63fcff 0xfff91ff8e7fc63fc

def z150 : W := mkw 0x0000080004009000 0x0000000800040090 0x000038000003f01c 0x00000038000003f0

def z151 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff80c7c00ff 0xfefffffff80c7c00

def z152 : W := mkw 0x4504058102c00840 0x014504058102c008 0x0600070003800000 0x0006000700038000

def z153 : W := mkw 0xffffb7fd82e34cc9 0x05ffffb7fd82e34c 0xffffffff83e3ccff 0xefffffffff83e3cc

def z154 : W := mkw 0x450405a102e04c41 0x01450405a102e04c 0xc70007e783e00ce2 0xe9c70007e783e00c

def z155 : W := mkw 0x000000036b580070 0x08000000036b5800 0x00000007fffc00c0 0x1900000007fffc00

def z156 : W := mkw 0x12b0d35c31922a2c 0x8012b0d35c31922a 0x3ff1fffc73923f7f 0xfa3ff1fffc73923f

def z157 : W := mkw 0xffd24807ff5bb07e 0x0affd24807ff5bb0 0xffe00007fffff0c3 0xf9ffe00007fffff0

def z158 : W := mkw 0x0010410410822a0c 0x800010410410822a 0x0000000000023f00 0x000000000000023f

def z159 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf89ff81ffc13ffff 0xfff89ff81ffc13ff

def z160 : W := mkw 0x00361dec84a7dd09 0x4100361dec84a7dd 0x001e3ff80003ff3c 0x04001e3ff80003ff

def z161 : W := mkw 0xbae9ba5804049180 0x44bae9ba58040491 0x38e1f8180c1c3311 0x1238e1f8180c1c33

def z162 : W := mkw 0xa80000036b580070 0x08a80000036b5800 0xf8000007fffc00c1 0xf9f8000007fffc00

def z163 : W := mkw 0x0000002000204401 0x0000000020002044 0x010000e00063ccee 0xa8010000e00063cc

def z164 : W := mkw 0xed6d3ce80424d581 0x44ed6d3ce80424d5 0xc96e38e00c6dc088 0x84c96e38e00c6dc0

def z165 : W := mkw 0x12adb6d800000080 0x0412adb6d8000000 0x369ffff80000003f 0x66369ffff8000000

def z166 : W := mkw 0xba9be316f9932a2e 0x82ba9be316f9932a 0xf69fc71ff3923f77 0x7ff69fc71ff3923f

def z167 : W := mkw 0xed1f65a7dae36c4f 0x03ed1f65a7dae36c 0xf71fc7e7f3e3ccee 0xeff71fc7e7f3e3cc

def z168 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcffe07e78fffccef 0xfdcffe07e78fffcc

def z169 : W := mkw 0x1290cb3435b6ff2d 0xc01290cb3435b6ff 0x3691c71c7ffffff7 0x7a3691c71c7fffff

def z170 : W := mkw 0x4516058582c30848 0x014516058582c308 0xc61e07078383c0cc 0xe5c61e07078383c0

def z171 : W := mkw 0x1280000021100020 0x0012800000211000 0x3080000070100001 0x1030800000701000

def z172 : W := mkw 0xed7f35ed82e34cc9 0x05ed7f35ed82e34c 0xcf7e3fe783e3ccee 0xedcf7e3fe783e3cc

def z173 : W := mkw 0xa800000248000000 0x00a8000002480000 0xf8000007fc0000c1 0xf1f8000007fc0000

def z174 : W := mkw 0xfffdb7dc00820888 0x04fffdb7dc008208 0xfffffffc03820c7f 0xeefffffffc03820c

def z175 : W := mkw 0x0010c31410822a0c 0x800010c31410822a 0x0011c71800023f34 0x020011c71800023f

def z176 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0x381ff8007c03f01d 0x16381ff8007c03f0

def z177 : W := mkw 0x0000000123580070 0x0800000001235800 0x0000000003fc0000 0x080000000003fc00

def z178 : W := mkw 0xa8124806dc03b00e 0x02a8124806dc03b0 0xf8000007fc03f0c1 0xf1f8000007fc03f0

def z179 : W := mkw 0x12b0db7c35b6ff2d 0xc012b0db7c35b6ff 0x3ff1fffc7fffffff 0xfa3ff1fffc7fffff

def z180 : W := mkw 0x1280821000000000 0x0012808210000000 0x3691c71800000037 0x623691c718000000

def z181 : W := mkw 0x0010410431922a2c 0x800010410431922a 0x0000000473923f40 0x180000000473923f

def z182 : W := mkw 0xffdb6806dc03b00e 0x02ffdb6806dc03b0 0xfffff807fc03f0df 0xf7fffff807fc03f0

def z183 : W := mkw 0xa81b68049403b00e 0x02a81b68049403b0 0xf81ff8000003f01d 0xe6f81ff8000003f0

def z184 : W := mkw 0xa81b6906dc83b80e 0x02a81b6906dc83b8 0xfe1fff07ff83fcff 0xfffe1fff07ff83fc

def z185 : W := mkw 0x001b6806dc03b00e 0x02001b6806dc03b0 0x001ff807fc03f0dc 0x17001ff807fc03f0

def z186 : W := mkw 0x12a0925800000000 0x0012a09258000000 0x3ff1fff80000003f 0xe23ff1fff8000000

def z187 : W := mkw 0xffedbef80424d581 0x44ffedbef80424d5 0xfffffff80c7fffff 0xfefffffff80c7fff

def z188 : W := mkw 0x4510010502c20848 0x004510010502c208 0xc710070783e20ce6 0xe9c710070783e20c

def z189 : W := mkw 0xffe9b25b6b5800f0 0x0cffe9b25b6b5800 0xffe1f81ffffc00d3 0xfbffe1f81ffffc00

def z190 : W := mkw 0x000008200424d501 0x40000008200424d5 0x080038000c7fffdd 0xb8080038000c7fff

def z191 : W := mkw 0x0000002000204401 0x0000000020002044 0x000000e00003cc2c 0x00000000e00003cc

def z192 : W := mkw 0x57e496d800000080 0x0457e496d8000000 0x0fe03ff80000003f 0xa00fe03ff8000000

def z193 : W := mkw 0xed1f6ca7de63f44f 0x03ed1f6ca7de63f4 0xf91ff8e7fc63f0dd 0xf7f91ff8e7fc63f0

def z194 : W := mkw 0xed6d34c800000080 0x04ed6d34c8000000 0xf97ff8e00000001d 0xe6f97ff8e0000000

def z195 : W := mkw 0xed6f34e9826144c1 0x05ed6f34e9826144 0xc96e38e38061c088 0x85c96e38e38061c0

def z196 : W := mkw 0x002018680424d501 0x40002018680424d5 0x000038f80003ff3c 0x00000038f80003ff

def z197 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xf6000007f3800000 0x41f6000007f38000

def z198 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c73800037 0x623691c71c738000

def z199 : W := mkw 0xa81960041002200c 0x00a8196004100220 0xf81ff8047002305d 0xf6f81ff804700230

def z200 : W := mkw 0x4504048000000000 0x0045040480000000 0xc71e07e00000002e 0xe4c71e07e0000000

def z201 : W := mkw 0xffc9200000000000 0x00ffc92000000000 0xfffff8000000001f 0xe6fffff800000000

def z202 : W := mkw 0x0010492435b6ff2d 0xc00010492435b6ff 0x000000047fffffc0 0x18000000047fffff

def z203 : W := mkw 0x0000080004009000 0x0000000800040090 0x080038000c03f0dd 0xb0080038000c03f0

def z204 : W := mkw 0xa83b786edc27f50f 0x42a83b786edc27f5 0xf9fff8fffc7fffff 0xfff9fff8fffc7fff

def z205 : W := mkw 0xffcda6936b5800f0 0x0cffcda6936b5800 0xffffc707fffc00c3 0xffffffc707fffc00

def z206 : W := mkw 0xffd20127ebfb4c79 0x09ffd20127ebfb4c 0xffe00007ffffccc3 0xf9ffe00007ffffcc

def z207 : W := mkw 0x451645a592e36c4d 0x01451645a592e36c 0xf71fc7e7f3e3fcff 0xfff71fc7e7f3e3fc

def z208 : W := mkw 0x0012000480030008 0x0000120004800300 0xc01e00078003c0cc 0xe5c01e00078003c0

def z209 : W := mkw 0x1280831021900a20 0x801280831021900a 0x3691c71803900f37 0x6a3691c71803900f

def z210 : W := mkw 0x0020104800000000 0x0000201048000000 0x09e038f80c7c00ff 0xb809e038f80c7c00

def z211 : W := mkw 0xed4d248000000080 0x04ed4d2480000000 0xc00e000000000000 0x04c00e0000000000

def z212 : W := mkw 0x0020104800000000 0x0000201048000000 0x096038e000000008 0x80096038e0000000

def z213 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe00007f3800003 0xe1ffe00007f38000

def z214 : W := mkw 0xa80b6802dc01b006 0x02a80b6802dc01b0 0xf80ff803fc01f099 0x97f80ff803fc01f0

def z215 : W := mkw 0xffc968037f58b076 0x0affc968037f58b0 0xffe1f807fffc30d3 0xfbffe1f807fffc30

def z216 : W := mkw 0xffc4048000000000 0x00ffc40480000000 0xfffe07e00000002f 0xe4fffe07e0000000

def z217 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3611c70473820c66 0x6a3611c70473820c

def z218 : W := mkw 0x450604a182614441 0x01450604a1826144 0xc70e00e783e1c0ca 0xedc70e00e783e1c0

def z219 : W := mkw 0x452db6d800000080 0x04452db6d8000000 0xc71ffff80000003e 0xe6c71ffff8000000

def z220 : W := mkw 0x1280000021100020 0x0012800000211000 0x3fe000047ffc00c3 0xf83fe000047ffc00

def z221 : W := mkw 0xed6d34c800000080 0x04ed6d34c8000000 0xcf7e3fe00000002e 0xe4cf7e3fe0000000

def z222 : W := mkw 0x450604a182614441 0x01450604a1826144 0xc71e07e38061c0ae 0xe5c71e07e38061c0

def z223 : W := mkw 0x0020106800204401 0x0000201068002044 0x09e038f80063ccff 0xa809e038f80063cc

def z224 : W := mkw 0x000000036b580070 0x08000000036b5800 0x09e00007fffc00c3 0xb909e00007fffc00

def z225 : W := mkw 0xa81b6006d803200e 0x02a81b6006d80320 0xf01fc007f003c0cc 0xe7f01fc007f003c0

def z226 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf01fc007fc03f0c0 0x57f01fc007fc03f0

def z227 : W := mkw 0x0020104800000000 0x0000201048000000 0x09e038f80000003f 0xa009e038f8000000

def z228 : W := mkw 0x0030196c04a6dd09 0x400030196c04a6dd 0x0ff03ffc0fffffff 0xf80ff03ffc0fffff

def z229 : W := mkw 0x1280831021900a20 0x801280831021900a 0x0680071803923f77 0x380680071803923f

def z230 : W := mkw 0x0000400031102224 0x8000004000311022 0x0000000070103300 0x1000000000701033

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000007800000c0 0xe1c0000007800000

def z232 : W := mkw 0x000008200424d501 0x40000008200424d5 0x010000e00c7fffee 0xb8010000e00c7fff

def z233 : W := mkw 0x450405a102e04c41 0x01450405a102e04c 0xc71e07e003e00c2e 0xecc71e07e003e00c

def z234 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xff600007ffec0080 0xc1ff600007ffec00

def z235 : W := mkw 0x4500000102400040 0x0045000001024000 0x0700000003e00002 0x080700000003e000

def z236 : W := mkw 0xa81b6006d803200e 0x02a81b6006d80320 0xf01fc007f0023055 0x77f01fc007f00230

def z237 : W := mkw 0x452415e902e44d41 0x41452415e902e44d 0x07e007f803fc0f22 0x0807e007f803fc0f

def z238 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000403800042 0x6806000004038000

def z239 : W := mkw 0x0000000000000000 0x0000000000000000 0x09e000180c7e3ff7 0xb809e000180c7e3f

def z240 : W := mkw 0xed5605a7caeb4c59 0x09ed5605a7caeb4c 0xcf7e07e78fefccee 0xedcf7e07e78fefcc

def z241 : W := mkw 0xa820186a4c24d501 0x40a820186a4c24d5 0xf9e038fffc7fffff 0xf9f9e038fffc7fff

def z242 : W := mkw 0x57f4d7dc31922aac 0x8457f4d7dc31922a 0x37f1c7fc73923f77 0x7a37f1c7fc73923f

def z243 : W := mkw 0xbae9b25800000080 0x04bae9b258000000 0x39e1f8f80000003f 0xa239e1f8f8000000

def z244 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffff380003f 0xe7fffffffff38000

def z245 : W := mkw 0x0020106800244501 0x4000201068002445 0x01e000f8007e3f77 0x3801e000f8007e3f

def z246 : W := mkw 0xed4000036b580070 0x08ed4000036b5800 0xc9600007fffc00c0 0x99c9600007fffc00

def z247 : W := mkw 0xffedb6da48000080 0x04ffedb6da480000 0xfffffffffc0000ff 0xf7fffffffffc0000

def z248 : W := mkw 0xffedbefb6f7cd5f1 0x4cffedbefb6f7cd5 0xffffffffffffffff 0xffffffffffffffff

def z249 : W := mkw 0x1280821021100220 0x8012808210211002 0x0080001800100300 0x0000800018001003

def z250 : W := mkw 0x000604a080214401 0x01000604a0802144 0x000e00e00001c008 0x04000e00e00001c0

def z251 : W := mkw 0xffedfeda5c00b086 0x06ffedfeda5c00b0 0xfffffff87c00303f 0xf6fffffff87c0030

def z252 : W := mkw 0x0020104800040100 0x4000201048000401 0x00e00018001c0300 0x0000e00018001c03

def z253 : W := mkw 0xa82b386acc25d503 0x42a82b386acc25d5 0xc9ee38fb8c7fffff 0xbdc9ee38fb8c7fff

def z254 : W := mkw 0x0012012582e34c49 0x010012012582e34c 0xc01e000783e3cccc 0xedc01e000783e3cc

def z255 : W := mkw 0x0000002000204401 0x0000000020002044 0x010000e000600c22 0x08010000e000600c

def z256 : W := mkw 0xffffb7dd82c308c8 0x05ffffb7dd82c308 0xffffffff8380003f 0xe7ffffffff838000

def z257 : W := mkw 0x4512000582430048 0x0045120005824300 0xc71e000783e3c0ce 0xedc71e000783e3c0

def z258 : W := mkw 0x0010c31410822a0c 0x800010c31410822a 0x3011c71c70023f75 0x723011c71c70023f

def z259 : W := mkw 0xed1f25a582e34c49 0x01ed1f25a582e34c 0xff1fffe783e3ccff 0xefff1fffe783e3cc

def z260 : W := mkw 0x5790c31533d22a6c 0x805790c31533d22a 0xf791c71ff3f23ff7 0xfbf791c71ff3f23f

def z261 : W := mkw 0x00124806dc03b00e 0x0200124806dc03b0 0x08003807fc03f0dd 0xb108003807fc03f0

def z262 : W := mkw 0xffedb6da691800b0 0x0cffedb6da691800 0xfffffff87c1c003f 0xf6fffffff87c1c00

def z263 : W := mkw 0x001b68049403b00e 0x02001b68049403b0 0x001ff8000003f01c 0x06001ff8000003f0

def z264 : W := mkw 0xffedbef80424d581 0x44ffedbef80424d5 0xfffffff80003ff3f 0xe6fffffff80003ff

def z265 : W := mkw 0x0004048000000000 0x0000040480000000 0x001e07e00000002c 0x04001e07e0000000

def z266 : W := mkw 0xffedb6d8211000a0 0x04ffedb6d8211000 0xfffffffc7390007f 0xfefffffffc739000

def z267 : W := mkw 0xed0d248000000000 0x00ed0d2480000000 0xff1fffe00000003f 0xe6ff1fffe0000000

def z268 : W := mkw 0x0012012582e34c49 0x010012012582e34c 0x010000e783e3ccee 0xa9010000e783e3cc

def z269 : W := mkw 0xa82db6d800000080 0x04a82db6d8000000 0xf81ffff80000003d 0xe6f81ffff8000000

def z270 : W := mkw 0x451405a502e24c49 0x01451405a502e24c 0x071007e403e20c66 0x68071007e403e20c

def z271 : W := mkw 0xffed34c800000080 0x04ffed34c8000000 0xffee38e00000000b 0xe4ffee38e0000000

def z272 : W := mkw 0x0012000480030008 0x0000120004800300 0x001e00000003c00c 0x04001e00000003c0

def z273 : W := mkw 0xed1605a7cae34c49 0x01ed1605a7cae34c 0xff1e07e7ffe3ccef 0xfdff1e07e7ffe3cc

def z274 : W := mkw 0xa83b786edc27f50f 0x42a83b786edc27f5 0xf81ff8fffc03fffd 0xf7f81ff8fffc03ff

def z275 : W := mkw 0x453615ed82e34c49 0x01453615ed82e34c 0xcffe3fff83e3ccff 0xedcffe3fff83e3cc

def z276 : W := mkw 0xffd6c7b7fbfb6e7d 0x89ffd6c7b7fbfb6e 0xffffc7ffffffffff 0xffffffc7ffffffff

def z277 : W := mkw 0x1290410431922a2c 0x801290410431922a 0x3680000473923f43 0x783680000473923f

def z278 : W := mkw 0x45361ded86e7dd49 0x4145361ded86e7dd 0xcf7e3fe78fefccee 0xedcf7e3fe78fefcc

def z279 : W := mkw 0xed6db6d800000080 0x04ed6db6d8000000 0xc97ffff80000003c 0x86c97ffff8000000

def z280 : W := mkw 0x00124806dc03b00e 0x0200124806dc03b0 0x3011c007fc03f0d5 0x733011c007fc03f0

def z281 : W := mkw 0xffc0000248000000 0x00ffc00002480000 0xffe00007fc0000c3 0xf1ffe00007fc0000

def z282 : W := mkw 0x57c4869000000080 0x0457c48690000000 0x0600070000000000 0x0006000700000000

def z283 : W := mkw 0x0030586c1426f50d 0x400030586c1426f5 0x39f1f8fc7c7fffff 0xfa39f1f8fc7c7fff

def z284 : W := mkw 0x0020104800000000 0x0000201048000000 0x09e038f800123f7f 0xb809e038f800123f

def z285 : W := mkw 0xffdb6007fb5b207e 0x0affdb6007fb5b20 0xf61fc007f3800000 0x47f61fc007f38000

def z286 : W := mkw 0x0012012480a34c09 0x010012012480a34c 0x000000000003cc00 0x00000000000003cc

def z287 : W := mkw 0x1280c21031102224 0x801280c210311022 0x3081c01870123f77 0x3a3081c01870123f

def z288 : W := mkw 0x1290c2143112222c 0x801290c214311222 0x3091c01c70123355 0x723091c01c701233

def z289 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3081c01c73923f51 0x1a3081c01c73923f

def z290 : W := mkw 0x0000000248000000 0x0000000002480000 0x00000007fc0000c0 0x1100000007fc0000

def z291 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e1c088 0xc5c71e07e783e1c0

def z292 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc61e07e78383cc2c 0x45c61e07e78383cc

def z293 : W := mkw 0xbae0184a6d1c9130 0x48bae0184a6d1c91 0x38e038187c1c3311 0x1038e038187c1c33

def z294 : W := mkw 0xba90c31679922a2c 0x80ba90c31679922a 0xfe91c71fff923ff7 0xfbfe91c71fff923f

def z295 : W := mkw 0xffdde79431922aac 0x84ffdde79431922a 0xf69fc71c73923f77 0x7ef69fc71c73923f

def z296 : W := mkw 0xa81b6906fd93ba2e 0x82a81b6906fd93ba 0xf81ff807ff93ffdd 0xfff81ff807ff93ff

def z297 : W := mkw 0x5794c7b533f26e6d 0x815794c7b533f26e 0x3791c7fc73f23f77 0x7a3791c7fc73f23f

def z298 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xf9eff8f800000019 0x86f9eff8f8000000

def z299 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xcfee3ff80000002a 0x84cfee3ff8000000

def z300 : W := mkw 0xbae0186a6d3cd531 0x48bae0186a6d3cd5 0x39e038f87c7fffff 0xb839e038f87c7fff

def z301 : W := mkw 0xed4b2803ce499052 0x0aed4b2803ce4990 0xc96e38038c6dc088 0x85c96e38038c6dc0

def z302 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080001800000037 0x2000800018000000

def z303 : W := mkw 0xffffbffd86e7ddc9 0x45ffffbffd86e7dd 0xffffffff8fffffff 0xffffffffff8fffff

def z304 : W := mkw 0xed4000034a480050 0x08ed4000034a4800 0xcf6000078fec00c2 0xe9cf6000078fec00

def z305 : W := mkw 0x000968001400b006 0x02000968001400b0 0x0001f80000003010 0x020001f800000030

def z306 : W := mkw 0x45261ce98665d541 0x4145261ce98665d5 0xc96e38e38c6dc088 0x85c96e38e38c6dc0

def z307 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0x3fe000007ffc0003 0x183fe000007ffc00

def z308 : W := mkw 0x0012092586e7dd49 0x410012092586e7dd 0x000000078fffffc0 0x19000000078fffff

def z309 : W := mkw 0xbac0000269180030 0x08bac00002691800 0xf8e00007fc1c00c1 0xf1f8e00007fc1c00

def z310 : W := mkw 0x0020184804049100 0x4000201848040491 0x08e038180c1e3f77 0x3808e038180c1e3f

def z311 : W := mkw 0xffdf6da7fffbfc7f 0x0bffdf6da7fffbfc 0xffffffe7fffffcff 0xffffffffe7fffffc

def z312 : W := mkw 0xa80928024c009002 0x02a80928024c0090 0x080038000c000000 0x00080038000c0000

def z313 : W := mkw 0xffedb6f800244581 0x44ffedb6f8002445 0xfffffff8007c0f3f 0xeefffffff8007c0f

def z314 : W := mkw 0x57c0000123580070 0x0857c00001235800 0x0fe000000ffc00c3 0xb80fe000000ffc00

def z315 : W := mkw 0x0012080484039008 0x0000120804840390 0xc81e38078c03f0dd 0xf5c81e38078c03f0

def z316 : W := mkw 0xa829304800000000 0x00a8293048000000 0xf9fff8f80000003f 0xe6f9fff8f8000000

def z317 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080001800103311 0x1000800018001033

def z318 : W := mkw 0xfffffefedc27f58f 0x46fffffefedc27f5 0xfffffffffc7fffff 0xfffffffffffc7fff

def z319 : W := mkw 0x1280821000000000 0x0012808210000000 0x3081c01800000011 0x023081c018000000

def z320 : W := mkw 0x5784869000000000 0x0057848690000000 0xf79fc7f80000003f 0xe6f79fc7f8000000

def z321 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038e00c7dc0cb 0xb809e038e00c7dc0

def z322 : W := mkw 0x00124006d803200e 0x0200124006d80320 0x00000007f0000000 0x0100000007f00000

def z323 : W := mkw 0xffe0104b6b580070 0x08ffe0104b6b5800 0xffe038fffffc00ff 0xf9ffe038fffffc00

def z324 : W := mkw 0x001240049003200c 0x0000124004900320 0xf01fc007f003f0dd 0xf7f01fc007f003f0

def z325 : W := mkw 0x0000002000204401 0x0000000020002044 0x09e000e00c7fccef 0xb809e000e00c7fcc

def z326 : W := mkw 0x001605a582e34c49 0x01001605a582e34c 0x001e07e783e3ccec 0x0d001e07e783e3cc

def z327 : W := mkw 0x1280831021900a20 0x801280831021900a 0x0600070003800000 0x0006000700038000

def z328 : W := mkw 0xffcda69000000080 0x04ffcda690000000 0xfe1fff000000001d 0xe6fe1fff00000000

def z329 : W := mkw 0xa80008024c009000 0x00a80008024c0090 0xf8003807fc03f0dd 0xf1f8003807fc03f0

def z330 : W := mkw 0xed0000034a400040 0x00ed0000034a4000 0xff000007ffe000c3 0xf9ff000007ffe000

def z331 : W := mkw 0x12a0937821b44f21 0xc012a0937821b44f 0x07e007f803fc0f22 0x0807e007f803fc0f

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x096000000c6c0080 0x80096000000c6c00

def z333 : W := mkw 0xffc404836b580070 0x08ffc404836b5800 0xfffe07e7fffc00ef 0xfdfffe07e7fffc00

def z334 : W := mkw 0x002018680424d501 0x40002018680424d5 0x000038f80c7ffffc 0x18000038f80c7fff

def z335 : W := mkw 0xba80000269100020 0x00ba800002691000 0xfe800007ff9000c3 0xf9fe800007ff9000

def z336 : W := mkw 0x128000036b580070 0x08128000036b5800 0x36800007fffc00c3 0x7936800007fffc00

def z337 : W := mkw 0x0032196d86e7dd49 0x410032196d86e7dd 0x09e038ff8fffffff 0xb909e038ff8fffff

def z338 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80c7dcfaa 0x8809e038f80c7dcf

def z339 : W := mkw 0x1292cb16fd93ba2e 0x821292cb16fd93ba 0x3691c71fff93fff7 0x7b3691c71fff93ff

def z340 : W := mkw 0x0020106800244501 0x4000201068002445 0x016000e0006c0000 0x00016000e0006c00

def z341 : W := mkw 0x0000000000000000 0x0000000000000000 0x0610070000000026 0x6006100700000000

def z342 : W := mkw 0x5780000123500060 0x0057800001235000 0xf7800007f3f000c3 0xf9f7800007f3f000

def z343 : W := mkw 0xfffdf6dc1002208c 0x04fffdf6dc100220 0xfffffffc7002307f 0xf6fffffffc700230

def z344 : W := mkw 0xffd0c31431922a2c 0x80ffd0c31431922a 0xfff1c71c73923f77 0xfafff1c71c73923f

def z345 : W := mkw 0x57e497f902e04cc1 0x0557e497f902e04c 0x07e007f803e00c22 0x0807e007f803e00c

def z346 : W := mkw 0xffc0000000000000 0x00ffc00000000000 0xffe0000000000003 0xe0ffe00000000000

def z347 : W := mkw 0x451605a480a34c09 0x01451605a480a34c 0xc71e07e00003cc2e 0xe4c71e07e00003cc

def z348 : W := mkw 0x57e01069237c4571 0x4857e01069237c45 0x07e000f803fc0f22 0x0807e000f803fc0f

def z349 : W := mkw 0xed1f6587dac3284e 0x03ed1f6587dac328 0xf61fc707f3800000 0x47f61fc707f38000

def z350 : W := mkw 0xfff0db7f7ffeff7d 0xc8fff0db7f7ffeff 0xfff1ffffffffffff 0xfbfff1ffffffffff

def z351 : W := mkw 0xfffb786fff7ff57f 0x4afffb786fff7ff5 0xfffff8ffffffffff 0xfffffff8ffffffff

def z352 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xf61ffff80000003c 0x46f61ffff8000000

def z353 : W := mkw 0x001beb149483ba0e 0x82001beb149483ba 0x001fff180003ff3c 0x06001fff180003ff

def z354 : W := mkw 0x002d34c800000080 0x04002d34c8000000 0x000e38e000000008 0x04000e38e0000000

def z355 : W := mkw 0xed6d3ce80424d581 0x44ed6d3ce80424d5 0xc9ee38f80c7fffff 0xbcc9ee38f80c7fff

def z356 : W := mkw 0xffc0000102400040 0x00ffc00001024000 0xffe0000783e000c3 0xe9ffe0000783e000

def z357 : W := mkw 0x12b0db5c3596bb2c 0xc012b0db5c3596bb 0x3ef1ff1c7f9e3f77 0x7a3ef1ff1c7f9e3f

def z358 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e00c22 0x4dc71e07e783e00c

def z359 : W := mkw 0x1280000021100020 0x0012800000211000 0x3680001c73923f77 0x783680001c73923f

def z360 : W := mkw 0x4540000102480050 0x0845400001024800 0x01600000006c0000 0x0001600000006c00

def z361 : W := mkw 0x002496d800000080 0x04002496d8000000 0x000007f800000020 0x00000007f8000000

def z362 : W := mkw 0x450404a000204401 0x00450404a0002044 0xc71e07e00063ccee 0xecc71e07e00063cc

def z363 : W := mkw 0x57c405a123f84c71 0x0957c405a123f84c 0x07e007e003fc0c22 0x0807e007e003fc0c

def z364 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80003ff3f 0xa009e038f80003ff

def z365 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3611c70473823055 0x723611c704738230

def z366 : W := mkw 0x0000010000800800 0x0000000100008008 0x0600070003800c22 0x080600070003800c

def z367 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z368 : W := mkw 0xbac0000269180030 0x08bac00002691800 0x39e000007c7c00c3 0xb839e000007c7c00

def z369 : W := mkw 0xffdfa7b582e34cc9 0x05ffdfa7b582e34c 0xf71fc7e783e3ccee 0xeff71fc7e783e3cc

def z370 : W := mkw 0x0020184804049100 0x4000201848040491 0x09e038f80c1c333f 0xb009e038f80c1c33

def z371 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x0691c71803923f36 0x0a0691c71803923f

def z372 : W := mkw 0xa80968025c00b006 0x02a80968025c00b0 0x3801f8007c003011 0x123801f8007c0030

def z373 : W := mkw 0xed6f3ccacc019082 0x06ed6f3ccacc0190 0xc96e38e38c01c088 0x85c96e38e38c01c0

def z374 : W := mkw 0x0012000480030008 0x0000120004800300 0xc01e000780000000 0x45c01e0007800000

def z375 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0x070007e783e3cce2 0x09070007e783e3cc

def z376 : W := mkw 0x1290cb143592ba2c 0x801290cb143592ba 0x3e91ff1c7f93ffff 0xfa3e91ff1c7f93ff

def z377 : W := mkw 0x579605a5a3f34c69 0x01579605a5a3f34c 0xf79e07e7f3f3ccef 0xfdf79e07e7f3f3cc

def z378 : W := mkw 0xffed34cb6b5800f0 0x0cffed34cb6b5800 0xffee38e7fffc00cb 0xfdffee38e7fffc00

def z379 : W := mkw 0x57edb6d800000080 0x0457edb6d8000000 0x07fffff80000003e 0x0607fffff8000000

def z380 : W := mkw 0x451605a7ebfb4c79 0x09451605a7ebfb4c 0xc71e07e7ffffccee 0xfdc71e07e7ffffcc

def z381 : W := mkw 0x1280c21031102224 0x801280c210311022 0x3001c00070000000 0x023001c000700000

def z382 : W := mkw 0x4500000102400040 0x0045000001024000 0xc600000783800000 0x41c6000007838000

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000470000041 0x7030000004700000

def z384 : W := mkw 0x002018680424d501 0x40002018680424d5 0x080038f80c03fffd 0xb0080038f80c03ff

def z385 : W := mkw 0xa81968065c02b00e 0x02a81968065c02b0 0x3811f8047c023055 0x723811f8047c0230

def z386 : W := mkw 0x0032186c8427d509 0x400032186c8427d5 0xc9fe38ff8c7fffff 0xfdc9fe38ff8c7fff

def z387 : W := mkw 0x0030db7c14a6ff0d 0xc00030db7c14a6ff 0x0011fff80003ff3c 0x020011fff80003ff

def z388 : W := mkw 0xa81b6006d803200e 0x02a81b6006d80320 0xf81fc007fc0000c1 0xf7f81fc007fc0000

def z389 : W := mkw 0x579687b5a3f34e69 0x81579687b5a3f34e 0xc79e07ff83f3cfee 0xedc79e07ff83f3cf

def z390 : W := mkw 0xa80968025c00b006 0x02a80968025c00b0 0x3801f8007c03f0dd 0xb23801f8007c03f0

def z391 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc79e07ff83f3ffff 0xfdc79e07ff83f3ff

def z392 : W := mkw 0xa83b786edc27f50f 0x42a83b786edc27f5 0xf97ff8e7fc6ff0dd 0xf7f97ff8e7fc6ff0

def z393 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xfee00007ff9c0001 0x51fee00007ff9c00

def z394 : W := mkw 0x001b60049003200e 0x02001b6004900320 0x001fc00000000000 0x06001fc000000000

def z395 : W := mkw 0xa869304800000080 0x04a8693048000000 0x0860380000000000 0x0008603800000000

def z396 : W := mkw 0x003fb7fc80a34c89 0x05003fb7fc80a34c 0x001ffff80003cc3c 0x06001ffff80003cc

def z397 : W := mkw 0xed1f6d87dec3b84e 0x03ed1f6d87dec3b8 0xfe1fff07ff83f0dd 0xf7fe1fff07ff83f0

def z398 : W := mkw 0xa80968025c00b006 0x02a80968025c00b0 0xf81ff8007c00301d 0xf6f81ff8007c0030

def z399 : W := mkw 0x0020184804049100 0x4000201848040491 0x086038000c0c0000 0x00086038000c0c00

def z400 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xf7ffc7f800000022 0x46f7ffc7f8000000

def z401 : W := mkw 0x0010410431922a2c 0x800010410431922a 0x0610070473923f66 0x780610070473923f

def z402 : W := mkw 0xfffffedfff5bb0fe 0x0efffffedfff5bb0 0xfffffffffffff0ff 0xfffffffffffffff0

def z403 : W := mkw 0x0000012102e04c41 0x010000012102e04c 0x0000000003e00c00 0x080000000003e00c

def z404 : W := mkw 0xa809200000000000 0x00a8092000000000 0x3801f80000000011 0x023801f800000000

def z405 : W := mkw 0xa83b784edc07b10e 0x42a83b784edc07b1 0xf8fff81ffc1ff3dd 0xf7f8fff81ffc1ff3

def z406 : W := mkw 0x45261ce98665d541 0x4145261ce98665d5 0xc9ee38fb8c7fffff 0xbdc9ee38fb8c7fff

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000020c66 0x280000000000020c

def z408 : W := mkw 0x450405a102e04c41 0x01450405a102e04c 0x070007e003e3ccee 0xa8070007e003e3cc

def z409 : W := mkw 0xed6d34c800000080 0x04ed6d34c8000000 0xc9ee38f80000003f 0xa4c9ee38f8000000

def z410 : W := mkw 0x001605a480a34c09 0x01001605a480a34c 0xc01e07e78003ccec 0xe5c01e07e78003cc

def z411 : W := mkw 0x4506048182410040 0x0145060481824100 0xc00e000380000000 0x05c00e0003800000

def z412 : W := mkw 0x453615ed82e74d49 0x41453615ed82e74d 0xc7fe07ff83ffcfee 0xedc7fe07ff83ffcf

def z413 : W := mkw 0x0000010021900a20 0x800000010021900a 0x0000000003900f00 0x080000000003900f

def z414 : W := mkw 0xffc000034a480050 0x08ffc000034a4800 0xffe000038c6c0083 0xe1ffe000038c6c00

def z415 : W := mkw 0x001605a480a34c09 0x01001605a480a34c 0x061e07e40383cc6e 0x6c061e07e40383cc

def z416 : W := mkw 0x450000036b580070 0x08450000036b5800 0xc7000007fffc00c2 0xf9c7000007fffc00

def z417 : W := mkw 0xed4604a3ca694451 0x09ed4604a3ca6944 0xc96e00e38c6dc088 0x85c96e00e38c6dc0

def z418 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000000c0000c1 0xb0080000000c0000

def z419 : W := mkw 0x000000034a480050 0x08000000034a4800 0x000000038c6c0080 0x01000000038c6c00

def z420 : W := mkw 0xa81b6927dee3fc4f 0x03a81b6927dee3fc 0xf81ff807ffe3fcdd 0xfff81ff807ffe3fc

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000123f40 0x180000000000123f

def z422 : W := mkw 0x0002002182614441 0x0100020021826144 0x000000038061c080 0x01000000038061c0

def z423 : W := mkw 0xa800000248000000 0x00a8000002480000 0x380000007c000001 0x10380000007c0000

def z424 : W := mkw 0x000048025c00b006 0x02000048025c00b0 0x000000007c003000 0x10000000007c0030

def z425 : W := mkw 0xffd60587ebdb0878 0x09ffd60587ebdb08 0xf61e0707f3800000 0x45f61e0707f38000

def z426 : W := mkw 0x002018680424d501 0x40002018680424d5 0x08e038180c7fffd1 0x1808e038180c7fff

def z427 : W := mkw 0xffe0106b6b7c4571 0x48ffe0106b6b7c45 0xffe000fffffc0fe3 0xf9ffe000fffffc0f

def z428 : W := mkw 0x4504048000000000 0x0045040480000000 0xc10e00e000000008 0x84c10e00e0000000

def z429 : W := mkw 0x0000002000244501 0x4000000020002445 0x00000000007c0f00 0x0800000000007c0f

def z430 : W := mkw 0xa800000000000000 0x00a8000000000000 0xf800000000000001 0xe0f8000000000000

def z431 : W := mkw 0x4516058582c30848 0x014516058582c308 0xc71e070783e000c2 0xedc71e070783e000

def z432 : W := mkw 0xa809280004009000 0x00a8092800040090 0xf81ff8000c03f0dd 0xf6f81ff8000c03f0

def z433 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xc80e3807fc03f0c8 0x95c80e3807fc03f0

def z434 : W := mkw 0x0020106800244501 0x4000201068002445 0x01e000f8007fcfee 0xa801e000f8007fcf

def z435 : W := mkw 0x1280831021900a20 0x801280831021900a 0x3680071c73900f63 0x783680071c73900f

def z436 : W := mkw 0x001040041002200c 0x0000104004100220 0x3091c01c70123f77 0x7a3091c01c70123f

def z437 : W := mkw 0x0000831000800a00 0x800000831000800a 0x0000071800000f20 0x000000071800000f

def z438 : W := mkw 0xa840000248080010 0x08a8400002480800 0x086000000c0c0000 0x00086000000c0c00

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0x080038000000001d 0xa008003800000000

def z440 : W := mkw 0xffd20007eb5b0078 0x08ffd20007eb5b00 0xfffe0007ffffc0cf 0xfdfffe0007ffffc0

def z441 : W := mkw 0x0020106800244501 0x4000201068002445 0x000000f800000f20 0x00000000f800000f

def z442 : W := mkw 0xffd041077bda2a7c 0x88ffd041077bda2a 0xffe00007fffe3fc3 0xf9ffe00007fffe3f

def z443 : W := mkw 0x000da69000000080 0x04000da690000000 0x001fc70000000000 0x06001fc700000000

def z444 : W := mkw 0x57e496f800244581 0x4457e496f8002445 0x07e007f8007c0f22 0x0807e007f8007c0f

def z445 : W := mkw 0x0000080004009000 0x0000000800040090 0x09e038000c7ff0df 0xb809e038000c7ff0

def z446 : W := mkw 0xffcda69000000080 0x04ffcda690000000 0xf69fc71800000037 0x66f69fc718000000

def z447 : W := mkw 0x0010410431922a2c 0x800010410431922a 0x0000000473800000 0x0000000004738000

def z448 : W := mkw 0x4500002102604441 0x0045000021026044 0xc70000e783e3ccee 0xe9c70000e783e3cc

def z449 : W := mkw 0x12a018682534d521 0x4012a018682534d5 0x3fe038fc7fffffff 0xf83fe038fc7fffff

def z450 : W := mkw 0x002018680424d501 0x40002018680424d5 0x01e000f80c7fffe2 0x1801e000f80c7fff

def z451 : W := mkw 0x0000000000000000 0x0000000000000000 0xc01e00000000000c 0xe4c01e0000000000

def z452 : W := mkw 0xbadb6806fd1bb03e 0x0abadb6806fd1bb0 0xf8fff807fc1ff0dd 0xf7f8fff807fc1ff0

def z453 : W := mkw 0x1280000021100020 0x0012800000211000 0x3600000473800000 0x4036000004738000

def z454 : W := mkw 0xffd0c3177bda2a7c 0x88ffd0c3177bda2a 0xfff1c707fffc00c3 0xfbfff1c707fffc00

def z455 : W := mkw 0xffedbed804049180 0x44ffedbed8040491 0xfffffff80c1c333f 0xf6fffffff80c1c33

def z456 : W := mkw 0xed4000034a480050 0x08ed4000034a4800 0xf9600007fc6c00c1 0xf1f9600007fc6c00

def z457 : W := mkw 0x5796c7b5b3f36e6d 0x815796c7b5b3f36e 0xf71fc7e7f3e3ccee 0xeff71fc7e7f3e3cc

def z458 : W := mkw 0x00020802cc019002 0x0200020802cc0190 0x000000038c01c080 0x01000000038c01c0

def z459 : W := mkw 0x0000080004009000 0x0000000800040090 0x080038000c003011 0x10080038000c0030

def z460 : W := mkw 0x1280000000000000 0x0012800000000000 0x3680000000000003 0x6036800000000000

def z461 : W := mkw 0x001048041402b00c 0x00001048041402b0 0x3811f8047c03f0dd 0xf23811f8047c03f0

def z462 : W := mkw 0x0020184804009000 0x0000201848040090 0x09e038f80c03f0ff 0xb009e038f80c03f0

def z463 : W := mkw 0xffcda6936b5800f0 0x0cffcda6936b5800 0xf61fc707f3800000 0x47f61fc707f38000

def z464 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc01c088 0xc7f81ff807fc01c0

def z465 : W := mkw 0xffcb2803ef599072 0x0affcb2803ef5990 0xffee3807fffdc0cb 0xfdffee3807fffdc0

def z466 : W := mkw 0xbaf9f35c31922aac 0x84baf9f35c31922a 0x3ef1ff1c73923f77 0x7a3ef1ff1c73923f

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x010000e00000002e 0xa0010000e0000000

def z468 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80c6dc0bf 0xa009e038f80c6dc0

def z469 : W := mkw 0x12c0000021180030 0x0812c00000211800 0x00e00000001c0000 0x0000e00000001c00

def z470 : W := mkw 0x0000400010002004 0x0000004000100020 0x3001c00070003011 0x123001c000700030

def z471 : W := mkw 0x001f6da494a3fc0f 0x03001f6da494a3fc 0x001fffe00003fc3c 0x06001fffe00003fc

def z472 : W := mkw 0x003b786c9427f50f 0x42003b786c9427f5 0x001ff8f80003ff3c 0x06001ff8f80003ff

def z473 : W := mkw 0x579687b582e34c49 0x01579687b582e34c 0xf79fc7ff83e3ccff 0xeff79fc7ff83e3cc

def z474 : W := mkw 0x002018680424d501 0x40002018680424d5 0x01e038f8007fff3e 0x0801e038f8007fff

def z475 : W := mkw 0xed60186b4e6cd551 0x48ed60186b4e6cd5 0xc96038e38c6dc088 0x81c96038e38c6dc0

def z476 : W := mkw 0x000b280084019002 0x02000b2800840190 0x000e38000001c008 0x04000e38000001c0

def z477 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3091c71870123f35 0x123091c71870123f

def z478 : W := mkw 0x450604a182614441 0x01450604a1826144 0xc10e00e38063ccee 0xadc10e00e38063cc

def z479 : W := mkw 0x0010010400820808 0x0000100104008208 0x0690071c03923f77 0x780690071c03923f

def z480 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xfe000007ff8000c1 0xf1fe000007ff8000

def z481 : W := mkw 0xa81b2806cc03900a 0x02a81b2806cc0390 0xc81e38078c03c0cc 0xe5c81e38078c03c0

def z482 : W := mkw 0xed1b6807de43b04e 0x02ed1b6807de43b0 0xff1ff807ffe3f0df 0xffff1ff807ffe3f0

def z483 : W := mkw 0xed3f7defdee7fd4f 0x43ed3f7defdee7fd 0xffffffffffffffff 0xffffffffffffffff

def z484 : W := mkw 0xffc008036f589070 0x08ffc008036f5890 0xffe03807fffff0df 0xf9ffe03807fffff0

def z485 : W := mkw 0xffc920036b580070 0x08ffc920036b5800 0xfffff807fffc00df 0xfffffff807fffc00

def z486 : W := mkw 0xba9b6806fd13b02e 0x02ba9b6806fd13b0 0xfe9ff807ff93f0df 0xfffe9ff807ff93f0

def z487 : W := mkw 0xbae9f258311022a4 0x84bae9f258311022 0x38e1f81870103311 0x1238e1f818701033

def z488 : W := mkw 0x45160da586e3dc49 0x0145160da586e3dc 0xcf1e3fe78fe3fcff 0xfdcf1e3fe78fe3fc

def z489 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80c7df399 0x9009e038f80c7df3

def z490 : W := mkw 0xffefb6f9826144c1 0x05ffefb6f9826144 0xfffffffb8061c0bf 0xe7fffffffb8061c0

def z491 : W := mkw 0x453fb7fd82e34cc9 0x05453fb7fd82e34c 0xc71fffff83e3ccfe 0xefc71fffff83e3cc

def z492 : W := mkw 0x000008236f7cd571 0x48000008236f7cd5 0x00000007ffffffc0 0x1900000007ffffff

def z493 : W := mkw 0xed1f2da7cee3dc4b 0x03ed1f2da7cee3dc 0xcf1e3fe78fe3ccee 0xedcf1e3fe78fe3cc

def z494 : W := mkw 0x0000821000000000 0x0000008210000000 0x0011c71800000034 0x020011c718000000

def z495 : W := mkw 0xbafbfa5edc03b08e 0x06bafbfa5edc03b0 0xf8fff81ffc03f0dd 0xf7f8fff81ffc03f0

def z496 : W := mkw 0xa80b2802cc019002 0x02a80b2802cc0190 0xc80e38038c03f0dd 0xb5c80e38038c03f0

def z497 : W := mkw 0x0000002000204401 0x0000000020002044 0x018000f80073ffff 0xb8018000f80073ff

def z498 : W := mkw 0x0000000269180030 0x0800000002691800 0x000000007c1c0000 0x10000000007c1c00

def z499 : W := mkw 0xffdde79431922aac 0x84ffdde79431922a 0xf61fc70473800000 0x46f61fc704738000

def z500 : W := mkw 0x57c0000123580070 0x0857c00001235800 0xc7e0000783fc00c2 0xe9c7e0000783fc00

def z501 : W := mkw 0xbac0000000000000 0x00bac00000000000 0x38e0000000000001 0x0038e00000000000

def z502 : W := mkw 0xffc0821000000000 0x00ffc08210000000 0xfff1c71800000037 0xe2fff1c718000000

def z503 : W := mkw 0xa81b6807ff5bb07e 0x0aa81b6807ff5bb0 0xf81ff807fffff0dd 0xfff81ff807fffff0

def z504 : W := mkw 0x12bdf7dc31922aac 0x8412bdf7dc31922a 0x369ffffc73923f7f 0x7e369ffffc73923f

def z505 : W := mkw 0xa83ffededc03b08e 0x06a83ffededc03b0 0xf81ffffffc03f0fd 0xf7f81ffffffc03f0

def z506 : W := mkw 0xbac9a21000000080 0x04bac9a210000000 0x3001c00000000000 0x023001c000000000

def z507 : W := mkw 0x12b0db7c35b6ff2d 0xc012b0db7c35b6ff 0x3691fffc7393ff7f 0x7a3691fffc7393ff

def z508 : W := mkw 0xba9bea16fd13b22e 0x82ba9bea16fd13b2 0xf89ff81ffc13f3dd 0xf7f89ff81ffc13f3

def z509 : W := mkw 0x0002000080010000 0x0000020000800100 0xc00e00038001c088 0x85c00e00038001c0

def z510 : W := mkw 0x4500000102400040 0x0045000001024000 0xcfe000078ffc00c3 0xf9cfe000078ffc00

def z511 : W := mkw 0x001605a480a34c09 0x01001605a480a34c 0x011e07e00063ccee 0xac011e07e00063cc

def z512 : W := mkw 0x4500000102400040 0x0045000001024000 0xc100000380600080 0x81c1000003806000

def z513 : W := mkw 0xffefbedacc019082 0x06ffefbedacc0190 0xfffffffb8c01c0bf 0xe7fffffffb8c01c0

def z514 : W := mkw 0xed0f2ca3ce61d443 0x03ed0f2ca3ce61d4 0xc90e38e38c61c088 0x85c90e38e38c61c0

def z515 : W := mkw 0xa809600258002006 0x02a8096002580020 0x3001c00070000000 0x023001c000700000

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x01e00000007c0002 0x0801e00000007c00

def z517 : W := mkw 0xbad0c316799a2a3c 0x88bad0c316799a2a 0x3ef1c71c7f9e3f77 0x7a3ef1c71c7f9e3f

def z518 : W := mkw 0xffffb7ffebfb4cf9 0x0dffffb7ffebfb4c 0xffffffffffffccff 0xffffffffffffffcc

def z519 : W := mkw 0x57f697fd82e34cc9 0x0557f697fd82e34c 0xc7fe07ff83e3ccee 0xedc7fe07ff83e3cc

def z520 : W := mkw 0xffe0184b6f5c9170 0x48ffe0184b6f5c91 0xffe0381ffffc33d3 0xf9ffe0381ffffc33

def z521 : W := mkw 0xffd0c3177bda2a7c 0x88ffd0c3177bda2a 0xf691c71ff3923f77 0x7bf691c71ff3923f

def z522 : W := mkw 0x0010410431922a2c 0x800010410431922a 0x0080001c73923f77 0x380080001c73923f

def z523 : W := mkw 0x57e496d800000080 0x0457e496d8000000 0xc7fe07f80000002e 0xe4c7fe07f8000000

def z524 : W := mkw 0x452018690664d541 0x40452018690664d5 0xcfe038ff8fffffff 0xf9cfe038ff8fffff

def z525 : W := mkw 0xffc0000021100020 0x00ffc00000211000 0xffe0000473900043 0xf8ffe00004739000

def z526 : W := mkw 0x1280c21031102224 0x801280c210311022 0x3681c01c73903353 0x7a3681c01c739033

def z527 : W := mkw 0x0000002000204401 0x0000000020002044 0x000000000063ccc0 0x08000000000063cc

def z528 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfeffff1800000011 0x46feffff18000000

def z529 : W := mkw 0xa829784a5c04b106 0x42a829784a5c04b1 0x38e1f8187c1c3311 0x1238e1f8187c1c33

def z530 : W := mkw 0x001040041002200c 0x0000104004100220 0x3011c00470000000 0x423011c004700000

def z531 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000c7c00c0 0x18000000000c7c00

def z532 : W := mkw 0xa829786a5c24f507 0x42a829786a5c24f5 0x39e1f8f87c7fffff 0xba39e1f8f87c7fff

def z533 : W := mkw 0x1296c7b4b1b36e2d 0x811296c7b4b1b36e 0x369fc7fc7393ff7f 0x7e369fc7fc7393ff

def z534 : W := mkw 0xffffb7fc80a34c89 0x05ffffb7fc80a34c 0xfffffff80003cc3f 0xe6fffffff80003cc

def z535 : W := mkw 0xffdfe696d803208e 0x06ffdfe696d80320 0xf61fc707f0000000 0x47f61fc707f00000

def z536 : W := mkw 0x57d605a5a3fb4c79 0x0957d605a5a3fb4c 0xc7fe07e783ffccee 0xedc7fe07e783ffcc

def z537 : W := mkw 0xa81b6006d803200e 0x02a81b6006d80320 0xf81ff807f000001d 0xe7f81ff807f00000

def z538 : W := mkw 0xa81beb16dc83ba0e 0x82a81beb16dc83ba 0xf81fff1ffc03fffd 0xf7f81fff1ffc03ff

def z539 : W := mkw 0xfffdf7dc31922aac 0x84fffdf7dc31922a 0xfffffffc7380003f 0xe6fffffffc738000

def z540 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xf7e00007f3fc0002 0x49f7e00007f3fc00

def z541 : W := mkw 0x5794c79431922a2c 0x805794c79431922a 0xf79fc7fc73923f7f 0xfef79fc7fc73923f

def z542 : W := mkw 0x129beb14b593ba2e 0x82129beb14b593ba 0x369fff1c7393ff7f 0x7e369fff1c7393ff

def z543 : W := mkw 0xffe9b25800000080 0x04ffe9b258000000 0xffe1f81800000013 0xe2ffe1f818000000

def z544 : W := mkw 0xffd605a582e34c49 0x01ffd605a582e34c 0xfffe07e783e3ccef 0xedfffe07e783e3cc

def z545 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c73903311 0x523691c71c739033

def z546 : W := mkw 0xffc000236b784471 0x08ffc000236b7844 0xffe000e7ffffccef 0xf9ffe000e7ffffcc

def z547 : W := mkw 0xa809200000000000 0x00a8092000000000 0xf01fc00000000000 0x46f01fc000000000

def z548 : W := mkw 0x1280c21031102224 0x801280c210311022 0x3691c71870103337 0x723691c718701033

def z549 : W := mkw 0xba99e31431922a2c 0x80ba99e31431922a 0xfe9fff1c73923f7f 0xfefe9fff1c73923f

def z550 : W := mkw 0x0010c31431922a2c 0x800010c31431922a 0x0011c71c73923f74 0x1a0011c71c73923f

def z551 : W := mkw 0x0012002480234409 0x0000120024802344 0xc11e00e78063ccee 0xedc11e00e78063cc

def z552 : W := mkw 0x0000080004009000 0x0000000800040090 0x088038180c13ffff 0xb8088038180c13ff

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000023055 0x3000000000000230

def z554 : W := mkw 0xbac0000269180030 0x08bac00002691800 0x3ee000047f9c0043 0x783ee000047f9c00

def z555 : W := mkw 0xffe496d800000080 0x04ffe496d8000000 0xffe007f800000023 0xe0ffe007f8000000

def z556 : W := mkw 0x0000c21010002204 0x800000c210100022 0x0001c01800003310 0x020001c018000033

def z557 : W := mkw 0x57c0831123d80a70 0x8857c0831123d80a 0x07e0071803fc0f22 0x0807e0071803fc0f

def z558 : W := mkw 0x0000000000000000 0x0000000000000000 0x09e0000000000003 0xa009e00000000000

def z559 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3611c70473923f40 0x5a3611c70473923f

def z560 : W := mkw 0xa81b6826dc27f50f 0x42a81b6826dc27f5 0xf81ff807fc7fffdd 0xfff81ff807fc7fff

def z561 : W := mkw 0x002018680424d501 0x40002018680424d5 0x008038f80013ff7f 0x38008038f80013ff

def z562 : W := mkw 0xed40000000000000 0x00ed400000000000 0xc960000000000000 0x80c9600000000000

def z563 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c73900f22 0x4a3691c71c73900f

def z564 : W := mkw 0x00361dec84a7dd09 0x4100361dec84a7dd 0x09fe3ff80c7fffff 0xbc09fe3ff80c7fff

def z565 : W := mkw 0x0020184804049100 0x4000201848040491 0x0000381800003310 0x0000003818000033

def z566 : W := mkw 0xffc083136bd80a70 0x88ffc083136bd80a 0xffe0071ffffc0fe3 0xf9ffe0071ffffc0f

def z567 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc61e070783e3ccc0 0x4dc61e070783e3cc

def z568 : W := mkw 0xffd001076bda0878 0x08ffd001076bda08 0xfff00707fffe0ce7 0xf9fff00707fffe0c

def z569 : W := mkw 0x450404a102604441 0x01450404a1026044 0x010000e000600000 0x00010000e0006000

def z570 : W := mkw 0xba9bea16dc03b00e 0x02ba9bea16dc03b0 0xfe9fff1ffc03f0ff 0xf7fe9fff1ffc03f0

def z571 : W := mkw 0x45241de906e4dd41 0x4145241de906e4dd 0x0fe03ff80fffffff 0xb80fe03ff80fffff

def z572 : W := mkw 0x57b6dffdb7f7ff6d 0xc157b6dffdb7f7ff 0xffffffffffffffff 0xffffffffffffffff

def z573 : W := mkw 0x0010010400820808 0x0000100104008208 0x0610070403800000 0x4006100704038000

def z574 : W := mkw 0xa81b200480030008 0x00a81b2004800300 0xf81ff8078003c0dd 0xe7f81ff8078003c0

def z575 : W := mkw 0xfffffedc9403b08e 0x06fffffedc9403b0 0xfffffff80003f03f 0xe6fffffff80003f0

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000001800023f34 0x000000001800023f

def z577 : W := mkw 0xfffff7fdb3f36eed 0x85fffff7fdb3f36e 0xfffffffff3f3ffff 0xfffffffffff3f3ff

def z578 : W := mkw 0xffc0000269180030 0x08ffc00002691800 0xffe000007c1c0003 0xf0ffe000007c1c00

def z579 : W := mkw 0x57c0000000000000 0x0057c00000000000 0x07e0000000000002 0x0007e00000000000

def z580 : W := mkw 0x002018680424d501 0x40002018680424d5 0x096038e00c6fccee 0xa8096038e00c6fcc

def z581 : W := mkw 0x456414c800000080 0x04456414c8000000 0x016000e000000000 0x00016000e0000000

def z582 : W := mkw 0xff9fefb7fff3fe6f 0x83ff9fefb7fff3fe 0xff9ffffffff3ffff 0xffff9ffffffff3ff

def z583 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x0680071c73923f62 0x180680071c73923f

def z584 : W := mkw 0x0000002000204401 0x0000000020002044 0x010000e00061c088 0x80010000e00061c0

def z585 : W := mkw 0x1280821000000000 0x0012808210000000 0x3611c70000000000 0x423611c700000000

def z586 : W := mkw 0x451604a582634449 0x01451604a5826344 0xc11e00e78063c0cc 0xe5c11e00e78063c0

def z587 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xc81ff8038c03f09c 0x87c81ff8038c03f0

def z588 : W := mkw 0x0012012582e34c49 0x010012012582e34c 0x0610070783e3cce6 0x690610070783e3cc

def z589 : W := mkw 0x1290c31410822a0c 0x801290c31410822a 0x3691c71800023f37 0x623691c71800023f

def z590 : W := mkw 0xfffdfffc35b6ffad 0xc4fffdfffc35b6ff 0xfffffffc7fffffff 0xfefffffffc7fffff

def z591 : W := mkw 0xffedb7d821900aa0 0x84ffedb7d821900a 0xfffffff803900f3f 0xeefffffff803900f

def z592 : W := mkw 0xffedb6f800204481 0x04ffedb6f8002044 0xfffffff80063ccff 0xeefffffff80063cc

def z593 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0x071e07e003e3cc2e 0x0c071e07e003e3cc

def z594 : W := mkw 0xffffffdefd93baae 0x86ffffffdefd93ba 0xffffffffff93ffff 0xffffffffffff93ff

def z595 : W := mkw 0x002018680424d501 0x40002018680424d5 0x096038e00c7fffc8 0x98096038e00c7fff

def z596 : W := mkw 0xa8120006c8030008 0x00a8120006c80300 0xf81e0007fc03c0cd 0xf5f81e0007fc03c0

def z597 : W := mkw 0xbac000036b580070 0x08bac000036b5800 0x38e00007fffc00c1 0x1938e00007fffc00

def z598 : W := mkw 0xa809200248000000 0x00a8092002480000 0xf81ff807fc0000dd 0xf7f81ff807fc0000

def z599 : W := mkw 0x4516058582c30848 0x014516058582c308 0xc71e07e78380002e 0xe5c71e07e7838000

def z600 : W := mkw 0xa80b2802cc019002 0x02a80b2802cc0190 0xf81ff8038c01c09d 0xe7f81ff8038c01c0

def z601 : W := mkw 0x45164da7dee3fc4f 0x0345164da7dee3fc 0xc71e07e7ffe3fcee 0xfdc71e07e7ffe3fc

def z602 : W := mkw 0xa80b2802cc019002 0x02a80b2802cc0190 0xf80e3807fc01c0c9 0xf5f80e3807fc01c0

def z603 : W := mkw 0xffffb6dc80030088 0x04ffffb6dc800300 0xffffffff8003c0ff 0xe7ffffffff8003c0

def z604 : W := mkw 0x4500000000000000 0x0045000000000000 0xc700000000000002 0xe0c7000000000000

def z605 : W := mkw 0x12b0d37c31b66f2d 0xc012b0d37c31b66f 0x37f1c7fc73fe3f77 0x7a37f1c7fc73fe3f

def z606 : W := mkw 0x451645a5b3f36e6d 0x81451645a5b3f36e 0xc71e07e7f3f3ffee 0xfdc71e07e7f3f3ff

def z607 : W := mkw 0xba99eb167d92ba2e 0x82ba99eb167d92ba 0x3e91ff1c7f923f77 0x7a3e91ff1c7f923f

def z608 : W := mkw 0xa800000248000000 0x00a8000002480000 0xf0000007f0000000 0x41f0000007f00000

def z609 : W := mkw 0xffdbeb17ffdbba7e 0x8affdbeb17ffdbba 0xffffff1fffffffff 0xffffffff1fffffff

def z610 : W := mkw 0x1280821000000000 0x0012808210000000 0x0680071800000022 0x0006800718000000

def z611 : W := mkw 0xed5b6807de4bb05e 0x0aed5b6807de4bb0 0xf97ff807fc6ff0dd 0xf7f97ff807fc6ff0

def z612 : W := mkw 0x1292c335b3f36e6d 0x811292c335b3f36e 0x3691c71ff3f3fff7 0x7b3691c71ff3f3ff

def z613 : W := mkw 0x002dbef80424d581 0x44002dbef80424d5 0x001ffff80003ff3c 0x06001ffff80003ff

def z614 : W := mkw 0x0010000400020008 0x0000100004000200 0x0010000400020044 0x6000100004000200

def z615 : W := mkw 0xbae9fa5a5c00b086 0x06bae9fa5a5c00b0 0x38e1f8187c003011 0x1238e1f8187c0030

def z616 : W := mkw 0x0020186b6f7cd571 0x480020186b6f7cd5 0x09e038ffffffffff 0xb909e038ffffffff

def z617 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0x3fe1fff800000033 0x023fe1fff8000000

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0x3011c00000000015 0x623011c000000000

def z619 : W := mkw 0x12a09a780424d501 0x4012a09a780424d5 0x3ff1fff80c7fffff 0xfa3ff1fff80c7fff

def z620 : W := mkw 0x1290c33431b26e2d 0x801290c33431b26e 0x3791c7fc73f3ffff 0xfa3791c7fc73f3ff

def z621 : W := mkw 0xbae9b25800000080 0x04bae9b258000000 0x3ef1ff1800000037 0x623ef1ff18000000

def z622 : W := mkw 0x001040041002200c 0x0000104004100220 0x0000000470023040 0x1000000004700230

def z623 : W := mkw 0x00124807ff5bb07e 0x0a00124807ff5bb0 0x00000007fffff0c0 0x1900000007fffff0

def z624 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xf6800007f3900043 0x79f6800007f39000

def z625 : W := mkw 0xa83b784edc03b00e 0x02a83b784edc03b0 0xf9fff8fffc03f0ff 0xf7f9fff8fffc03f0

def z626 : W := mkw 0xbae9b25800000080 0x04bae9b258000000 0xf8fff8180000001d 0xe6f8fff818000000

def z627 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xf7000007f3e000c2 0xe9f7000007f3e000

def z628 : W := mkw 0x0010c31410822a0c 0x800010c31410822a 0x0091c71800123f77 0x3a0091c71800123f

def z629 : W := mkw 0xba9be316f9932a2e 0x82ba9be316f9932a 0xf61fc707f3800000 0x47f61fc707f38000

def z630 : W := mkw 0x5796c795b3d32a6c 0x815796c795b3d32a 0xf69fc71ff3923f77 0x7ff69fc71ff3923f

def z631 : W := mkw 0xffdb6007fb5b207e 0x0affdb6007fb5b20 0xffffc007fffc00c3 0xffffffc007fffc00

def z632 : W := mkw 0x12e0925800000080 0x0412e09258000000 0x00e0001800000000 0x0000e00018000000

def z633 : W := mkw 0x57c0000123580070 0x0857c00001235800 0x0600000003800000 0x0006000000038000

def z634 : W := mkw 0x003df7dc10822a8c 0x84003df7dc10822a 0x001ffff800023f3c 0x06001ffff800023f

def z635 : W := mkw 0xffdfa79582c308c8 0x05ffdfa79582c308 0xf61fc70783800000 0x47f61fc707838000

def z636 : W := mkw 0x57d0c31533da2a7c 0x8857d0c31533da2a 0x37f1c71c73fe3f77 0x7a37f1c71c73fe3f

def z637 : W := mkw 0x001041077bda2a7c 0x88001041077bda2a 0x00000007fffe3fc0 0x1900000007fffe3f

def z638 : W := mkw 0x0030596c35b6ff2d 0xc00030596c35b6ff 0x09e038fc7fffffff 0xb809e038fc7fffff

def z639 : W := mkw 0x001041041082280c 0x0000104104108228 0x3611c70473823c77 0x7a3611c70473823c

def z640 : W := mkw 0x0010010400820808 0x0000100104008208 0x0000000403820c40 0x080000000403820c

def z641 : W := mkw 0x0020184804049100 0x4000201848040491 0x08e038180c1ff3dd 0xb008e038180c1ff3

def z642 : W := mkw 0xbae9ba780424d581 0x44bae9ba780424d5 0x39e1f8f80c7fffff 0xba39e1f8f80c7fff

def z643 : W := mkw 0x00124125b3f36e6d 0x8100124125b3f36e 0x00000007f3f3ffc0 0x1900000007f3f3ff

def z644 : W := mkw 0x000008200420d401 0x00000008200420d4 0x090038e00c63fcff 0xb8090038e00c63fc

def z645 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c70473900043 0x7a3691c704739000

def z646 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xf6000007fffc00c0 0x59f6000007fffc00

def z647 : W := mkw 0xffc0c2137b582274 0x88ffc0c2137b5822 0xffe1c01ffffc33d3 0xfbffe1c01ffffc33

def z648 : W := mkw 0x0000080004009000 0x0000000800040090 0x080038000c01c088 0x80080038000c01c0

def z649 : W := mkw 0xffd040077b5a207c 0x08ffd040077b5a20 0xfff1c007fffe30d7 0xfbfff1c007fffe30

def z650 : W := mkw 0xed60186b4e6cd551 0x48ed60186b4e6cd5 0xc9e038fb8c7fffff 0xb9c9e038fb8c7fff

def z651 : W := mkw 0x1290010421920828 0x0012900104219208 0x3690070473920c67 0x783690070473920c

def z652 : W := mkw 0xffc0000123580070 0x08ffc00001235800 0xffe0000003fc0003 0xe8ffe0000003fc00

def z653 : W := mkw 0x000008200424d501 0x40000008200424d5 0x000000000003ff00 0x00000000000003ff

def z654 : W := mkw 0x1290c2141002200c 0x001290c214100220 0x3691c71c70023077 0x723691c71c700230

def z655 : W := mkw 0x002018680424d501 0x40002018680424d5 0x000038e00001c008 0x00000038e00001c0

def z656 : W := mkw 0x1280821000000000 0x0012808210000000 0x3691c71800123f77 0x7a3691c71800123f

def z657 : W := mkw 0xa800000248000000 0x00a8000002480000 0xc80000038c000080 0x81c80000038c0000

def z658 : W := mkw 0xffcda69000000080 0x04ffcda690000000 0xf71fc7e00000002e 0xe6f71fc7e0000000

def z659 : W := mkw 0x0020104800000000 0x0000201048000000 0x08e0381800000011 0x0008e03818000000

def z660 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xf9e00003fc7c0081 0x91f9e00003fc7c00

def z661 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xcfe000038ffc0082 0x89cfe000038ffc00

def z662 : W := mkw 0x1290c3177bda2a7c 0x881290c3177bda2a 0x3691c71ffffe3ff7 0x7b3691c71ffffe3f

def z663 : W := mkw 0x12a0da583514b324 0xc012a0da583514b3 0x38e1f8187c1c3311 0x1238e1f8187c1c33

def z664 : W := mkw 0xffc0000000000000 0x00ffc00000000000 0xf600000000000000 0x40f6000000000000

def z665 : W := mkw 0x0012000480030008 0x0000120004800300 0x000000078003c0c0 0x01000000078003c0

def z666 : W := mkw 0xffedbef80424d581 0x44ffedbef80424d5 0xfffffff80c6dc0bf 0xe6fffffff80c6dc0

def z667 : W := mkw 0xffe0104800000000 0x00ffe01048000000 0xffe038f80000003f 0xe0ffe038f8000000

def z668 : W := mkw 0xfffdf7dc10822a8c 0x84fffdf7dc10822a 0xfffffff800023f3f 0xe6fffffff800023f

def z669 : W := mkw 0x57e496d9235800f0 0x0c57e496d9235800 0x07e007f803fc0022 0x0807e007f803fc00

def z670 : W := mkw 0x0000080004049100 0x4000000800040491 0x000000000c1c3300 0x10000000000c1c33

def z671 : W := mkw 0xffe496db6b5800f0 0x0cffe496db6b5800 0xffe007fffffc00e3 0xf9ffe007fffffc00

def z672 : W := mkw 0x578487b123f04e61 0x81578487b123f04e 0x078007f803f00f22 0x08078007f803f00f

def z673 : W := mkw 0x0012010480830808 0x0000120104808308 0xc61e07078383ccee 0xedc61e07078383cc

def z674 : W := mkw 0xed4000034a480050 0x08ed4000034a4800 0xc000000380000000 0x01c0000003800000

def z675 : W := mkw 0x000008200424d501 0x40000008200424d5 0x008000180c7ffff7 0x38008000180c7fff

def z676 : W := mkw 0x0000000021100020 0x0000000000211000 0x0000000473900040 0x1800000004739000

def z677 : W := mkw 0x57e01869277cd571 0x4857e01869277cd5 0x0fe038f80fffffff 0xb80fe038f80fffff

def z678 : W := mkw 0xba9beb16fd93ba2e 0x82ba9beb16fd93ba 0xfe1fff07ff83f0dd 0xf7fe1fff07ff83f0

def z679 : W := mkw 0x00124906fd93ba2e 0x8200124906fd93ba 0x00000007ff93ffc0 0x1900000007ff93ff

def z680 : W := mkw 0x0010410431922a2c 0x800010410431922a 0x3011c00473923f55 0x7a3011c00473923f

def z681 : W := mkw 0x0020184804049100 0x4000201848040491 0x09e038180c7c33d3 0xb809e038180c7c33

def z682 : W := mkw 0xffdb6807ff5bb07e 0x0affdb6807ff5bb0 0xfe1ff807ff83f0dd 0xf7fe1ff807ff83f0

def z683 : W := mkw 0xed7f7ccedc03b08e 0x06ed7f7ccedc03b0 0xf97ff8e7fc03f0dd 0xf7f97ff8e7fc03f0

def z684 : W := mkw 0x0020104800000000 0x0000201048000000 0x01e000f800000022 0x0001e000f8000000

def z685 : W := mkw 0x45241ce80424d501 0x4045241ce80424d5 0xcffe3ff80c7fffff 0xfccffe3ff80c7fff

def z686 : W := mkw 0x5796c795b3d32a6c 0x815796c795b3d32a 0xf61fc707f3800000 0x47f61fc707f38000

def z687 : W := mkw 0xbac0c21279182234 0x88bac0c212791822 0x38e1c0187c1c3311 0x1238e1c0187c1c33

def z688 : W := mkw 0xa82b386acc25d503 0x42a82b386acc25d5 0xc96e38e38c6dc088 0x85c96e38e38c6dc0

def z689 : W := mkw 0xfff61defefffdd79 0x49fff61defefffdd 0xfffe3fffffffffff 0xfdfffe3fffffffff

def z690 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0x3801f807fc03f0d1 0x133801f807fc03f0

def z691 : W := mkw 0x00124826dc27f50f 0x4200124826dc27f5 0x00000007fc7fffc0 0x1900000007fc7fff

def z692 : W := mkw 0x1280000021100020 0x0012800000211000 0x0680000003900002 0x0806800000039000

def z693 : W := mkw 0xffedb7f902e04cc1 0x05ffedb7f902e04c 0xfffffff803e00c3f 0xeefffffff803e00c

def z694 : W := mkw 0x003b786c9427f50f 0x42003b786c9427f5 0x09fff8f80c7fffff 0xbe09fff8f80c7fff

def z695 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc003011 0x57f81ff807fc0030

def z696 : W := mkw 0x0012010582c30848 0x010012010582c308 0x0000000783800000 0x0100000007838000

def z697 : W := mkw 0x4516c7b592e36e4d 0x814516c7b592e36e 0xc71fc7ff83e3fffe 0xefc71fc7ff83e3ff

def z698 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc10e00e783e3ccc8 0x8dc10e00e783e3cc

def z699 : W := mkw 0x001040041002200c 0x0000104004100220 0x0011c00000023014 0x020011c000000230

def z700 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc11e07e38063ccac 0x85c11e07e38063cc

def z701 : W := mkw 0xffffffffdee3fccf 0x07ffffffffdee3fc 0xffffffffffe3fcff 0xffffffffffffe3fc

def z702 : W := mkw 0x1290831421920a28 0x801290831421920a 0x0690071c03920f66 0x680690071c03920f

def z703 : W := mkw 0xa81f6da6dca3fc0f 0x03a81f6da6dca3fc 0xf81fffe7fc03fcfd 0xf7f81fffe7fc03fc

def z704 : W := mkw 0x45361ded86e7dd49 0x4145361ded86e7dd 0xc71e3fff83e3fffe 0xedc71e3fff83e3ff

def z705 : W := mkw 0xba89a21000000000 0x00ba89a210000000 0xfe9fff180000003f 0xe6fe9fff18000000

def z706 : W := mkw 0x12a09b7825b4df21 0xc012a09b7825b4df 0x0fe03ff80fffffff 0xb80fe03ff80fffff

def z707 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xf71ffff80000003e 0xe6f71ffff8000000

def z708 : W := mkw 0xffedb6db4a4000c0 0x04ffedb6db4a4000 0xffffffffffe000ff 0xffffffffffffe000

def z709 : W := mkw 0xed4000036b580070 0x08ed4000036b5800 0xc9e00007fffc00c3 0xb9c9e00007fffc00

def z710 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xf9fffff80000003d 0x86f9fffff8000000

def z711 : W := mkw 0x0012012480a34c09 0x000012012480a34c 0xc71e07e783e3ccee 0xedc71e07e783e3cc

def z712 : W := mkw 0xba8bab12ed919a22 0x82ba8bab12ed919a 0xce8e3f1b8f91cfaa 0x8dce8e3f1b8f91cf

def z713 : W := mkw 0xffedb6db4a4800d0 0x0cffedb6db4a4800 0xfffffffffc6c00ff 0xf7fffffffffc6c00

def z714 : W := mkw 0xed0d24834a400040 0x00ed0d24834a4000 0xff1fffe7ffe000ff 0xffff1fffe7ffe000

def z715 : W := mkw 0xed6db6d800000080 0x04ed6db6d8000000 0xc97fffe000000008 0x86c97fffe0000000

def z716 : W := mkw 0x57edb6d800000080 0x0457edb6d8000000 0xc7fffff80000003e 0xe6c7fffff8000000

def z717 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x301ffff80000003d 0x66301ffff8000000

def z718 : W := mkw 0xffd24927fffbfc7f 0x0bffd24927fffbfc 0xffe00007fffffcc3 0xf9ffe00007fffffc

def z719 : W := mkw 0xbafbb37d82e34cc9 0x05bafbb37d82e34c 0x38e1f81f83e3ccd1 0x0b38e1f81f83e3cc

def z720 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3e91c71c7f923ff7 0xfa3e91c71c7f923f

def z721 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80c7fffbe 0x8809e038f80c7fff

def z722 : W := mkw 0x45361dcd86c79948 0x4145361dcd86c799 0xcefe3f1f8f9c3311 0x55cefe3f1f8f9c33

def z723 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xffffffffff8000ff 0xf7ffffffffff8000

def z724 : W := mkw 0x57edb6d800000080 0x0457edb6d8000000 0x061ffff80000003c 0x06061ffff8000000

def z725 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc61e07e783e3ccec 0x4dc61e07e783e3cc

def z726 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c73923f51 0x5a3691c71c73923f

def z727 : W := mkw 0x450605a182e14c41 0x01450605a182e14c 0xc70e07e383e1c088 0x85c70e07e383e1c0

def z728 : W := mkw 0xbad605a6e9bb4c39 0x09bad605a6e9bb4c 0x38fe07e07c1fcc2d 0x1438fe07e07c1fcc

def z729 : W := mkw 0x001248049403b00c 0x00001248049403b0 0xf81ff807fc03f0dd 0xf7f81ff807fc03f0

def z730 : W := mkw 0xed50c3175aca2a5c 0x88ed50c3175aca2a 0xc971c71b8c6e3fb4 0x83c971c71b8c6e3f

def z731 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x001ffff800023f3c 0x06001ffff800023f

def z732 : W := mkw 0x002018680424d501 0x40002018680424d5 0x0ff03ff80c7fffff 0xf80ff03ff80c7fff

def z733 : W := mkw 0xa84000036b580070 0x08a84000036b5800 0x08600007fffc00c0 0x1908600007fffc00

def z734 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe00007fffe3fc3 0xf9ffe00007fffe3f

def z735 : W := mkw 0x00124927fffbfc7f 0x0b00124927fffbfc 0x00000007fffffcc0 0x1900000007fffffc

def z736 : W := mkw 0x57edb6d9235800f0 0x0c57edb6d9235800 0x07fffff803fc003e 0x0e07fffff803fc00

def z737 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc03f01d 0x57f81ff807fc03f0

def z738 : W := mkw 0xffc404836b580070 0x08ffc404836b5800 0xffee00e7fffc00cb 0xfdffee00e7fffc00

def z739 : W := mkw 0x12b0db7c35b6ff2d 0xc012b0db7c35b6ff 0x3f71ffe47fedc088 0xc23f71ffe47fedc0

def z740 : W := mkw 0x451645a592e36c4d 0x01451645a592e36c 0xf79fc7fff3f3ffff 0xfff79fc7fff3f3ff

def z741 : W := mkw 0x452db6d800000080 0x04452db6d8000000 0x071ffff80000003e 0x06071ffff8000000

def z742 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e78fffccee 0xfdc71e07e78fffcc

def z743 : W := mkw 0x57f6dededc03b08e 0x0657f6dededc03b0 0x07e007fffc03f0e2 0x1107e007fffc03f0

def z744 : W := mkw 0x1280821021100020 0x0012808210211000 0x3691c71c73923f77 0x7a3691c71c73923f

def z745 : W := mkw 0xffc082136b580070 0x08ffc082136b5800 0xfff1c707fffc00c3 0xfbfff1c707fffc00

def z746 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xfe1fff07fc03f0ff 0xf7fe1fff07fc03f0

def z747 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807f003f01d 0xe7f81ff807f003f0

def z748 : W := mkw 0xbae9fa5a7d18b0b6 0x0ebae9fa5a7d18b0 0x38e1f8187c1c3011 0x1238e1f8187c1c30

def z749 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe00007fffc0081 0xd1ffe00007fffc00

def z750 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xffffffffffec00bf 0xe7ffffffffffec00

def z751 : W := mkw 0xffedb6da48000080 0x04ffedb6da480000 0xfffffffff000003f 0xe7fffffffff00000

def z752 : W := mkw 0xa81b6906dc83b80e 0x02a81b6906dc83b8 0xf81ff807ff83fcdd 0xfff81ff807ff83fc

def z753 : W := mkw 0x002018680424d501 0x40002018680424d5 0xc9e038ff8c7fffff 0xf9c9e038ff8c7fff

def z754 : W := mkw 0x452db6d9024000c0 0x04452db6d9024000 0xc71fffff83e000fe 0xefc71fffff83e000

def z755 : W := mkw 0xbac000036b580070 0x08bac000036b5800 0x39e00007fffc00c3 0xb939e00007fffc00

def z756 : W := mkw 0xffe0186b6f7cd571 0x48ffe0186b6f7cd5 0xf60038fff383ff3c 0x41f60038fff383ff

def z757 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80c7fffd9 0x9809e038f80c7fff

def z758 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe0001ffffc0fe3 0xf9ffe0001ffffc0f

def z759 : W := mkw 0xffedb6d9024000c0 0x04ffedb6d9024000 0xfffffffb806000bf 0xe7fffffffb806000

def z760 : W := mkw 0x002018680424d501 0x40002018680424d5 0x39e038fc7c7fffff 0xf839e038fc7c7fff

def z761 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3cce2 0x4dc71e07e783e3cc

def z762 : W := mkw 0xffedb6d9024800d0 0x0cffedb6d9024800 0xfffffff8006c003f 0xe6fffffff8006c00

def z763 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf89ff81ffc13f3dd 0xf7f89ff81ffc13f3

def z764 : W := mkw 0xffc486936b5800f0 0x0cffc486936b5800 0xffe00707fffc00c3 0xf9ffe00707fffc00

def z765 : W := mkw 0xffcdaeb00424d581 0x44ffcdaeb00424d5 0xf61fc7000c7fffc0 0x5ef61fc7000c7fff

def z766 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xf7e00007fffc00c2 0x59f7e00007fffc00

def z767 : W := mkw 0x002018680424d501 0x40002018680424d5 0x0fe038fc0fffffff 0xf80fe038fc0fffff

def z768 : W := mkw 0xffedb6d9024000c0 0x04ffedb6d9024000 0xffffffff8380003f 0xe7ffffffff838000

def z769 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcf1e3fe783e3ccff 0xedcf1e3fe783e3cc

def z770 : W := mkw 0xffedb6d9235800f0 0x0cffedb6d9235800 0xfffffff80380003f 0xe6fffffff8038000

def z771 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc03f0c8 0xd7f81ff807fc03f0

def z772 : W := mkw 0xffc082136b580270 0x88ffc082136b5802 0xffe0001ffffc03c3 0xf9ffe0001ffffc03

def z773 : W := mkw 0x12adb6d8211000a0 0x0412adb6d8211000 0x369ffffc7390007f 0x7e369ffffc739000

def z774 : W := mkw 0xa83b706ed827650f 0x42a83b706ed82765 0xf1ffc0fff07c0f22 0x4ff1ffc0fff07c0f

def z775 : W := mkw 0xed7d75cc31922aac 0x84ed7d75cc31922a 0xc96e38e473923f48 0x9cc96e38e473923f

def z776 : W := mkw 0x001041041082280c 0x0000104104108228 0x3691c71c73923f77 0x7a3691c71c73923f

def z777 : W := mkw 0x128000036b580070 0x08128000036b5800 0x3fe00007fffc00c3 0xf93fe00007fffc00

def z778 : W := mkw 0x57c000036b580070 0x0857c000036b5800 0x0fe00007fffc00c3 0xb90fe00007fffc00

def z779 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c73903f33 0x5a3691c71c73903f

def z780 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff80c1c003f 0xf6fffffff80c1c00

def z781 : W := mkw 0x57edb6d800000080 0x0457edb6d8000000 0x37fffff80000003f 0x6637fffff8000000

def z782 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcf1e07e78fe3ccef 0xfdcf1e07e78fe3cc

def z783 : W := mkw 0xffcda69000000080 0x04ffcda690000000 0xff1fffe00000003f 0xe6ff1fffe0000000

def z784 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffff3fc003f 0xeffffffffff3fc00

def z785 : W := mkw 0xed0d6da35ee0fc47 0x03ed0d6da35ee0fc 0x3f01ffe07fe03c33 0x1a3f01ffe07fe03c

def z786 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc79e07ff83f3cfee 0xedc79e07ff83f3cf

def z787 : W := mkw 0xffedb6d8211000a0 0x04ffedb6d8211000 0xfffffffc7ffc00ff 0xfefffffffc7ffc00

def z788 : W := mkw 0xed2d34c800000000 0x00ed2d34c8000000 0xfffffff80000003f 0xe6fffffff8000000

def z789 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x01fffff80000003e 0x0601fffff8000000

def z790 : W := mkw 0xa81b6006d803200e 0x02a81b6006d80320 0xf81ff807f003c0dd 0xe7f81ff807f003c0

def z791 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xff7fffe7ffec0088 0xc7ff7fffe7ffec00

def z792 : W := mkw 0x4516058582c30848 0x014516058582c308 0xc71e07e78383c0ee 0xe5c71e07e78383c0

def z793 : W := mkw 0x451645a592e36c4d 0x01451645a592e36c 0xc71e07e7f3e3fcee 0xfdc71e07e7f3e3fc

def z794 : W := mkw 0x455605a582eb4c59 0x09455605a582eb4c 0xc77e07e783efccee 0xedc77e07e783efcc

def z795 : W := mkw 0x5786c6b1b3716665 0x815786c6b1b37166 0xf18fc0fbf071f399 0x97f18fc0fbf071f3

def z796 : W := mkw 0xa82db6d800000080 0x04a82db6d8000000 0xf9fffff80000003f 0xe6f9fffff8000000

def z797 : W := mkw 0x1280c31031902a24 0x801280c31031902a 0x3681c71c73903f73 0x7a3681c71c73903f

def z798 : W := mkw 0x5780000123500060 0x0057800001235000 0xffe00007fffc00c3 0xf9ffe00007fffc00

def z799 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80c7fffbd 0x9009e038f80c7fff

def z800 : W := mkw 0x450605a182e14c41 0x01450605a182e14c 0xc70e07e783e1ccea 0xedc70e07e783e1cc

def z801 : W := mkw 0xffcda6936b5800f0 0x0cffcda6936b5800 0xffffc7e7fffc00ef 0xffffffc7e7fffc00

def z802 : W := mkw 0x452db6d800000080 0x04452db6d8000000 0xc61ffff80000003c 0x46c61ffff8000000

def z803 : W := mkw 0xffedb6da48000080 0x04ffedb6da480000 0xfffffffb8c0000bf 0xe7fffffffb8c0000

def z804 : W := mkw 0xed0000034a400040 0x00ed0000034a4000 0xffe00007fffc00c3 0xf9ffe00007fffc00

def z805 : W := mkw 0x450000036b580070 0x08450000036b5800 0xcfe00007fffc00c3 0xf9cfe00007fffc00

def z806 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe00007fffe30d7 0xf9ffe00007fffe30

def z807 : W := mkw 0x00124925b7f7ff6d 0xc100124925b7f7ff 0x00000007ffffffc0 0x1900000007ffffff

def z808 : W := mkw 0xa80928024c009000 0x00a80928024c0090 0xf81ff807fc03f0dd 0xf7f81ff807fc03f0

def z809 : W := mkw 0xa81b6906dc83ba0e 0x82a81b6906dc83ba 0xf81ff807fc03ffdd 0xf7f81ff807fc03ff

def z810 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e383e3ccae 0x8dc71e07e383e3cc

def z811 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xcffffff80000003e 0x86cffffff8000000

def z812 : W := mkw 0xa80b6802dc01b006 0x02a80b6802dc01b0 0xf81ff803fc01f09d 0xf7f81ff803fc01f0

def z813 : W := mkw 0xa82db6da48000080 0x04a82db6da480000 0xf81ffffffc0000fd 0xf7f81ffffffc0000

def z814 : W := mkw 0xa81b2006c8030008 0x00a81b2006c80300 0xf81ff807fc03c0dd 0xf7f81ff807fc03c0

def z815 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffffffe3fff 0xfffffffffffffe3f

def z816 : W := mkw 0xa80000036b580070 0x08a80000036b5800 0xf9e00007fffc00c3 0xf9f9e00007fffc00

def z817 : W := mkw 0xed2f3cebce65d543 0x43ed2f3cebce65d5 0xc96e38e38c6dc088 0x85c96e38e38c6dc0

def z818 : W := mkw 0x0036dffc94a7ff0d 0xc10036dffc94a7ff 0x001ffff80003ff3c 0x06001ffff80003ff

def z819 : W := mkw 0x0012492494a3fc0f 0x030012492494a3fc 0x000000000003fc00 0x00000000000003fc

def z820 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e78383cc2e 0xe5c71e07e78383cc

def z821 : W := mkw 0x57db6805b75bb07e 0x0a57db6805b75bb0 0x07fff80003fff01e 0x0e07fff80003fff0

def z822 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xff7ffff80000003c 0xc6ff7ffff8000000

def z823 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe0001ffffc00f7 0xf9ffe0001ffffc00

def z824 : W := mkw 0x00124927fff3fe6f 0x8300124927fff3fe 0x00000007fff3ffc0 0x1900000007fff3ff

def z825 : W := mkw 0xffedb6d8211000a0 0x04ffedb6d8211000 0xfffffff87010003f 0xf6fffffff8701000

def z826 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80c7fff3f 0x1809e038f80c7fff

def z827 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3fcff 0xfdc71e07e783e3fc

def z828 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe03807fffc00df 0xf9ffe03807fffc00

def z829 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0x3fe00007fffc00c3 0x193fe00007fffc00

def z830 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf91ff807fc63f0df 0xfff91ff807fc63f0

def z831 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff80002307f 0xf6fffffff8000230

def z832 : W := mkw 0xed4000036b580070 0x08ed4000036b5800 0xf9600007fffc00c1 0xf9f9600007fffc00

def z833 : W := mkw 0x451645a592e36c4d 0x01451645a592e36c 0xf71fc7e7f3e3ccee 0xeff71fc7e7f3e3cc

def z834 : W := mkw 0xa81b6906dc83b80e 0x02a81b6906dc83b8 0xfe9fff1fff93ffff 0xfffe9fff1fff93ff

def z835 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc13ffdd 0xfff81ff807fc13ff

def z836 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffffc0380007f 0xeefffffffc038000

def z837 : W := mkw 0x003f7dec94a7fd0f 0x43003f7dec94a7fd 0x001ffff80003ff3c 0x06001ffff80003ff

def z838 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xffffffff800000ff 0xe7ffffffff800000

def z839 : W := mkw 0x57c000036b580070 0x0857c000036b5800 0xc7e00007fffc00c2 0xf9c7e00007fffc00

def z840 : W := mkw 0x57e497f923f84cf1 0x0d57e497f923f84c 0x07e007f803fc0c22 0x0807e007f803fc0c

def z841 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffb8ffc00bf 0xeffffffffb8ffc00

def z842 : W := mkw 0xffc9a2136b580070 0x08ffc9a2136b5800 0xffffff1ffffc00ff 0xffffffff1ffffc00

def z843 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcffe07ff8fffffff 0xfdcffe07ff8fffff

def z844 : W := mkw 0x002018680424d501 0x40002018680424d5 0xc9fe38f80c7fffff 0xfcc9fe38f80c7fff

def z845 : W := mkw 0xffcd24836b580070 0x08ffcd24836b5800 0xffffffe7fffc00ff 0xffffffffe7fffc00

def z846 : W := mkw 0x0010c31410822a0c 0x800010c31410822a 0x3611c71c73823f77 0x7a3611c71c73823f

def z847 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff800000019 0xc6fffffff8000000

def z848 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff80010333f 0xf6fffffff8001033

def z849 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc7ff0dd 0xfff81ff807fc7ff0

def z850 : W := mkw 0x1280c31031902a24 0x801280c31031902a 0x3691c71873903f37 0x7a3691c71873903f

def z851 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c7393ffff 0xfa3691c71c7393ff

def z852 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xcfe00007fffc00c2 0x99cfe00007fffc00

def z853 : W := mkw 0xffcd248000000000 0x00ffcd2480000000 0xffffffe00000003f 0xe6ffffffe0000000

def z854 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff80003c0ff 0xe6fffffff80003c0

def z855 : W := mkw 0xffedb6da691800b0 0x0cffedb6da691800 0xfffffff87000003f 0xe6fffffff8700000

def z856 : W := mkw 0xa81b6806dc07b10e 0x42a81b6806dc07b1 0xf81ff807fc1ff3dd 0xf7f81ff807fc1ff3

def z857 : W := mkw 0x000000036b580070 0x08000000036b5800 0x08e00007fffc00c1 0x1908e00007fffc00

def z858 : W := mkw 0x001b68049403b00e 0x02001b68049403b0 0xf01ff807f003f0dd 0xf7f01ff807f003f0

def z859 : W := mkw 0x451605a582e74d49 0x41451605a582e74d 0xc71e07e783ffcfee 0xedc71e07e783ffcf

def z860 : W := mkw 0xffedb6d9024000c0 0x04ffedb6d9024000 0xfffffff803e0003f 0xeefffffff803e000

def z861 : W := mkw 0xa80b6802dc01b006 0x02a80b6802dc01b0 0xf80ff803fc01c088 0x87f80ff803fc01c0

def z862 : W := mkw 0x00124926dca3fc0f 0x0300124926dca3fc 0x00000007fc03fcc0 0x1100000007fc03fc

def z863 : W := mkw 0xed6db6d800000080 0x04ed6db6d8000000 0xc9fffff80000003f 0xa6c9fffff8000000

def z864 : W := mkw 0xa80b6802dc01b006 0x02a80b6802dc01b0 0xf80ff807fc01f0d9 0xf7f80ff807fc01f0

def z865 : W := mkw 0x001605a480a34c09 0x01001605a480a34c 0xc61e07e78383ccee 0xedc61e07e78383cc

def z866 : W := mkw 0xffcd24836b5800f0 0x0cffcd24836b5800 0xffee0007fffc00c3 0xfdffee0007fffc00

def z867 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffff390007f 0xfffffffffff39000

def z868 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c73923f35 0x523691c71c73923f

def z869 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc61e07e78381c008 0x45c61e07e78381c0

def z870 : W := mkw 0xbac000036b580070 0x08bac000036b5800 0x3ee00007fffc00c3 0x793ee00007fffc00

def z871 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0xc01ffff80000003c 0xe6c01ffff8000000

def z872 : W := mkw 0x002db6db6b5800f0 0x0c002db6db6b5800 0x001ffffffffc00fc 0x1f001ffffffffc00

def z873 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffbfc7c00bf 0xf7fffffffbfc7c00

def z874 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf89ff807fc13f0df 0xfff89ff807fc13f0

def z875 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xf69ffff80000003f 0x66f69ffff8000000

def z876 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe00007ffffc0cf 0xf9ffe00007ffffc0

def z877 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xf61ffffff380003c 0x47f61ffffff38000

def z878 : W := mkw 0xffedb6d8211002a0 0x84ffedb6d8211002 0xfffffff80010033f 0xe6fffffff8001003

def z879 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xf71fc7e783e3ccff 0xeff71fc7e783e3cc

def z880 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x081ffff80000003d 0xa6081ffff8000000

def z881 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3cc2e 0x4dc71e07e783e3cc

def z882 : W := mkw 0xffedb6d9235800f0 0x0cffedb6d9235800 0xffffffff83fc00ff 0xefffffffff83fc00

def z883 : W := mkw 0x00124926fdb7ff2f 0xc200124926fdb7ff 0x00000007ffffffc0 0x1900000007ffffff

def z884 : W := mkw 0xa81b6906dc83b80e 0x02a81b6906dc83b8 0xfe1fff07ff83f0dd 0xf7fe1fff07ff83f0

def z885 : W := mkw 0xed4000036b580070 0x08ed4000036b5800 0xcf600007fffc00c2 0xf9cf600007fffc00

def z886 : W := mkw 0xffc082136b580070 0x08ffc082136b5800 0xffe0071ffffc00e3 0xf9ffe0071ffffc00

def z887 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xffffffffff9c003f 0xf7ffffffffff9c00

def z888 : W := mkw 0xa82db6d800000080 0x04a82db6d8000000 0xf01ffff80000003c 0x46f01ffff8000000

def z889 : W := mkw 0x450604a182614441 0x01450604a1826144 0xc71e07e783e1c0ee 0xedc71e07e783e1c0

def z890 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c7ffe3ff7 0x7a3691c71c7ffe3f

def z891 : W := mkw 0x4516058480830808 0x0045160584808308 0xc71e07e78383ccee 0xedc71e07e78383cc

def z892 : W := mkw 0xffc082136b580070 0x08ffc082136b5800 0xfff1c71ffffe3ff7 0xfbfff1c71ffffe3f

def z893 : W := mkw 0xed124927dee3fc4f 0x03ed124927dee3fc 0xff000007ffe3fcc3 0xf9ff000007ffe3fc

def z894 : W := mkw 0xbae9ba5a6d1c91b0 0x4cbae9ba5a6d1c91 0x38e1f8187c1c3311 0x1238e1f8187c1c33

def z895 : W := mkw 0xffc486936b580070 0x08ffc486936b5800 0xffffc7fffffc00ff 0xffffffc7fffffc00

def z896 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc01f099 0xd7f81ff807fc01f0

def z897 : W := mkw 0x12adb6d800000080 0x0412adb6d8000000 0x361ffff80000003c 0x46361ffff8000000

def z898 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff800020c7f 0xeefffffff800020c

def z899 : W := mkw 0x456db6d800000080 0x04456db6d8000000 0x017ffff80000003c 0x06017ffff8000000

def z900 : W := mkw 0xbae9fa5a7d10b2a6 0x86bae9fa5a7d10b2 0x38e1f8187c103311 0x1238e1f8187c1033

def z901 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf01ff807f001c008 0x47f01ff807f001c0

def z902 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c73923f62 0x5a3691c71c73923f

def z903 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc01c09d 0xe7f81ff807fc01c0

def z904 : W := mkw 0x1292c314b1932a2c 0x801292c314b1932a 0x3691c71ff393fff7 0x7b3691c71ff393ff

def z905 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc03f0d1 0x57f81ff807fc03f0

def z906 : W := mkw 0xbaedb6d800000080 0x04baedb6d8000000 0x39fffff80000003f 0xa639fffff8000000

def z907 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80c7ffff3 0x1809e038f80c7fff

def z908 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff81ffc03fffd 0xf7f81ff81ffc03ff

def z909 : W := mkw 0x00124927dee7fd4f 0x4300124927dee7fd 0x00000007ffffffc0 0x1900000007ffffff

def z910 : W := mkw 0xffedb6db4a4800d0 0x0cffedb6db4a4800 0xfffffffb8000003f 0xe7fffffffb800000

def z911 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xf9e00007fffc00c1 0x99f9e00007fffc00

def z912 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xf61fffe000000008 0x46f61fffe0000000

def z913 : W := mkw 0xbaa9b25800000000 0x00baa9b258000000 0xfffffff80000003f 0xe6fffffff8000000

def z914 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xff7fffe00000001d 0xe6ff7fffe0000000

def z915 : W := mkw 0xa80d248000000000 0x00a80d2480000000 0xf81fffe00000003d 0xe6f81fffe0000000

def z916 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3ccac 0xc5c71e07e783e3cc

def z917 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07ff83e3fffe 0xedc71e07ff83e3ff

def z918 : W := mkw 0xbaedb6da691800b0 0x0cbaedb6da691800 0x38fffff87c1c003d 0x1638fffff87c1c00

def z919 : W := mkw 0x000000036b580070 0x08000000036b5800 0x01e00007fffc00c2 0x1901e00007fffc00

def z920 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff8006000ff 0xeefffffff8006000

def z921 : W := mkw 0xa81b6906dc83b80e 0x02a81b6906dc83b8 0xf81fff07fc03fcfd 0xf7f81fff07fc03fc

def z922 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3c0cc 0xe5c71e07e783e3c0

def z923 : W := mkw 0xffedb6da48000080 0x04ffedb6da480000 0xfffffffffc7c00ff 0xfffffffffffc7c00

def z924 : W := mkw 0xffedb6da48000080 0x04ffedb6da480000 0xfffffff87c00003f 0xf6fffffff87c0000

def z925 : W := mkw 0xffc9a2136b5800f0 0x0cffc9a2136b5800 0xffe1c007fffc00c3 0xfbffe1c007fffc00

def z926 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x001fffe000000008 0x06001fffe0000000

def z927 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf89ff81ffc03f0ff 0xf7f89ff81ffc03f0

def z928 : W := mkw 0xed6db6d800000080 0x04ed6db6d8000000 0xc01ffff80000003c 0x06c01ffff8000000

def z929 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff80000002a 0xc6fffffff8000000

def z930 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff80c6c00bf 0xe6fffffff80c6c00

def z931 : W := mkw 0x002018680424d501 0x40002018680424d5 0x39f1f8f80c7fffff 0xfa39f1f8f80c7fff

def z932 : W := mkw 0x12adb6d800000080 0x0412adb6d8000000 0x069ffff80000003e 0x06069ffff8000000

def z933 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xfff00707fffc00e7 0xf9fff00707fffc00

def z934 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf9fff81ffc7fffff 0xfff9fff81ffc7fff

def z935 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xff600007ffec00c2 0xe9ff600007ffec00

def z936 : W := mkw 0xa82db6d800000080 0x04a82db6d8000000 0x381ffff80000003d 0x06381ffff8000000

def z937 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc79e07ff83e3ccff 0xedc79e07ff83e3cc

def z938 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfe1ffff80000003d 0xe6fe1ffff8000000

def z939 : W := mkw 0xffedb6da691800b0 0x0cffedb6da691800 0xfffffffffc1c00ff 0xf7fffffffffc1c00

def z940 : W := mkw 0xffc920036b580070 0x08ffc920036b5800 0xffffc007fffc00c3 0xffffffc007fffc00

def z941 : W := mkw 0xbac000036b580070 0x08bac000036b5800 0xf8e00007fffc00c1 0xf9f8e00007fffc00

def z942 : W := mkw 0x450d248000000000 0x00450d2480000000 0xc71fffe00000003e 0xe6c71fffe0000000

def z943 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe0001ffffc33d3 0xf9ffe0001ffffc33

def z944 : W := mkw 0xffedb6d9024000c0 0x04ffedb6d9024000 0xffffffff8ffc00ff 0xffffffffff8ffc00

def z945 : W := mkw 0x4516048582430048 0x0045160485824300 0xc71e07e783e3c0ee 0xedc71e07e783e3c0

def z946 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc7fe07e783ffccee 0xedc7fe07e783ffcc

def z947 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0xf691c71ff3923ff7 0xfbf691c71ff3923f

def z948 : W := mkw 0x12edb6d800000080 0x0412edb6d8000000 0x00fffff80000003c 0x0600fffff8000000

def z949 : W := mkw 0x57a496d800000000 0x0057a496d8000000 0xfffffff80000003f 0xe6fffffff8000000

def z950 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3791c7fc73923f7f 0xfa3791c7fc73923f

def z951 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xfe1ff807ff83f0df 0xfffe1ff807ff83f0

def z952 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x009ffff80000003f 0x26009ffff8000000

def z953 : W := mkw 0xbaa9fa5a7d14b326 0xc2baa9fa5a7d14b3 0x38e1f8187c1c3311 0x1238e1f8187c1c33

def z954 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffffc7000007f 0xf6fffffffc700000

def z955 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffff87ffc003f 0xfefffffff87ffc00

def z956 : W := mkw 0x451645a592e36c4d 0x01451645a592e36c 0xc71fc7e783e3fcfe 0xefc71fc7e783e3fc

def z957 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff80c7e3fff 0xfefffffff80c7e3f

def z958 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3ff1c71c73923f77 0xfa3ff1c71c73923f

def z959 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff8007c003f 0xeefffffff8007c00

def z960 : W := mkw 0x0012492596e3fc4f 0x030012492596e3fc 0x0000000783e3fcc0 0x090000000783e3fc

def z961 : W := mkw 0xffedb6db4a4800d0 0x0cffedb6db4a4800 0xffffffff8fec00ff 0xefffffffff8fec00

def z962 : W := mkw 0xbaedb6d800000080 0x04baedb6d8000000 0x301ffff80000003c 0x06301ffff8000000

def z963 : W := mkw 0xed2db6d800000080 0x04ed2db6d8000000 0xff1ffff80000003f 0xe6ff1ffff8000000

def z964 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfefffff80000003d 0x46fefffff8000000

def z965 : W := mkw 0x57e497f923f04ee1 0x8557e497f923f04e 0x07e007f803f00f22 0x0807e007f803f00f

def z966 : W := mkw 0xed6db6d800000080 0x04ed6db6d8000000 0xf97ffff80000003d 0xe6f97ffff8000000

def z967 : W := mkw 0xed6d3ceb4e6cd5d1 0x4ced6d3ceb4e6cd5 0xc96e38e38c6dc088 0x85c96e38e38c6dc0

def z968 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x009ffff800123f7f 0x3e009ffff800123f

def z969 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf97ff807fc6ff0dd 0xf7f97ff807fc6ff0

def z970 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xfff1c007fffc00d7 0xfbfff1c007fffc00

def z971 : W := mkw 0xed4000036b580070 0x08ed4000036b5800 0xc9600007ffec0080 0x81c9600007ffec00

def z972 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc70e07e783e3ccea 0x8dc70e07e783e3cc

def z973 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c73823f37 0x623691c71c73823f

def z974 : W := mkw 0xa86db6d800000080 0x04a86db6d8000000 0x087ffff80000003c 0x06087ffff8000000

def z975 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x061ffff80000003e 0x66061ffff8000000

def z976 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc01c0c9 0xf7f81ff807fc01c0

def z977 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e3ccc8 0xcdc71e07e783e3cc

def z978 : W := mkw 0xff8da69000000000 0x00ff8da690000000 0xff9ffff80000003f 0xe6ff9ffff8000000

def z979 : W := mkw 0xffedb6d8211800b0 0x0cffedb6d8211800 0xfffffff8001c003f 0xe6fffffff8001c00

def z980 : W := mkw 0xa80b2802cc019002 0x02a80b2802cc0190 0xf81ff807fc01c0dd 0xf7f81ff807fc01c0

def z981 : W := mkw 0x1292c314b1932a2c 0x801292c314b1932a 0x369fc71c7393ff7f 0x7e369fc71c7393ff

def z982 : W := mkw 0x450605a182e14c41 0x01450605a182e14c 0xc70e07e383e3ccee 0xadc70e07e383e3cc

def z983 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71c73923f36 0x4a3691c71c73923f

def z984 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcffe07e783e3ccef 0xedcffe07e783e3cc

def z985 : W := mkw 0x000d248000000000 0x00000d2480000000 0x001fffe00000003c 0x06001fffe0000000

def z986 : W := mkw 0x57e496f9237c45f1 0x4c57e496f9237c45 0x07e007f803fc0f22 0x0807e007f803fc0f

def z987 : W := mkw 0xffedb6d9235000e0 0x04ffedb6d9235000 0xfffffffff3f000ff 0xfffffffffff3f000

def z988 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf91ff8e7fc03f0ff 0xf7f91ff8e7fc03f0

def z989 : W := mkw 0xed6db6db4a4800d0 0x0ced6db6db4a4800 0xc97ffffb8c6c00bc 0x87c97ffffb8c6c00

def z990 : W := mkw 0xffedb6d8211000a0 0x04ffedb6d8211000 0xfffffffc7380003f 0xe6fffffffc738000

def z991 : W := mkw 0xffedb6d9235800f0 0x0cffedb6d9235800 0xfffffffc73fc007f 0xfefffffffc73fc00

def z992 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf9fff807fc03f0df 0xf7f9fff807fc03f0

def z993 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0x3ffffff80000003f 0x063ffffff8000000

def z994 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x011ffff80000003e 0xa6011ffff8000000

def z995 : W := mkw 0x57c000036b580070 0x0857c000036b5800 0x37e00007fffc00c3 0x7937e00007fffc00

def z996 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe00007fffe0ce7 0xf9ffe00007fffe0c

def z997 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xff600007ffec00c1 0xf1ff600007ffec00

def z998 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff800100f3f 0xeefffffff800100f

def z999 : W := mkw 0xa80b6802dc01b006 0x02a80b6802dc01b0 0xf80ff803fc03f0dd 0xb7f80ff803fc03f0

def z1000 : W := mkw 0x454000036b580070 0x08454000036b5800 0x01600007fffc00c0 0x1901600007fffc00

def z1001 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xff7fffe00000002e 0xe6ff7fffe0000000

def z1002 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe00007ffec0083 0xe1ffe00007ffec00

def z1003 : W := mkw 0xffcda6936b5800f0 0x0cffcda6936b5800 0xffffc71ffffc00f7 0xffffffc71ffffc00

def z1004 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe000e7fffc00ef 0xf9ffe000e7fffc00

def z1005 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc03fcff 0xfff81ff807fc03fc

def z1006 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e1ccaa 0xcdc71e07e783e1cc

def z1007 : W := mkw 0xbaedb6d800000080 0x04baedb6d8000000 0x3efffff80000003f 0x663efffff8000000

def z1008 : W := mkw 0xffcda6936b5800f0 0x0cffcda6936b5800 0xffffff07fffc00df 0xffffffff07fffc00

def z1009 : W := mkw 0x12adb6d800000080 0x0412adb6d8000000 0x309ffff80000003d 0x06309ffff8000000

def z1010 : W := mkw 0x003bfb7c94a7ff0f 0xc2003bfb7c94a7ff 0x001ffff80003ff3c 0x06001ffff80003ff

def z1011 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf8fff807fc1ff0dd 0xf7f8fff807fc1ff0

def z1012 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff80c0000ff 0xf6fffffff80c0000

def z1013 : W := mkw 0xffc082136b580070 0x08ffc082136b5800 0xffe1c01ffffc00d3 0xfbffe1c01ffffc00

def z1014 : W := mkw 0x450605a182e14c41 0x01450605a182e14c 0xc71e07e383e1ccae 0xedc71e07e383e1cc

def z1015 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e1c0ca 0xedc71e07e783e1c0

def z1016 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc61e07e78383cc6e 0x6dc61e07e78383cc

def z1017 : W := mkw 0xed6db6d800000080 0x04ed6db6d8000000 0xcf7ffff80000003e 0xe6cf7ffff8000000

def z1018 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xfffffffff3e000ff 0xeffffffffff3e000

def z1019 : W := mkw 0xffc920036b580070 0x08ffc920036b5800 0xffe1f807fffc00d3 0xfbffe1f807fffc00

def z1020 : W := mkw 0xffedb6db6b5800f0 0x0cffedb6db6b5800 0xffffffe7fffc00cb 0xffffffffe7fffc00

def z1021 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xfee00007fffc00c1 0x59fee00007fffc00

def z1022 : W := mkw 0x452db6d800000080 0x04452db6d8000000 0xcffffff80000003f 0xe6cffffff8000000

def z1023 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x37f1c71c73fe3f77 0x7a37f1c71c73fe3f

def z1024 : W := mkw 0xffedb6d8211000a0 0x04ffedb6d8211000 0xfffffffc73923f7f 0xfefffffffc73923f

def z1025 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3691c71873923f37 0x1a3691c71873923f

def z1026 : W := mkw 0x57adb6d800000080 0x0457adb6d8000000 0xf79ffff80000003f 0xe6f79ffff8000000

def z1027 : W := mkw 0xffc404836b580070 0x08ffc404836b5800 0xffe007e7fffc00e3 0xf9ffe007e7fffc00

def z1028 : W := mkw 0xa81b60049003200c 0x00a81b6004900320 0xf81ff807f003f0dd 0xf7f81ff807f003f0

def z1029 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xffffffe00000000b 0xe6ffffffe0000000

def z1030 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xf7fffff80000003e 0x46f7fffff8000000

def z1031 : W := mkw 0xffedb6da691800b0 0x0cffedb6da691800 0xfffffff87c7c00ff 0xfefffffff87c7c00

def z1032 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff803fc03f09d 0x97f81ff803fc03f0

def z1033 : W := mkw 0x452db6d800000080 0x04452db6d8000000 0xc11ffff80000003c 0x86c11ffff8000000

def z1034 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xcf7e07e78fefccee 0xedcf7e07e78fefcc

def z1035 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff800000033 0x46fffffff8000000

def z1036 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf01ff807f003f05d 0x77f01ff807f003f0

def z1037 : W := mkw 0xa85b6806dc0bb01e 0x0aa85b6806dc0bb0 0xf87ff807fc0ff0dd 0xf7f87ff807fc0ff0

def z1038 : W := mkw 0x12d0c314319a2a3c 0x8812d0c314319a2a 0x36f1c71c739e3f77 0x7a36f1c71c739e3f

def z1039 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0xf69fc71c73923f7f 0xfef69fc71c73923f

def z1040 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xfffe0007fffc00cf 0xfdfffe0007fffc00

def z1041 : W := mkw 0x002018680424d501 0x40002018680424d5 0x09e038f80c7fffea 0x9809e038f80c7fff

def z1042 : W := mkw 0xffedb6da691000a0 0x04ffedb6da691000 0xffffffffff9000ff 0xffffffffffff9000

def z1043 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x08fffff80000003d 0x0608fffff8000000

def z1044 : W := mkw 0xffedb6da691800b0 0x0cffedb6da691800 0xfffffffc7f9c007f 0xfefffffffc7f9c00

def z1045 : W := mkw 0x57a497f923f44f61 0xc157a497f923f44f 0x07e007f803fc0f22 0x0807e007f803fc0f

def z1046 : W := mkw 0x12adb6d800000080 0x0412adb6d8000000 0x3ffffff80000003f 0xe63ffffff8000000

def z1047 : W := mkw 0x1280c31031902a24 0x801280c31031902a 0x3681c71873923f77 0x3a3681c71873923f

def z1048 : W := mkw 0x57edb6d800000080 0x0457edb6d8000000 0x0ffffff80000003f 0xa60ffffff8000000

def z1049 : W := mkw 0xffedb6d9235800f0 0x0cffedb6d9235800 0xfffffff80ffc00ff 0xfefffffff80ffc00

def z1050 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff80010007f 0xfefffffff8001000

def z1051 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783e1c0ae 0xe5c71e07e783e1c0

def z1052 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3ef1c71c7f9e3f77 0x7a3ef1c71c7f9e3f

def z1053 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe00007fffc0003 0x59ffe00007fffc00

def z1054 : W := mkw 0x12c000036b580070 0x0812c000036b5800 0x00e00007fffc00c0 0x1900e00007fffc00

def z1055 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc71e07e783f3ffee 0xfdc71e07e783f3ff

def z1056 : W := mkw 0xffc404836b580070 0x08ffc404836b5800 0xfffe0707fffc00c3 0xfdfffe0707fffc00

def z1057 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x09fffff80c7c00ff 0xbe09fffff80c7c00

def z1058 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc03c0cc 0xe7f81ff807fc03c0

def z1059 : W := mkw 0xffedb6d800040180 0x44ffedb6d8000401 0xfffffff8001c033f 0xe6fffffff8001c03

def z1060 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf81ff807fc03f09c 0xc7f81ff807fc03f0

def z1061 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3611c71c73823f75 0x723611c71c73823f

def z1062 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf01ff807fc03f0dc 0x57f01ff807fc03f0

def z1063 : W := mkw 0xa82db6d800000080 0x04a82db6d8000000 0xc81ffff80000003c 0x86c81ffff8000000

def z1064 : W := mkw 0x450404a102604441 0x00450404a1026044 0xc71e07e783e3ccee 0xedc71e07e783e3cc

def z1065 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc61e07e78383ccec 0xe5c61e07e78383cc

def z1066 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xff600007fffc00c0 0xd9ff600007fffc00

def z1067 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3611c71c73923f74 0x5a3611c71c73923f

def z1068 : W := mkw 0xffedb6d800000080 0x04ffedb6d8000000 0xfffffff800023f3f 0xe6fffffff800023f

def z1069 : W := mkw 0xffc000036b580070 0x08ffc000036b5800 0xffe00007fffc0082 0xc9ffe00007fffc00

def z1070 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf01ff807f003f0dc 0xe7f01ff807f003f0

def z1071 : W := mkw 0x000000036b580070 0x08000000036b5800 0x09600007fffc00c0 0x9909600007fffc00

def z1072 : W := mkw 0xa81b6806dc03b00e 0x02a81b6806dc03b0 0xf80ff807fc03f0d9 0x97f80ff807fc03f0

def z1073 : W := mkw 0xffc920036b580070 0x08ffc920036b5800 0xffee3807fffc00cb 0xfdffee3807fffc00

def z1074 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3681c71c73923f73 0x1a3681c71c73923f

def z1075 : W := mkw 0x451645a592e36e4d 0x81451645a592e36e 0xc71e07e783e3ffee 0xedc71e07e783e3ff

def z1076 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3791c71c73f23ff7 0xfa3791c71c73f23f

def z1077 : W := mkw 0xed6d34c800000080 0x04ed6d34c8000000 0xff7fffe00000003f 0xe6ff7fffe0000000

def z1078 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xf71e07e7f3e3ccef 0xfdf71e07e7f3e3cc

def z1079 : W := mkw 0x451605a582e34c49 0x01451605a582e34c 0xc79e07e783f3ccef 0xfdc79e07e783f3cc

def z1080 : W := mkw 0xffedb6d8211000a0 0x04ffedb6d8211000 0xfffffff80390003f 0xeefffffff8039000

def z1081 : W := mkw 0x002db6d800000080 0x04002db6d8000000 0x097ffff80000003c 0x86097ffff8000000

def z1082 : W := mkw 0x1292c314b1932a2c 0x801292c314b1932a 0xf69fc71ff3923f77 0x7ff69fc71ff3923f

def z1083 : W := mkw 0xffedb6db4a4800d0 0x0cffedb6db4a4800 0xfffffffb8c7c00ff 0xfffffffffb8c7c00

def z1084 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3e91ff1c73923f7f 0xfa3e91ff1c73923f

def z1085 : W := mkw 0x1290c31431922a2c 0x801290c31431922a 0x3611c71c73823f76 0x6a3611c71c73823f

def z1086 : W := mkw 0xed4000034a480050 0x08ed4000034a4800 0xff600007ffec00c3 0xf9ff600007ffec00

def z1087 : W := mkw 0xbaadb6d800000080 0x04baadb6d8000000 0xfe9ffff80000003f 0xe6fe9ffff8000000

def z1088 : W := mkw 0xba80000269100020 0x00ba800002691000 0xffe00007fffc00c3 0xf9ffe00007fffc00

def z1089 : W := mkw 0xffedb6da48080090 0x0cffedb6da480800 0xfffffff80c0c003f 0xe6fffffff80c0c00

def z1090 : W := mkw 0xbaedb6d800000080 0x04baedb6d8000000 0xf8fffff80000003d 0xe6f8fffff8000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z0,z1,z2,z3,z7,z8]),(0,[z0,z1,z9,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z10,z5,z6]),(0,[z0,z11,z1,z12,z2,z3,z5])],[],[(0,[z0,z1,z2,z3,z5,z13,z6]),(0,[z0,z1,z2,z14,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z15,z6]),(0,[z0,z11,z1,z2,z3,z16,z5]),(0,[z17,z0,z1,z2,z18,z5,z6]),(0,[z0,z19,z1,z2,z3,z5,z8])],[(0,[z0,z2,z20,z3,z21,z5,z6]),(0,[z0,z2,z3,z22,z5,z6,z23]),(0,[z24,z0,z1,z2,z3,z5,z6]),(0,[z25,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z26,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z27,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z28]),(0,[z0,z1,z2,z3,z5,z29,z6]),(0,[z30,z0,z1,z2,z3,z5,z6]),(0,[z31,z0,z1,z3,z32,z5,z6])],[(1,[z33,z34,z2,z3,z5,z6]),(0,[z35,z0,z1,z2,z3,z5,z6]),(1,[z0,z36,z1,z2,z3,z5]),(0,[z37,z0,z1,z2,z3,z5,z6]),(0,[z38,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z39,z3,z5,z6]),(0,[z0,z1,z2,z3,z40,z5,z6])],[(0,[z0,z41,z2,z42,z3,z5,z6]),(1,[z0,z41,z2,z20,z5,z6]),(1,[z0,z43,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z44,z8])],[(0,[z0,z1,z2,z3,z5,z45,z6]),(0,[z0,z1,z2,z46,z3,z5,z6]),(0,[z47,z0,z1,z2,z3,z5,z6]),(0,[z48,z0,z1,z2,z3,z5,z6]),(0,[z49,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z39,z3,z5,z50]),(0,[z0,z1,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z52,z6])]],
   [[(0,[z0,z1,z2,z20,z53,z5,z6]),(0,[z0,z1,z54,z2,z3,z5,z6]),(0,[z0,z1,z2,z55,z3,z5,z6]),(0,[z0,z19,z1,z2,z3,z5,z6]),(0,[z56,z0,z11,z1,z2,z3,z5])],[(0,[z57,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z58]),(0,[z0,z59,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z60,z5,z6])],[(0,[z0,z1,z2,z61,z3,z5,z6]),(0,[z0,z1,z62,z2,z3,z5,z6]),(0,[z0,z1,z2,z63,z3,z5,z6]),(0,[z0,z1,z2,z64,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z6,z8])],[(0,[z0,z1,z2,z3,z5,z6,z65]),(0,[z0,z66,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z44,z6])],[(0,[z67,z0,z1,z2,z3,z5,z6]),(0,[z0,z68,z1,z2,z3,z5,z6]),(0,[z69,z0,z1,z2,z3,z70,z6]),(0,[z71,z0,z1,z2,z3,z5,z6]),(0,[z0,z41,z2,z20,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z72]),(0,[z73,z0,z11,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z22,z5,z8]),(1,[z0,z74,z2,z3,z5,z6]),(1,[z0,z1,z75,z3,z76,z6]),(0,[z77,z0,z1,z2,z3,z5,z6]),(0,[z78,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z79,z6]),(0,[z0,z1,z75,z2,z3,z80,z5])],[(0,[z0,z1,z81,z2,z3,z5,z6]),(0,[z82,z1,z2,z53,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z83,z6]),(0,[z0,z1,z2,z84,z3,z5,z6]),(0,[z85,z0,z1,z2,z3,z5,z6]),(0,[z0,z59,z1,z2,z3,z5,z6]),(0,[z86,z0,z1,z2,z3,z5,z6]),(0,[z87,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z88,z42,z3,z5,z6]),(0,[z0,z1,z89,z42,z3,z5,z6]),(0,[z90,z0,z1,z2,z20,z5,z6])],[(0,[z91,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z42,z3,z5,z8]),(0,[z90,z0,z1,z92,z3,z5,z6]),(0,[z0,z41,z1,z2,z21,z5,z6]),(1,[z0,z1,z2,z3,z5,z93]),(0,[z0,z94,z1,z2,z3,z5,z6])],[(0,[z69,z0,z1,z2,z95,z5,z6]),(1,[z0,z1,z2,z96,z3,z6])],[(0,[z97,z0,z1,z2,z3,z5,z6]),(0,[z98,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z99,z5,z6]),(0,[z0,z1,z2,z3,z22,z5,z6])],[(0,[z0,z1,z2,z3,z5,z100,z6]),(0,[z0,z1,z2,z3,z5,z101,z6]),(1,[z0,z102,z2,z3,z5,z6]),(0,[z103,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z104]),(0,[z0,z1,z2,z3,z105,z5,z8])],[(0,[z106,z0,z1,z107,z3,z5,z6]),(0,[z108,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z109]),(0,[z110,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z5,z5])],[(0,[z0,z1,z88,z3,z5,z76,z6]),(0,[z0,z1,z2,z3,z5,z111,z23]),(0,[z112,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z113,z5,z6])],[(0,[z0,z1,z2,z3,z114,z5,z6]),(0,[z115,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z42,z3,z5,z6]),(0,[z0,z1,z2,z20,z3,z5,z8]),(0,[z31,z0,z1,z75,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z116])]],
   [[(0,[z0,z1,z2,z3,z5,z117,z6]),(0,[z0,z1,z2,z3,z5,z118,z6]),(0,[z0,z1,z2,z3,z5,z119,z6]),(0,[z0,z120,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z121,z6]),(1,[z0,z1,z2,z3,z76,z8]),(0,[z0,z122,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z45]),(0,[z123,z0,z1,z2,z3,z5,z45]),(0,[z0,z34,z2,z3,z5,z124,z6]),(0,[z0,z1,z2,z3,z125,z5,z6]),(0,[z0,z126,z127,z2,z3,z5,z6]),(0,[z0,z128,z11,z1,z2,z3,z5])],[(0,[z0,z1,z2,z129,z3,z5,z6]),(0,[z0,z59,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z130,z3,z5,z6]),(0,[z0,z1,z2,z3,z105,z5,z6]),(0,[z0,z11,z131,z1,z2,z3,z5])],[(0,[z132,z0,z1,z2,z3,z5,z6]),(0,[z0,z126,z2,z3,z21,z5,z6]),(0,[z133,z0,z1,z2,z3,z134,z5]),(0,[z135,z0,z11,z1,z2,z3,z5]),(0,[z136,z0,z1,z2,z3,z5,z6])],[(0,[z137,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z138,z5,z44,z6]),(0,[z0,z1,z139,z2,z3,z5,z6])],[(0,[z0,z1,z2,z20,z3,z5,z6]),(0,[z0,z140,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z141,z3,z5,z6]),(0,[z142,z0,z1,z2,z3,z5,z8])],[(0,[z143,z0,z1,z2,z3,z5,z6]),(0,[z144,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z145,z3,z5,z6]),(0,[z146,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z147,z5,z6]),(0,[z0,z1,z2,z148,z3,z5,z6])],[(0,[z0,z1,z2,z3,z149,z5,z6]),(0,[z150,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z151])]],
   [[(0,[z0,z1,z152,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z7,z5]),(0,[z0,z11,z1,z2,z3,z5,z153]),(0,[z0,z1,z154,z2,z3,z5,z6]),(0,[z155,z0,z1,z2,z138,z3,z6])],[(0,[z33,z0,z1,z2,z3,z5,z8]),(0,[z90,z0,z41,z2,z3,z5,z6])],[(0,[z0,z1,z156,z2,z3,z5,z6]),(0,[z31,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z157,z6]),(0,[z0,z1,z2,z18,z3,z5,z8]),(0,[z158,z0,z1,z2,z3,z5,z8])],[(0,[z0,z1,z2,z3,z159,z5,z6]),(0,[z0,z160,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z161,z5,z6]),(0,[z142,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z162,z3,z5,z6])],[(0,[z163,z0,z1,z2,z3,z5,z8]),(0,[z69,z155,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z164,z5,z6]),(0,[z90,z0,z11,z1,z2,z3,z5]),(1,[z0,z1,z165,z2,z3,z5])],[(0,[z0,z1,z2,z3,z166,z5,z6])],[(0,[z0,z1,z2,z3,z167,z5,z6]),(0,[z0,z1,z2,z168,z3,z5,z6]),(0,[z0,z1,z169,z2,z3,z5,z6])],[(0,[z33,z0,z1,z2,z3,z5,z6]),(0,[z106,z0,z1,z88,z3,z5,z6]),(0,[z0,z1,z170,z2,z3,z5,z6]),(0,[z0,z171,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z172,z5,z6]),(0,[z0,z1,z2,z173,z5,z44,z6])]],
   [[(0,[z69,z0,z102,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z174]),(0,[z175,z0,z1,z2,z3,z124,z6]),(0,[z158,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z176,z3,z5,z6]),(0,[z177,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z18,z3,z5,z6]),(0,[z0,z11,z1,z2,z178,z3,z5])],[(0,[z175,z0,z179,z2,z3,z5,z6]),(1,[z0,z180,z2,z3,z5,z23]),(0,[z155,z0,z11,z1,z2,z3,z5])],[(0,[z181,z0,z1,z2,z3,z22,z5]),(0,[z0,z1,z75,z2,z3,z76,z6]),(0,[z135,z0,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z5,z182,z6]),(0,[z0,z1,z2,z183,z3,z5,z6])],[(1,[z0,z1,z2,z184,z5,z6]),(0,[z185,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z186,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z187]),(0,[z0,z1,z2,z3,z22,z5,z111]),(0,[z0,z1,z188,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z189,z6]),(0,[z190,z0,z1,z2,z3,z5,z6])],[],[(0,[z191,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z192,z3,z5,z6]),(0,[z0,z1,z2,z3,z193,z5,z6]),(0,[z0,z1,z2,z3,z194,z5,z6]),(0,[z0,z1,z2,z3,z195,z5,z6])],[(0,[z196,z1,z2,z3,z197,z5,z6]),(0,[z0,z198,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z111,z8]),(0,[z90,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z199,z3,z5,z6]),(0,[z0,z1,z200,z2,z39,z3,z5]),(0,[z0,z1,z2,z3,z5,z201,z6]),(0,[z0,z1,z2,z39,z5,z6,z50])]],
   [[(0,[z202,z0,z1,z2,z3,z5,z6]),(1,[z203,z1,z2,z204,z5,z6]),(0,[z0,z1,z2,z3,z5,z205,z6]),(1,[z0,z1,z2,z3,z124,z8]),(0,[z0,z1,z2,z3,z5,z206,z6])],[(0,[z90,z0,z1,z207,z3,z5,z6]),(0,[z208,z0,z11,z1,z2,z3,z5]),(0,[z0,z209,z1,z2,z3,z5,z6]),(0,[z210,z0,z1,z2,z3,z5,z8])],[(0,[z0,z1,z2,z3,z211,z5,z6]),(0,[z212,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z213,z5,z6]),(1,[z0,z1,z2,z214,z5,z6])],[(0,[z0,z1,z2,z3,z5,z215,z6]),(0,[z0,z1,z2,z3,z5,z216,z6]),(0,[z0,z11,z1,z2,z173,z3,z5])],[(0,[z0,z217,z1,z2,z3,z5,z6]),(0,[z0,z1,z218,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z5,z76]),(0,[z0,z1,z2,z219,z3,z32,z5])],[(0,[z0,z220,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z111,z6]),(0,[z0,z1,z2,z3,z221,z5,z6]),(1,[z175,z0,z2,z3,z7,z6]),(0,[z0,z1,z222,z2,z3,z5,z6]),(0,[z181,z0,z1,z2,z3,z5,z8]),(0,[z223,z0,z1,z2,z3,z5,z6])],[(1,[z224,z0,z1,z2,z3,z6]),(1,[z0,z1,z2,z39,z5,z50])],[(0,[z123,z0,z179,z2,z3,z5,z6]),(0,[z0,z1,z2,z225,z3,z5,z6]),(0,[z0,z1,z127,z107,z3,z5,z6]),(0,[z0,z1,z2,z226,z3,z5,z6]),(0,[z227,z0,z11,z1,z2,z3,z5]),(0,[z224,z0,z1,z2,z3,z5,z6]),(0,[z0,z228,z1,z2,z3,z5,z6]),(0,[z210,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z229,z1,z2,z3,z5,z6]),(0,[z230,z0,z1,z2,z3,z5,z6]),(0,[z231,z0,z1,z2,z3,z5,z6]),(0,[z232,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z233,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z234,z5,z6]),(0,[z0,z1,z235,z2,z3,z5,z6]),(0,[z0,z1,z2,z138,z3,z6,z8])],[(0,[z0,z1,z2,z236,z3,z5,z6]),(0,[z0,z1,z2,z237,z3,z5,z6]),(0,[z238,z0,z1,z2,z3,z5,z6]),(0,[z239,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z240,z5,z6]),(0,[z0,z1,z2,z3,z241,z5,z6]),(1,[z0,z1,z2,z138,z3,z8]),(0,[z0,z1,z2,z96,z39,z3,z6]),(0,[z0,z1,z2,z242,z3,z5,z6])],[(0,[z0,z1,z2,z3,z243,z5,z6]),(1,[z0,z1,z2,z3,z5,z244]),(0,[z175,z0,z11,z1,z2,z3,z5]),(0,[z181,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z107,z2,z3,z5,z6]),(0,[z203,z82,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z2,z53,z5,z44,z6]),(0,[z245,z0,z1,z2,z3,z5,z6]),(0,[z0,z180,z1,z2,z3,z246,z6]),(0,[z0,z1,z2,z173,z3,z5,z247])],[(0,[z0,z1,z2,z3,z5,z6,z248]),(0,[z0,z249,z1,z2,z3,z5,z6]),(0,[z250,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z20,z134,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z251])],[(0,[z252,z0,z1,z2,z3,z5,z6]),(0,[z196,z0,z1,z2,z3,z197,z6]),(0,[z0,z1,z2,z3,z253,z5,z6]),(0,[z254,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z255,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z256]),(0,[z0,z1,z257,z2,z3,z5,z6])],[(0,[z0,z1,z2,z20,z204,z5,z6]),(0,[z258,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z259,z5,z6])],[(0,[z0,z1,z2,z260,z3,z5,z6])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z261,z0,z1,z2,z3,z5,z6]),(0,[z0,z126,z1,z42,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z262]),(0,[z263,z0,z1,z2,z138,z3,z6])],[(0,[z0,z1,z2,z3,z5,z6,z264]),(0,[z265,z0,z11,z1,z2,z3,z5]),(0,[z0,z1,z12,z2,z3,z5,z6])],[(0,[z1,z2,z53,z3,z204,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z266]),(0,[z181,z0,z180,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z267,z5]),(1,[z0,z1,z2,z3,z80,z5]),(0,[z31,z0,z1,z2,z3,z32,z6])],[(0,[z106,z0,z11,z1,z2,z3,z5]),(0,[z268,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z269,z5])],[(1,[z73,z1,z2,z3,z5,z111]),(0,[z0,z1,z270,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z271,z6]),(0,[z272,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z273,z5,z6])]],
   [[(0,[z0,z11,z34,z1,z2,z3,z5]),(0,[z82,z0,z1,z2,z53,z5,z6]),(1,[z0,z59,z2,z3,z124,z6]),(0,[z0,z11,z1,z89,z2,z3,z5]),(0,[z135,z0,z1,z2,z3,z5,z153]),(0,[z0,z1,z2,z138,z3,z5,z8])],[(0,[z123,z0,z11,z1,z2,z3,z5]),(0,[z0,z1,z127,z88,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z5,z70]),(0,[z0,z1,z2,z3,z274,z5,z6]),(0,[z0,z1,z2,z275,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z247])],[(0,[z0,z1,z2,z3,z5,z276,z6]),(0,[z0,z59,z1,z2,z3,z124,z6]),(1,[z0,z1,z2,z219,z3,z5]),(0,[z17,z0,z1,z2,z3,z5,z8]),(0,[z0,z277,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z278,z3,z5,z6]),(1,[z0,z1,z2,z3,z279,z5]),(0,[z280,z0,z1,z2,z3,z5,z6])],[(0,[z0,z11,z1,z179,z2,z3,z5]),(0,[z69,z0,z1,z2,z3,z5,z8]),(0,[z0,z11,z1,z2,z3,z5,z124]),(0,[z0,z1,z89,z2,z3,z5,z8]),(0,[z263,z0,z11,z1,z2,z3,z5])],[(0,[z33,z0,z34,z2,z3,z5,z6]),(0,[z0,z127,z2,z42,z3,z5,z6]),(0,[z0,z1,z2,z3,z124,z6,z8]),(0,[z0,z1,z2,z3,z281,z5,z6])],[(0,[z0,z1,z2,z282,z3,z5,z6]),(0,[z0,z1,z2,z53,z21,z5,z6]),(0,[z0,z283,z1,z2,z3,z5,z6]),(0,[z284,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z285,z6]),(0,[z286,z0,z1,z2,z3,z5,z8])],[(0,[z0,z287,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z204,z5,z44,z6]),(0,[z0,z1,z2,z3,z267,z5,z6]),(0,[z0,z288,z1,z2,z3,z5,z6]),(0,[z0,z289,z1,z2,z3,z5,z6]),(0,[z290,z0,z1,z2,z3,z5,z6])]],
   [[(1,[z0,z1,z291,z3,z5,z6]),(0,[z123,z0,z1,z291,z3,z5,z6]),(1,[z0,z1,z292,z3,z5,z6]),(0,[z0,z1,z2,z3,z293,z5,z6]),(0,[z0,z1,z2,z3,z294,z5,z6])],[(0,[z0,z1,z2,z3,z5,z295,z6]),(0,[z0,z1,z2,z3,z296,z5,z6]),(0,[z0,z11,z1,z2,z3,z22,z5]),(0,[z0,z1,z2,z297,z3,z5,z6])],[(0,[z69,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z298,z6]),(0,[z0,z1,z2,z3,z5,z299,z6]),(0,[z0,z1,z89,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z300,z5,z6]),(0,[z0,z1,z2,z3,z301,z5,z6])],[(0,[z302,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z303]),(0,[z0,z1,z2,z3,z304,z5,z6]),(0,[z305,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z173,z3,z5,z8])],[(0,[z0,z1,z2,z306,z3,z5,z6]),(0,[z146,z0,z1,z2,z184,z5,z6]),(0,[z0,z1,z2,z3,z307,z5,z6])],[(0,[z308,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z99,z5,z6]),(0,[z0,z1,z2,z3,z309,z5,z6]),(1,[z31,z0,z1,z3,z32,z6]),(0,[z47,z0,z11,z1,z2,z3,z5])],[(0,[z203,z0,z11,z1,z2,z3,z5]),(0,[z310,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z311,z6])],[(0,[z82,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z312,z3,z5,z6])]],
   [[(1,[z0,z1,z2,z3,z100,z6]),(0,[z123,z0,z1,z2,z3,z100,z6]),(0,[z0,z1,z2,z3,z5,z6,z313]),(0,[z0,z1,z2,z314,z3,z5,z6]),(0,[z208,z0,z1,z89,z3,z5,z6]),(0,[z0,z1,z2,z3,z134,z5,z8])],[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z315,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z316,z5,z6]),(0,[z0,z11,z1,z2,z3,z204,z5]),(0,[z0,z1,z2,z3,z197,z5,z8])],[(0,[z317,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z318]),(0,[z0,z319,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z204,z5,z8]),(0,[z0,z1,z2,z320,z3,z5,z6]),(0,[z321,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z102,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z121,z6]),(0,[z0,z11,z1,z2,z3,z5,z8])],[(0,[z82,z0,z1,z2,z3,z5,z6]),(1,[z82,z1,z2,z53,z5,z6]),(0,[z322,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z53,z3,z5]),(0,[z0,z1,z2,z3,z5,z323,z6]),(0,[z324,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z134,z5,z6]),(0,[z325,z0,z1,z2,z3,z5,z6]),(0,[z326,z0,z1,z2,z3,z5,z6])],[(0,[z0,z327,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z124,z70,z6]),(0,[z0,z59,z1,z2,z3,z279,z5]),(0,[z181,z0,z1,z2,z3,z5,z23]),(0,[z0,z1,z2,z3,z5,z6,z8])]],
   [[(0,[z0,z1,z2,z204,z21,z5,z6]),(0,[z0,z1,z2,z3,z5,z328,z6]),(0,[z0,z1,z2,z329,z3,z5,z6]),(1,[z90,z0,z2,z21,z5,z6]),(0,[z0,z1,z2,z3,z330,z5,z6])],[(0,[z0,z1,z331,z2,z3,z5,z6]),(0,[z332,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z204,z5,z6]),(0,[z196,z0,z11,z1,z2,z3,z5]),(0,[z227,z1,z2,z3,z5,z6,z187]),(0,[z0,z1,z2,z3,z5,z333,z6]),(0,[z0,z1,z3,z16,z5,z6,z153]),(0,[z0,z1,z2,z96,z3,z5,z6]),(0,[z334,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z335,z5,z6]),(0,[z0,z336,z1,z2,z3,z5,z6]),(0,[z0,z337,z1,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z5,z6])],[(0,[z338,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z339,z2,z3,z5,z6])],[(0,[z340,z0,z1,z2,z3,z5,z6]),(0,[z0,z34,z1,z2,z3,z5,z8]),(0,[z341,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z342,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z343]),(0,[z0,z11,z1,z2,z3,z5,z50])],[(0,[z0,z1,z2,z3,z5,z344,z6])],[(0,[z0,z1,z2,z3,z5,z6,z153]),(0,[z0,z1,z2,z345,z3,z5,z6]),(0,[z0,z1,z2,z3,z346,z6,z8]),(0,[z0,z1,z347,z2,z3,z5,z6])],[(0,[z0,z1,z2,z348,z3,z5,z6]),(0,[z146,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z349,z5,z6]),(0,[z0,z1,z2,z3,z269,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z50])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z350])],[(0,[z0,z1,z2,z3,z5,z6,z351]),(1,[z0,z1,z2,z3,z5,z352]),(0,[z0,z1,z2,z3,z22,z5,z187]),(0,[z353,z0,z1,z2,z3,z5,z6]),(0,[z0,z354,z1,z2,z3,z5,z6])],[(0,[z123,z0,z1,z2,z3,z234,z6]),(0,[z69,z0,z1,z2,z99,z5,z6]),(1,[z0,z1,z2,z3,z5,z116]),(0,[z155,z0,z1,z2,z3,z346,z6])],[(0,[z0,z1,z2,z3,z5,z70,z8]),(0,[z0,z1,z2,z3,z355,z5,z6]),(0,[z31,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z356,z5,z6])],[(0,[z0,z1,z2,z3,z5,z8,z248])],[(0,[z163,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z357,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z184,z5,z6])],[(0,[z0,z1,z358,z2,z3,z5,z6]),(0,[z0,z359,z1,z2,z3,z5,z6]),(0,[z73,z1,z2,z3,z5,z111,z6]),(0,[z0,z1,z2,z360,z3,z5,z6]),(0,[z0,z361,z1,z2,z3,z5,z6])],[(0,[z0,z1,z362,z2,z3,z5,z6]),(0,[z0,z41,z1,z2,z3,z5,z8]),(0,[z0,z11,z180,z1,z2,z3,z5]),(0,[z0,z1,z2,z363,z3,z5,z6]),(0,[z364,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z365,z1,z2,z3,z5,z6]),(0,[z146,z0,z1,z127,z3,z5,z6]),(0,[z366,z0,z1,z2,z3,z5,z6]),(0,[z367,z0,z11,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z368,z5,z6]),(0,[z0,z1,z2,z3,z5,z70,z6]),(0,[z0,z1,z2,z3,z5,z369,z6]),(0,[z0,z1,z2,z3,z7,z6,z8]),(0,[z370,z0,z1,z2,z3,z5,z6]),(0,[z0,z371,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z18,z39,z3,z5])],[(1,[z0,z1,z2,z3,z5,z151]),(1,[z146,z0,z42,z3,z5,z6]),(0,[z0,z1,z2,z372,z20,z5,z6]),(0,[z155,z0,z1,z2,z3,z32,z6]),(0,[z0,z1,z2,z3,z373,z5,z6])],[(0,[z374,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z89,z2,z134,z5,z6]),(0,[z0,z1,z375,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z205,z6]),(0,[z0,z2,z42,z3,z21,z5,z6])],[(0,[z0,z1,z376,z2,z3,z5,z6]),(0,[z0,z41,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z377,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z378,z6]),(0,[z0,z1,z2,z379,z173,z3,z5]),(0,[z0,z1,z2,z3,z346,z5,z8]),(0,[z0,z1,z2,z380,z3,z5,z6])],[(0,[z0,z381,z1,z2,z3,z5,z6]),(0,[z0,z1,z382,z2,z3,z5,z6]),(0,[z0,z1,z2,z95,z3,z5,z6]),(0,[z73,z0,z1,z2,z3,z5,z8]),(0,[z383,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z75,z2,z3,z5,z116]),(0,[z384,z0,z1,z2,z3,z5,z6]),(0,[z155,z0,z11,z1,z2,z3,z6]),(0,[z0,z131,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z72]),(0,[z163,z106,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z385,z3,z5,z6]),(0,[z0,z11,z59,z1,z2,z3,z5]),(0,[z0,z386,z1,z2,z3,z5,z6]),(0,[z56,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z387,z1,z2,z3,z5,z6]),(0,[z196,z0,z1,z2,z3,z6,z8])],[(0,[z0,z1,z2,z388,z3,z5,z6]),(1,[z0,z1,z92,z3,z5,z6]),(0,[z0,z1,z2,z389,z3,z5,z6])],[(0,[z123,z1,z179,z2,z3,z5,z6]),(0,[z0,z1,z2,z390,z3,z5,z6])],[(1,[z0,z1,z391,z3,z5,z6]),(0,[z123,z0,z1,z391,z3,z5,z6]),(0,[z0,z1,z2,z3,z392,z5,z6]),(0,[z0,z1,z2,z3,z393,z5,z6]),(0,[z394,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z5,z111]),(0,[z0,z1,z2,z3,z395,z5,z6]),(0,[z0,z59,z2,z3,z5,z124,z6]),(0,[z0,z1,z2,z3,z267,z134,z5]),(0,[z0,z396,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z93]),(0,[z0,z1,z2,z3,z346,z5,z6])],[(0,[z0,z1,z2,z3,z397,z5,z6]),(0,[z73,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z165,z2,z3,z7,z5]),(0,[z0,z1,z2,z398,z3,z5,z6]),(0,[z263,z0,z1,z2,z173,z5,z6])],[(0,[z399,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z400,z6]),(0,[z0,z1,z2,z3,z32,z5,z262]),(0,[z401,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z402])],[(0,[z403,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z404,z3,z5,z6])],[(0,[z0,z1,z2,z3,z405,z5,z6]),(0,[z0,z126,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z406,z3,z5,z6]),(0,[z0,z11,z1,z75,z2,z3,z5]),(0,[z17,z0,z1,z200,z2,z3,z5])]],
   [[(0,[z407,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z408,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z5,z8]),(0,[z0,z180,z1,z2,z3,z22,z5])],[(0,[z0,z1,z2,z3,z409,z5,z6]),(0,[z82,z0,z1,z2,z204,z5,z6]),(0,[z410,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z411,z2,z3,z5,z6]),(0,[z0,z1,z2,z412,z3,z5,z6]),(1,[z0,z126,z127,z3,z5,z6]),(0,[z413,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z414,z5,z6]),(1,[z208,z0,z1,z134,z5,z6])],[(0,[z0,z1,z2,z3,z7,z70,z6]),(0,[z415,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z416,z2,z3,z5,z6])],[(0,[z0,z11,z1,z2,z3,z197,z5]),(0,[z0,z1,z2,z3,z417,z5,z6]),(0,[z135,z0,z1,z2,z3,z5,z8]),(1,[z0,z1,z2,z3,z346,z8])],[(0,[z418,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z168,z3,z5,z6]),(0,[z419,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z420,z5,z6])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z5,z6]),(0,[z0,z11,z1,z2,z3,z5,z23]),(0,[z0,z1,z200,z2,z3,z16,z5])],[(0,[z421,z0,z1,z2,z3,z5,z6]),(0,[z422,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z423,z3,z5,z6]),(0,[z424,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z425,z6]),(0,[z426,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z427,z6]),(0,[z0,z1,z428,z2,z3,z5,z6]),(0,[z0,z1,z75,z3,z5,z76,z6]),(0,[z0,z128,z1,z2,z3,z5,z6])],[(0,[z429,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z23]),(0,[z0,z1,z2,z3,z76,z6,z8]),(0,[z0,z1,z2,z430,z3,z5,z6])],[(0,[z196,z0,z1,z2,z3,z70,z6]),(0,[z0,z1,z431,z2,z3,z5,z6]),(0,[z0,z1,z2,z432,z3,z5,z6]),(0,[z0,z1,z2,z433,z3,z5,z6]),(0,[z434,z0,z1,z2,z3,z5,z6]),(0,[z135,z0,z1,z2,z3,z5,z6]),(0,[z0,z435,z1,z2,z3,z5,z6])],[(0,[z0,z180,z1,z2,z3,z5,z8]),(0,[z135,z0,z1,z200,z3,z5,z6])],[(0,[z436,z0,z1,z2,z3,z5,z6]),(1,[z0,z11,z1,z2,z3,z5])],[(0,[z90,z0,z1,z2,z3,z5,z8]),(0,[z437,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z438,z5,z6]),(0,[z0,z11,z1,z2,z3,z134,z5]),(0,[z31,z0,z1,z2,z3,z76,z6])],[(0,[z439,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z440,z6])]],
   [[(0,[z441,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z200,z2,z3,z333,z6])],[(0,[z0,z1,z291,z2,z3,z5,z6]),(0,[z0,z179,z2,z3,z5,z124,z6]),(0,[z33,z34,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z372,z21,z5,z6]),(0,[z0,z180,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z442,z6]),(0,[z0,z11,z1,z200,z2,z3,z5]),(0,[z0,z1,z2,z138,z3,z5,z6])],[(0,[z443,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z444,z3,z5,z6]),(0,[z445,z0,z1,z2,z3,z5,z6]),(0,[z155,z0,z1,z2,z3,z5,z8])],[(0,[z0,z1,z2,z3,z5,z446,z6]),(0,[z447,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z448,z2,z3,z5,z6]),(0,[z90,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z449,z2,z3,z5,z6]),(0,[z450,z0,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z5,z6])],[(0,[z0,z180,z2,z3,z5,z6,z23]),(0,[z451,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z452,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z153])],[(0,[z0,z453,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z454,z6]),(0,[z0,z1,z2,z3,z5,z6,z455]),(0,[z73,z0,z1,z2,z3,z5,z111]),(0,[z17,z0,z1,z2,z3,z5,z50]),(0,[z0,z1,z2,z18,z5,z6,z50])],[(0,[z0,z1,z2,z3,z456,z5,z6])],[(0,[z0,z1,z2,z457,z3,z5,z6]),(0,[z458,z0,z1,z2,z3,z5,z6]),(0,[z286,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z459,z0,z1,z2,z3,z5,z6]),(0,[z0,z460,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z266]),(0,[z0,z1,z74,z2,z3,z5,z6]),(0,[z155,z0,z1,z2,z3,z5,z6])],[(0,[z461,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z1,z127,z2,z3,z5]),(1,[z0,z1,z207,z3,z5,z6]),(0,[z462,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z463,z8])],[(1,[z0,z1,z2,z464,z5,z6]),(0,[z123,z0,z1,z2,z464,z5,z6]),(0,[z31,z0,z1,z88,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z465,z6]),(0,[z208,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z32,z6,z8]),(0,[z0,z1,z2,z3,z466,z5,z6])],[(0,[z467,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z21,z5]),(0,[z468,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z469,z2,z3,z5,z6])],[(0,[z470,z0,z1,z2,z3,z5,z6]),(0,[z471,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z173,z3,z5,z6])],[(0,[z0,z472,z1,z2,z3,z5,z6]),(1,[z0,z68,z2,z3,z5,z6]),(1,[z69,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z473,z3,z5,z6]),(0,[z474,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z138,z3,z5])],[(0,[z0,z1,z2,z3,z475,z5,z6]),(0,[z146,z0,z1,z2,z214,z5,z6]),(0,[z0,z1,z89,z127,z3,z5,z6]),(0,[z476,z0,z1,z2,z3,z5,z6]),(0,[z0,z477,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z44,z6,z8])],[(0,[z0,z1,z478,z2,z3,z5,z6]),(0,[z479,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z480,z5,z6]),(0,[z0,z1,z2,z481,z3,z5,z6]),(0,[z0,z1,z2,z3,z482,z5,z6]),(0,[z0,z1,z2,z3,z5,z463,z6])]],
   [[(0,[z0,z1,z2,z3,z483,z5,z6]),(0,[z0,z1,z2,z3,z5,z484,z6]),(0,[z227,z0,z1,z2,z3,z5,z8]),(0,[z0,z11,z126,z1,z2,z3,z5]),(0,[z208,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z485,z6])],[(0,[z0,z1,z2,z3,z486,z5,z6]),(0,[z0,z1,z2,z3,z487,z5,z6]),(1,[z0,z1,z2,z3,z485,z6])],[(0,[z0,z1,z2,z488,z3,z5,z6]),(0,[z0,z1,z2,z3,z197,z5,z6]),(0,[z489,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z490]),(0,[z155,z0,z1,z2,z3,z7,z6]),(0,[z263,z0,z1,z2,z138,z5,z6]),(0,[z0,z11,z1,z2,z491,z3,z5])],[(0,[z492,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z187,z23]),(0,[z0,z1,z2,z3,z493,z5,z6]),(0,[z494,z0,z1,z2,z3,z5,z6]),(0,[z175,z0,z1,z2,z3,z5,z8]),(0,[z0,z11,z1,z2,z372,z3,z5]),(0,[z0,z1,z200,z2,z3,z5,z153]),(0,[z0,z1,z2,z3,z495,z5,z6]),(0,[z0,z1,z2,z379,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z346,z5])],[(0,[z0,z1,z2,z496,z3,z5,z6]),(0,[z497,z0,z1,z2,z3,z5,z6]),(0,[z208,z0,z1,z3,z134,z5,z6]),(0,[z498,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z333,z6])],[(0,[z33,z0,z179,z2,z3,z5,z6]),(0,[z263,z0,z1,z2,z53,z5,z6]),(0,[z227,z0,z1,z2,z3,z5,z6]),(1,[z227,z1,z2,z3,z5,z187]),(0,[z0,z1,z2,z3,z5,z499,z6]),(0,[z0,z1,z2,z500,z3,z5,z6]),(0,[z0,z1,z2,z3,z501,z5,z6]),(0,[z0,z1,z2,z491,z3,z5,z6])],[(0,[z69,z0,z1,z292,z3,z5,z6]),(0,[z0,z1,z92,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z502,z6]),(1,[z0,z1,z2,z3,z246,z6]),(0,[z0,z1,z2,z219,z3,z5,z6]),(1,[z135,z0,z1,z3,z16,z5]),(0,[z0,z1,z2,z138,z3,z5,z93]),(0,[z0,z1,z2,z3,z503,z5,z6]),(0,[z0,z11,z1,z504,z2,z3,z5])]],
   [[(1,[z163,z1,z88,z3,z5,z6]),(1,[z106,z1,z107,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z11,z1,z2,z3,z505,z5])],[(0,[z0,z1,z2,z3,z506,z5,z6]),(0,[z0,z1,z507,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z508,z5,z6]),(0,[z509,z0,z1,z2,z3,z5,z6]),(0,[z155,z0,z1,z2,z3,z44,z6])],[(0,[z0,z1,z510,z2,z3,z5,z6]),(0,[z511,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z512,z2,z3,z5,z6]),(0,[z175,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z513]),(0,[z208,z0,z43,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z514,z5,z6]),(0,[z0,z1,z2,z39,z3,z485,z6]),(0,[z0,z11,z1,z2,z39,z3,z5])],[(0,[z0,z1,z2,z515,z3,z5,z6]),(0,[z516,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z53,z3,z5,z8]),(0,[z0,z59,z1,z2,z3,z5,z266]),(0,[z136,z0,z11,z1,z2,z3,z5])],[(0,[z0,z34,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z234,z6]),(0,[z0,z1,z2,z3,z517,z5,z6]),(0,[z0,z1,z2,z173,z3,z44,z6])],[(0,[z106,z1,z107,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z518]),(0,[z0,z1,z2,z519,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z520,z6]),(0,[z106,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z521,z6]),(0,[z522,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z523,z3,z5,z6]),(0,[z0,z1,z2,z524,z3,z5,z6]),(0,[z0,z1,z2,z138,z173,z3,z6])]],
   [[(0,[z203,z0,z1,z2,z53,z5,z6]),(0,[z0,z1,z2,z21,z134,z5,z6]),(0,[z0,z11,z41,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z525,z5,z6]),(0,[z0,z526,z1,z2,z3,z5,z6]),(0,[z0,z1,z200,z3,z5,z6,z153])],[(0,[z527,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z528,z6]),(0,[z0,z1,z2,z3,z529,z5,z6]),(0,[z0,z1,z2,z3,z5,z5,z8])],[(0,[z123,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z53,z3,z5,z6]),(0,[z69,z196,z1,z2,z3,z5,z6]),(0,[z208,z0,z74,z2,z3,z5,z6])],[(0,[z530,z0,z1,z2,z3,z5,z6]),(0,[z531,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z532,z5,z6]),(0,[z0,z1,z533,z2,z3,z5,z6]),(0,[z265,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z16,z5,z8])],[(0,[z0,z1,z2,z3,z5,z6,z534]),(0,[z0,z1,z2,z3,z5,z535,z6]),(0,[z0,z1,z504,z2,z3,z5,z6])],[(0,[z0,z1,z2,z464,z3,z5,z6]),(0,[z106,z0,z1,z2,z3,z5,z6]),(0,[z224,z0,z1,z2,z3,z111,z6]),(0,[z146,z0,z11,z1,z2,z3,z5]),(0,[z175,z0,z1,z2,z3,z7,z6]),(0,[z0,z180,z1,z2,z3,z5,z23]),(0,[z263,z0,z1,z2,z3,z5,z8])],[(0,[z0,z11,z1,z2,z42,z3,z5])],[(0,[z0,z1,z107,z42,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z0,z1,z2,z536,z3,z5,z6])]],
   [[(0,[z33,z0,z11,z1,z2,z3,z5]),(0,[z0,z11,z1,z2,z3,z5,z187]),(0,[z0,z1,z2,z537,z3,z5,z6]),(0,[z0,z1,z2,z3,z538,z5,z6])],[(0,[z31,z0,z11,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z16,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z539]),(0,[z0,z1,z2,z3,z540,z5,z6]),(0,[z0,z1,z2,z3,z279,z5,z6]),(0,[z0,z1,z2,z541,z3,z5,z6]),(1,[z0,z1,z200,z3,z5,z153]),(0,[z0,z1,z542,z2,z3,z5,z6])],[(0,[z155,z196,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z187]),(0,[z0,z1,z2,z214,z3,z5,z6]),(0,[z0,z1,z2,z3,z246,z5,z6]),(0,[z155,z0,z1,z2,z3,z76,z6]),(0,[z0,z1,z2,z3,z5,z543,z6]),(0,[z263,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z544,z6])],[(0,[z0,z1,z179,z2,z3,z5,z8]),(0,[z0,z545,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z546,z6]),(0,[z0,z1,z2,z547,z3,z5,z6]),(0,[z0,z43,z1,z2,z3,z5,z6]),(0,[z0,z1,z372,z3,z134,z5,z6]),(1,[z133,z0,z1,z2,z3,z5]),(0,[z0,z548,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z39,z3,z5,z8])],[(0,[z0,z1,z107,z3,z5,z76,z6]),(0,[z0,z1,z2,z3,z549,z5,z6]),(0,[z550,z0,z1,z2,z3,z5,z6])],[(0,[z551,z0,z1,z2,z3,z5,z6]),(0,[z552,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z165,z2,z3,z5,z6]),(0,[z0,z1,z75,z2,z3,z5,z8])],[(0,[z553,z0,z1,z2,z3,z5,z6]),(0,[z203,z0,z1,z2,z3,z5,z8]),(0,[z227,z0,z1,z2,z3,z5,z111]),(0,[z0,z1,z2,z3,z554,z5,z6]),(0,[z0,z1,z2,z3,z5,z555,z6]),(1,[z17,z0,z1,z2,z18,z5])]],
   [[(0,[z69,z0,z1,z2,z3,z5,z352]),(0,[z556,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z557,z3,z5,z6])],[(0,[z69,z0,z1,z2,z3,z197,z6]),(0,[z558,z0,z1,z2,z3,z5,z6]),(0,[z0,z559,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z560,z5,z6]),(0,[z561,z0,z1,z2,z3,z5,z6]),(0,[z208,z0,z1,z2,z134,z5,z6]),(0,[z0,z1,z2,z178,z3,z5,z6])],[(0,[z0,z1,z179,z2,z3,z5,z6]),(0,[z0,z1,z42,z3,z134,z5,z6]),(0,[z0,z1,z2,z3,z562,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z109]),(0,[z0,z1,z2,z3,z5,z44,z8])],[(0,[z0,z563,z1,z2,z3,z5,z6]),(0,[z69,z1,z2,z3,z5,z70,z6]),(0,[z0,z564,z1,z2,z3,z5,z6])],[(0,[z565,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z566,z6]),(0,[z0,z1,z75,z2,z3,z5,z6]),(1,[z0,z1,z2,z379,z3,z5])],[(0,[z0,z1,z2,z88,z3,z5,z8]),(0,[z203,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z567,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z568,z6]),(0,[z0,z1,z569,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z570,z5,z6]),(0,[z0,z1,z2,z571,z3,z5,z6])],[(0,[z0,z1,z2,z572,z3,z5,z6]),(0,[z573,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z574,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z575])],[(0,[z576,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z88,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z577]),(0,[z0,z1,z89,z2,z372,z5,z6]),(0,[z0,z1,z2,z3,z578,z5,z6]),(0,[z0,z1,z2,z579,z3,z5,z6])]],
   [[(0,[z0,z1,z292,z2,z3,z5,z6]),(0,[z0,z126,z1,z2,z3,z5,z6]),(0,[z580,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z581,z3,z5,z6]),(0,[z181,z0,z2,z3,z22,z5,z6])],[(0,[z69,z0,z1,z2,z3,z5,z151])],[(0,[z123,z0,z1,z2,z3,z5,z72]),(1,[z196,z1,z2,z3,z197,z6]),(0,[z196,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z582,z5,z6]),(0,[z0,z583,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z88,z3,z5,z6]),(0,[z31,z0,z1,z107,z3,z5,z6]),(0,[z0,z36,z1,z2,z3,z5,z6]),(0,[z135,z17,z0,z1,z2,z3,z5])],[(0,[z584,z0,z1,z2,z3,z5,z6]),(0,[z0,z585,z1,z2,z3,z5,z6]),(0,[z0,z1,z586,z2,z3,z5,z6]),(0,[z0,z1,z2,z587,z3,z5,z6]),(0,[z181,z0,z11,z1,z2,z3,z5]),(0,[z588,z0,z1,z2,z3,z5,z6]),(0,[z263,z0,z1,z2,z3,z44,z6]),(0,[z17,z0,z1,z2,z39,z5,z6]),(0,[z0,z589,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z590]),(0,[z163,z0,z1,z107,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z591]),(1,[z0,z1,z2,z173,z44,z6])],[(0,[z0,z1,z2,z3,z5,z6,z592]),(0,[z0,z1,z593,z2,z3,z5,z6])],[(0,[z34,z1,z179,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z594]),(0,[z595,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z596,z3,z5,z6]),(1,[z0,z1,z2,z3,z32,z8]),(0,[z0,z1,z200,z2,z3,z597,z6]),(0,[z17,z0,z1,z2,z18,z3,z5]),(0,[z0,z1,z2,z598,z3,z5,z8])]],
   [[(0,[z175,z0,z34,z2,z3,z5,z6]),(0,[z196,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z599,z2,z3,z5,z6]),(0,[z0,z1,z2,z600,z3,z5,z6]),(0,[z0,z1,z2,z601,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z8])],[(0,[z73,z227,z1,z2,z3,z5,z6]),(0,[z0,z126,z1,z127,z3,z5,z6]),(0,[z0,z1,z127,z2,z3,z5,z8]),(0,[z0,z1,z2,z602,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z603]),(0,[z0,z1,z604,z2,z3,z5,z6])],[(0,[z73,z0,z1,z2,z3,z5,z187]),(0,[z208,z0,z1,z2,z372,z5,z6])],[(0,[z0,z1,z605,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z21,z5,z8]),(0,[z155,z0,z1,z2,z3,z124,z6]),(0,[z0,z1,z2,z606,z3,z5,z6]),(0,[z135,z0,z1,z2,z39,z3,z5]),(0,[z0,z1,z139,z2,z3,z5,z8]),(1,[z0,z11,z1,z2,z3,z8])],[(0,[z0,z1,z2,z3,z607,z5,z6]),(0,[z0,z1,z2,z3,z5,z76,z8])],[(0,[z0,z1,z2,z608,z3,z5,z6]),(1,[z196,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z3,z5,z609,z6]),(0,[z0,z610,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z611,z5,z6]),(0,[z0,z1,z612,z2,z3,z5,z6]),(0,[z0,z1,z2,z598,z3,z5,z6])],[(0,[z0,z613,z1,z2,z3,z5,z6]),(0,[z614,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z615,z5,z6]),(0,[z0,z616,z1,z2,z3,z5,z6])],[(0,[z0,z1,z127,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z8,z50])],[(0,[z0,z1,z2,z391,z3,z5,z6]),(0,[z0,z1,z2,z3,z21,z5,z6]),(0,[z0,z1,z2,z3,z5,z617,z6]),(0,[z367,z0,z1,z2,z3,z5,z8])],[(0,[z618,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z619,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z76,z6])],[(1,[z123,z179,z2,z3,z5,z6]),(0,[z0,z1,z620,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z352,z6]),(0,[z0,z1,z2,z3,z621,z5,z6]),(0,[z622,z0,z1,z2,z3,z5,z6])],[(0,[z69,z0,z1,z168,z3,z5,z6]),(0,[z0,z1,z127,z3,z134,z5,z6]),(0,[z623,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z138,z3,z269,z5]),(0,[z0,z1,z2,z3,z5,z8,z518]),(0,[z0,z11,z277,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z624,z5,z6]),(1,[z69,z1,z2,z3,z70,z6]),(0,[z0,z1,z2,z3,z197,z124,z6]),(0,[z0,z1,z2,z3,z625,z5,z6]),(0,[z0,z1,z2,z3,z626,z5,z6])],[(0,[z123,z0,z34,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z627,z5,z6]),(0,[z628,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z111,z6,z187]),(0,[z0,z1,z2,z3,z629,z5,z6])],[(0,[z367,z0,z1,z2,z3,z5,z6]),(0,[z123,z33,z1,z2,z3,z5,z6]),(0,[z163,z0,z1,z88,z3,z5,z6]),(0,[z0,z1,z2,z630,z3,z5,z6]),(0,[z263,z0,z1,z2,z204,z5,z6]),(0,[z0,z1,z2,z3,z5,z631,z6]),(0,[z0,z1,z632,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z247])]],
   [[(0,[z0,z1,z2,z633,z3,z5,z6]),(0,[z0,z1,z2,z3,z111,z205,z6]),(0,[z0,z634,z1,z2,z3,z5,z6]),(0,[z0,z1,z200,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z635,z6]),(0,[z0,z1,z2,z636,z3,z5,z6]),(0,[z443,z0,z11,z1,z2,z3,z5])],[(1,[z0,z1,z2,z159,z5,z6]),(0,[z123,z0,z1,z2,z159,z5,z6]),(0,[z637,z0,z1,z2,z3,z5,z6]),(0,[z0,z638,z1,z2,z3,z5,z6]),(0,[z639,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z75,z2,z3,z32,z6]),(0,[z0,z1,z2,z3,z80,z5,z6]),(0,[z17,z0,z11,z1,z2,z3,z5]),(0,[z0,z11,z1,z2,z18,z3,z5])],[(0,[z0,z1,z2,z3,z197,z5,z244]),(0,[z640,z0,z1,z2,z3,z5,z6]),(0,[z146,z0,z1,z42,z3,z5,z6]),(0,[z641,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z597,z5,z6]),(0,[z0,z1,z2,z3,z642,z5,z6])],[(0,[z203,z1,z2,z3,z204,z5,z6]),(0,[z69,z0,z11,z1,z2,z3,z5]),(0,[z643,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z5,z109]),(0,[z644,z0,z1,z2,z3,z5,z6])],[(0,[z0,z645,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z646,z5,z6]),(0,[z0,z1,z2,z3,z5,z647,z6]),(1,[z0,z1,z2,z3,z597,z6])],[(0,[z648,z0,z1,z2,z3,z5,z6]),(0,[z146,z0,z126,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z649,z6]),(0,[z0,z1,z2,z3,z650,z5,z6]),(0,[z0,z651,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z652,z5,z6]),(0,[z653,z0,z1,z2,z3,z5,z8])],[(0,[z90,z0,z2,z3,z21,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z104]),(0,[z0,z1,z200,z2,z3,z5,z6]),(0,[z0,z654,z1,z2,z3,z5,z6])],[(0,[z0,z1,z3,z32,z5,z76,z6])]],
   [[(0,[z655,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z244]),(0,[z0,z656,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z657,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z658,z6]),(0,[z203,z0,z1,z2,z204,z5,z6])],[(0,[z659,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z660,z5,z6]),(0,[z0,z1,z2,z3,z661,z5,z6]),(0,[z135,z0,z1,z3,z16,z5,z6]),(0,[z0,z1,z662,z2,z3,z5,z6])],[(0,[z0,z1,z663,z2,z3,z5,z6]),(0,[z653,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z664,z5,z6]),(0,[z0,z2,z3,z7,z5,z124,z6]),(0,[z665,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z505,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z666]),(0,[z0,z1,z2,z3,z5,z667,z6]),(0,[z0,z1,z2,z3,z5,z124,z8]),(0,[z0,z1,z2,z3,z5,z6,z668]),(0,[z0,z1,z2,z3,z32,z5,z8]),(0,[z0,z1,z2,z669,z3,z5,z8])],[(0,[z670,z0,z1,z2,z3,z5,z6]),(0,[z0,z36,z1,z2,z3,z197,z5]),(0,[z175,z0,z2,z3,z7,z5,z6]),(0,[z0,z1,z2,z3,z5,z671,z6])],[(0,[z82,z0,z11,z1,z2,z3,z5]),(0,[z0,z1,z2,z672,z3,z5,z6]),(0,[z673,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z89,z372,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z402])],[(0,[z0,z1,z2,z3,z674,z5,z6]),(0,[z0,z11,z1,z2,z20,z3,z5]),(0,[z133,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z372,z3,z5,z8]),(0,[z0,z11,z1,z2,z3,z32,z5])]],
   [[(0,[z0,z11,z1,z107,z2,z3,z5]),(0,[z675,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z262])],[],[(0,[z1,z107,z2,z88,z3,z5,z6]),(0,[z1,z2,z3,z197,z5,z70,z6]),(0,[z0,z41,z1,z2,z20,z5,z6]),(0,[z676,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z124,z6]),(0,[z0,z180,z1,z2,z3,z121,z6]),(0,[z0,z1,z2,z3,z32,z5,z6]),(0,[z0,z1,z2,z677,z3,z5,z6]),(0,[z0,z1,z2,z669,z3,z5,z6]),(0,[z494,z0,z11,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z678,z5,z6]),(0,[z0,z1,z107,z2,z3,z5,z8]),(0,[z0,z41,z126,z2,z3,z5,z6]),(0,[z679,z0,z1,z2,z3,z5,z6]),(0,[z680,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z11,z1,z2,z3,z5])],[(0,[z69,z0,z68,z2,z3,z5,z6]),(0,[z681,z0,z1,z2,z3,z5,z6])],[(0,[z163,z1,z2,z88,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z197,z6]),(0,[z0,z1,z2,z3,z5,z682,z6]),(0,[z0,z1,z2,z3,z683,z5,z6]),(0,[z0,z1,z2,z372,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z8])],[(0,[z684,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z685,z3,z5,z6])],[(0,[z0,z1,z2,z686,z3,z5,z6]),(0,[z0,z1,z2,z207,z3,z5,z6]),(0,[z0,z1,z2,z3,z687,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z688,z5,z6]),(0,[z146,z0,z2,z42,z3,z5,z6]),(1,[z155,z0,z11,z1,z2,z3])],[(0,[z0,z1,z2,z3,z5,z6,z689]),(0,[z0,z1,z2,z690,z3,z5,z6])],[(0,[z691,z0,z1,z2,z3,z5,z6]),(0,[z69,z0,z1,z2,z3,z6,z8]),(0,[z0,z692,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z23]),(0,[z0,z1,z2,z3,z5,z6,z693]),(0,[z0,z694,z1,z2,z3,z5,z6]),(0,[z0,z354,z11,z1,z2,z3,z5])],[(0,[z123,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z695,z3,z5,z6]),(0,[z696,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z697,z3,z5,z6]),(0,[z0,z1,z698,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z5,z44])],[(0,[z227,z0,z1,z2,z3,z5,z187]),(0,[z699,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z700,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z701]),(0,[z0,z702,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z703,z5,z6])],[],[(0,[z163,z0,z11,z1,z2,z3,z5]),(1,[z0,z1,z2,z95,z5,z6]),(0,[z0,z1,z2,z704,z3,z5,z6]),(0,[z0,z1,z2,z3,z705,z5,z6])],[(0,[z0,z1,z706,z2,z3,z5,z6]),(0,[z175,z0,z59,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z40,z5,z8]),(0,[z0,z361,z11,z1,z2,z3,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z470,z0,z2,z21,z5,z6]),(0,[z0,z1,z2,z3,z661,z8])],[(0,[z0,z1,z2,z3,z5,z707]),(0,[z0,z1,z2,z3,z631,z8]),(0,[z0,z1,z2,z3,z5,z708])],[(0,[z0,z1,z2,z3,z709,z6]),(0,[z0,z1,z2,z3,z5,z710]),(0,[z0,z1,z2,z598,z5,z402])],[(0,[z0,z11,z68,z2,z3,z5]),(0,[z0,z1,z2,z39,z485,z50])],[(0,[z711,z0,z1,z3,z5,z6]),(0,[z245,z1,z2,z53,z5,z6]),(0,[z69,z1,z2,z3,z70,z6]),(0,[z90,z0,z2,z712,z5,z6]),(0,[z0,z1,z2,z3,z5,z713]),(0,[z0,z1,z2,z3,z714,z5])],[(0,[z0,z1,z2,z3,z484,z8]),(1,[z0,z1,z168,z3,z8]),(0,[z0,z1,z2,z3,z715,z5]),(0,[z90,z0,z92,z21,z5,z6]),(0,[z0,z1,z2,z716,z3,z5]),(0,[z0,z11,z1,z2,z96,z3])],[(0,[z69,z0,z1,z2,z95,z8]),(0,[z0,z1,z2,z3,z647,z8]),(0,[z0,z1,z2,z669,z44,z8])],[(0,[z332,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z3,z274,z8]),(0,[z0,z717,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z718]),(0,[z0,z1,z2,z3,z719,z5]),(0,[z56,z0,z1,z2,z505,z5])]],
   [[(0,[z0,z1,z2,z159,z5,z6]),(0,[z0,z11,z1,z2,z3,z323]),(0,[z0,z1,z165,z2,z3,z5]),(0,[z0,z1,z200,z3,z719,z5])],[(0,[z0,z720,z2,z3,z5,z6]),(0,[z0,z1,z2,z184,z5,z8]),(0,[z721,z1,z2,z3,z5,z6]),(0,[z0,z361,z1,z2,z3,z485])],[(0,[z0,z1,z2,z3,z393,z8]),(0,[z1,z2,z722,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z723]),(0,[z69,z196,z1,z2,z3,z8]),(0,[z155,z0,z1,z2,z99,z6]),(0,[z69,z0,z1,z2,z3,z244]),(0,[z196,z11,z1,z2,z3,z197])],[],[(0,[z0,z1,z2,z61,z44,z6]),(0,[z0,z1,z2,z724,z3,z5]),(0,[z0,z59,z2,z3,z124,z266]),(0,[z0,z1,z2,z3,z502,z8])],[(0,[z0,z1,z725,z3,z5,z6]),(0,[z0,z180,z2,z3,z5,z23]),(0,[z0,z1,z2,z3,z578,z8])],[(0,[z0,z726,z2,z3,z5,z6]),(0,[z0,z1,z727,z3,z5,z6]),(0,[z0,z1,z2,z204,z44,z8]),(0,[z0,z1,z75,z3,z728,z6])],[(0,[z0,z11,z1,z2,z159,z5]),(0,[z729,z0,z1,z2,z5,z6]),(0,[z681,z1,z107,z3,z5,z6]),(0,[z0,z1,z2,z61,z3,z8]),(0,[z0,z1,z2,z184,z5,z6])]],
   [[(0,[z0,z1,z510,z2,z3,z8]),(0,[z0,z102,z2,z99,z5,z6]),(0,[z0,z1,z2,z214,z5,z8]),(0,[z0,z2,z3,z730,z5,z6])],[(0,[z0,z731,z1,z2,z3,z5]),(0,[z0,z453,z2,z3,z124,z6]),(0,[z732,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z733,z6]),(0,[z0,z1,z2,z3,z611,z8])],[(0,[z0,z1,z2,z3,z734,z6]),(0,[z0,z74,z2,z134,z5,z6]),(0,[z735,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z736,z3,z5])],[(0,[z0,z1,z2,z737,z5,z6]),(0,[z0,z1,z2,z3,z738,z6]),(0,[z135,z0,z1,z3,z719,z5])],[(1,[z739,z2,z3,z5,z6]),(0,[z0,z1,z740,z3,z5,z6]),(0,[z69,z0,z68,z2,z3,z8]),(0,[z0,z1,z2,z3,z124,z8]),(0,[z0,z1,z2,z741,z3,z5])],[(0,[z0,z1,z742,z3,z5,z6]),(0,[z0,z1,z2,z3,z213,z8]),(0,[z0,z1,z2,z138,z44,z8]),(0,[z0,z1,z2,z743,z5,z6]),(0,[z0,z744,z2,z3,z5,z8])],[(0,[z0,z1,z291,z464,z5,z6]),(0,[z0,z1,z2,z3,z745,z6]),(0,[z0,z1,z2,z746,z5,z6])],[(0,[z0,z1,z2,z3,z44,z247]),(0,[z0,z1,z2,z743,z5,z50]),(0,[z0,z11,z1,z2,z162,z3])]],
   [[(0,[z0,z1,z2,z53,z44,z8]),(0,[z0,z1,z2,z3,z660,z8]),(0,[z494,z0,z504,z2,z3,z5])],[(0,[z0,z68,z292,z3,z5,z6]),(0,[z0,z1,z2,z747,z5,z6]),(0,[z0,z1,z3,z748,z5,z8])],[(0,[z0,z1,z2,z3,z749,z6]),(0,[z0,z1,z2,z3,z5,z750]),(0,[z0,z1,z168,z3,z5,z352])],[(0,[z0,z1,z2,z3,z5,z751]),(0,[z0,z656,z2,z3,z5,z23]),(0,[z0,z1,z2,z752,z5,z6]),(0,[z753,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z754,z3,z32])],[(0,[z123,z179,z2,z3,z100,z6]),(0,[z0,z1,z2,z3,z755,z6]),(0,[z69,z1,z2,z99,z70,z6]),(0,[z1,z2,z3,z756,z70,z6]),(0,[z0,z634,z1,z2,z3,z8]),(0,[z0,z1,z139,z3,z5,z153]),(0,[z0,z1,z2,z636,z3,z8])],[(0,[z757,z1,z2,z3,z5,z6]),(0,[z136,z443,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z758,z6]),(0,[z0,z1,z2,z3,z5,z759]),(0,[z760,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z754,z3,z5])],[(0,[z0,z1,z2,z3,z728,z6]),(0,[z0,z1,z3,z748,z5,z6])]],
   [[(0,[z0,z1,z761,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z762]),(0,[z0,z1,z2,z363,z3,z8])],[(0,[z0,z1,z2,z763,z5,z6]),(0,[z0,z1,z2,z3,z764,z6]),(0,[z25,z1,z2,z53,z5,z6]),(0,[z0,z11,z1,z2,z3,z646]),(1,[z1,z2,z3,z5,z765]),(0,[z0,z1,z200,z491,z3,z5])],[],[(0,[z0,z1,z2,z3,z766,z6]),(0,[z0,z1,z168,z3,z5,z151]),(0,[z239,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z3,z687,z8])],[(0,[z739,z179,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z13,z8])],[(0,[z163,z11,z1,z88,z3,z5]),(0,[z767,z1,z2,z3,z5,z6]),(0,[z90,z0,z207,z21,z5,z6]),(0,[z208,z133,z0,z1,z134,z5]),(0,[z0,z1,z2,z743,z3,z5])],[(0,[z0,z1,z2,z159,z5,z45]),(0,[z0,z1,z2,z3,z5,z768]),(0,[z0,z1,z769,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z770]),(0,[z0,z1,z2,z18,z3,z485])],[(0,[z0,z1,z2,z771,z5,z6]),(0,[z0,z449,z2,z3,z124,z6]),(0,[z0,z43,z2,z3,z5,z8]),(0,[z208,z0,z43,z134,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z772,z6]),(0,[z0,z1,z773,z2,z3,z8])],[(0,[z0,z1,z291,z3,z234,z6]),(0,[z0,z1,z2,z3,z267,z5]),(0,[z0,z1,z2,z3,z80,z5])],[(0,[z445,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z743,z39,z5])],[(0,[z1,z2,z3,z774,z5,z6]),(0,[z0,z126,z586,z3,z5,z6]),(0,[z0,z2,z3,z775,z5,z6]),(0,[z0,z128,z1,z2,z3,z333])],[(0,[z33,z34,z2,z3,z5,z6]),(0,[z776,z0,z2,z3,z5,z6]),(0,[z0,z36,z1,z2,z3,z5]),(0,[z146,z0,z11,z42,z3,z5]),(0,[z0,z11,z1,z2,z3,z246])],[(0,[z0,z777,z1,z2,z3,z6]),(0,[z0,z1,z2,z778,z3,z6]),(0,[z0,z1,z2,z168,z3,z8]),(0,[z0,z43,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z44,z8])],[(0,[z0,z779,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z780]),(0,[z0,z1,z2,z14,z3,z8]),(0,[z0,z74,z2,z3,z5,z8]),(0,[z0,z1,z2,z219,z3,z5]),(0,[z0,z1,z75,z3,z76,z8]),(0,[z155,z0,z1,z2,z219,z3])],[(0,[z163,z1,z722,z3,z5,z6]),(0,[z227,z131,z1,z2,z3,z5]),(0,[z0,z2,z207,z21,z5,z6]),(0,[z0,z1,z2,z781,z3,z5]),(0,[z0,z1,z2,z3,z279,z5]),(0,[z0,z1,z2,z3,z60,z8])]],
   [[(0,[z0,z1,z2,z464,z234,z6]),(0,[z0,z1,z782,z3,z5,z6]),(0,[z0,z1,z2,z3,z79,z8])],[(0,[z0,z1,z2,z3,z5,z783]),(0,[z0,z1,z2,z3,z5,z784]),(0,[z196,z1,z2,z3,z197,z244]),(0,[z0,z1,z2,z3,z83,z8])],[(0,[z0,z1,z2,z3,z27,z8]),(0,[z0,z68,z2,z3,z5,z352]),(0,[z0,z1,z2,z785,z5,z6]),(0,[z0,z1,z3,z719,z5,z153]),(0,[z0,z1,z12,z3,z16,z5])],[(0,[z0,z1,z786,z3,z5,z6]),(0,[z47,z0,z1,z2,z3,z205]),(0,[z17,z0,z1,z2,z3,z333]),(0,[z0,z1,z2,z96,z3,z8]),(0,[z334,z0,z1,z2,z3,z8])],[(0,[z0,z1,z2,z3,z5,z787]),(0,[z0,z1,z2,z3,z788,z5]),(0,[z0,z789,z1,z2,z3,z5]),(0,[z0,z11,z1,z292,z3,z5]),(0,[z0,z74,z2,z3,z5,z6]),(0,[z0,z1,z75,z3,z76,z6])],[(0,[z73,z1,z2,z3,z111,z205])],[(0,[z0,z1,z2,z3,z100,z8]),(0,[z135,z0,z1,z601,z3,z5])],[(0,[z0,z1,z2,z790,z5,z6]),(0,[z0,z1,z292,z95,z5,z6]),(0,[z73,z0,z1,z2,z3,z205]),(0,[z0,z1,z75,z3,z80,z76]),(0,[z0,z396,z1,z2,z3,z8])]],
   [[(0,[z0,z1,z2,z3,z5,z791]),(0,[z0,z1,z792,z3,z5,z6]),(0,[z0,z1,z793,z3,z5,z6]),(0,[z0,z1,z794,z3,z5,z6]),(0,[z0,z1,z2,z3,z414,z8]),(0,[z0,z1,z2,z598,z44,z8]),(0,[z0,z11,z1,z2,z3,z485])],[(0,[z0,z74,z3,z134,z5,z6]),(0,[z0,z1,z2,z96,z3,z6])],[(0,[z0,z34,z2,z3,z124,z8]),(0,[z0,z1,z2,z3,z117,z8]),(0,[z0,z1,z2,z99,z5,z6]),(0,[z0,z127,z795,z3,z5,z6]),(0,[z0,z1,z2,z3,z121,z8])],[(0,[z0,z1,z2,z3,z796,z5]),(0,[z82,z1,z2,z53,z5,z8])],[(0,[z0,z1,z2,z3,z5,z109]),(0,[z0,z797,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z417,z8])],[(0,[z0,z1,z2,z798,z3,z6]),(0,[z799,z1,z2,z3,z5,z6]),(0,[z0,z1,z207,z20,z5,z6]),(0,[z0,z1,z800,z3,z5,z6])],[(0,[z0,z1,z2,z3,z801,z6]),(0,[z0,z1,z2,z802,z3,z5]),(0,[z0,z1,z2,z3,z5,z803]),(0,[z0,z1,z2,z598,z44,z6]),(0,[z155,z0,z1,z2,z3,z269])],[(0,[z0,z1,z2,z3,z804,z6]),(0,[z0,z1,z805,z2,z3,z6]),(0,[z90,z0,z11,z2,z21,z5]),(0,[z0,z1,z2,z3,z76,z8])]],
   [[(0,[z0,z1,z2,z3,z806,z6]),(0,[z807,z0,z1,z2,z3,z5]),(0,[z82,z11,z1,z2,z53,z5]),(0,[z0,z1,z2,z360,z3,z8]),(0,[z0,z1,z2,z3,z121,z6]),(0,[z0,z11,z1,z2,z3,z333]),(0,[z0,z1,z2,z96,z39,z50])],[(0,[z0,z1,z391,z464,z5,z6]),(0,[z0,z739,z2,z3,z5,z6]),(0,[z98,z0,z1,z2,z3,z8]),(0,[z82,z1,z2,z53,z5,z6]),(0,[z0,z1,z2,z808,z5,z8]),(0,[z0,z1,z2,z809,z5,z8])],[(0,[z203,z1,z2,z774,z5,z6]),(1,[z0,z1,z2,z99,z8]),(0,[z1,z2,z3,z5,z765,z187]),(0,[z0,z1,z810,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z811])],[],[(0,[z0,z1,z2,z812,z5,z6]),(0,[z0,z1,z2,z3,z813,z8]),(0,[z0,z1,z2,z3,z157,z8]),(0,[z210,z1,z2,z3,z5,z248])],[(0,[z0,z220,z2,z3,z124,z6]),(0,[z69,z0,z1,z292,z3,z8]),(0,[z224,z0,z11,z1,z2,z3]),(0,[z0,z11,z1,z2,z173,z44]),(0,[z0,z1,z2,z814,z5,z8])],[(0,[z0,z1,z2,z3,z100,z815]),(0,[z0,z1,z2,z816,z3,z6])],[(0,[z0,z2,z3,z817,z5,z6]),(0,[z0,z1,z2,z808,z5,z6]),(0,[z0,z1,z2,z809,z5,z6])]],
   [[(0,[z0,z818,z1,z2,z3,z6]),(0,[z0,z1,z507,z2,z3,z8]),(0,[z819,z0,z1,z2,z3,z5]),(0,[z0,z1,z200,z3,z333,z153])],[(0,[z0,z11,z1,z168,z3,z5]),(0,[z0,z1,z820,z3,z5,z6]),(0,[z0,z11,z41,z2,z20,z5]),(0,[z0,z1,z2,z821,z5,z6])],[(0,[z558,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z3,z649,z8]),(0,[z17,z0,z1,z2,z420,z5])],[(0,[z0,z1,z2,z3,z5,z822]),(0,[z31,z0,z1,z3,z368,z6]),(0,[z0,z1,z2,z3,z756,z6]),(0,[z0,z2,z3,z730,z124,z6]),(0,[z0,z1,z2,z3,z309,z8]),(0,[z0,z1,z2,z138,z3,z247])],[(0,[z0,z1,z2,z3,z823,z6]),(0,[z0,z1,z2,z3,z99,z8]),(0,[z824,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z825]),(0,[z0,z1,z2,z3,z525,z8]),(0,[z0,z1,z2,z3,z182,z8])],[(0,[z0,z102,z292,z3,z5,z6]),(0,[z826,z1,z2,z3,z5,z6])],[(0,[z0,z1,z827,z3,z5,z6]),(0,[z0,z1,z2,z3,z100,z72]),(0,[z0,z1,z2,z3,z828,z6]),(0,[z0,z68,z168,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z765]),(0,[z0,z41,z207,z3,z5,z6]),(0,[z0,z1,z2,z3,z829,z6])],[(0,[z0,z1,z2,z830,z5,z6]),(0,[z0,z1,z165,z2,z3,z8]),(0,[z0,z2,z3,z775,z5,z23]),(0,[z0,z1,z2,z3,z16,z333])]],
   [[(0,[z0,z1,z2,z3,z5,z831]),(0,[z0,z1,z2,z95,z5,z352]),(0,[z146,z0,z42,z3,z5,z8]),(0,[z0,z1,z2,z3,z832,z6])],[(0,[z0,z1,z833,z3,z5,z6]),(0,[z0,z1,z2,z834,z5,z6]),(0,[z203,z1,z2,z204,z5,z8]),(0,[z0,z1,z2,z3,z201,z8])],[(0,[z0,z1,z2,z835,z5,z6]),(0,[z0,z1,z2,z3,z205,z8]),(0,[z0,z1,z2,z3,z5,z836])],[(0,[z0,z837,z1,z2,z3,z6]),(0,[z441,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z3,z5,z838]),(0,[z0,z1,z2,z839,z3,z6]),(0,[z0,z1,z2,z840,z5,z8])],[(0,[z0,z1,z391,z3,z234,z6]),(0,[z0,z220,z1,z2,z3,z8]),(0,[z0,z387,z1,z2,z3,z8]),(0,[z0,z1,z168,z3,z6,z8]),(0,[z0,z1,z2,z3,z5,z841])],[(0,[z0,z1,z2,z3,z842,z6]),(0,[z0,z1,z2,z3,z215,z8]),(0,[z0,z1,z2,z3,z216,z8])],[(0,[z310,z1,z107,z3,z5,z6]),(0,[z146,z0,z42,z3,z5,z6]),(0,[z175,z0,z165,z2,z3,z7]),(0,[z175,z0,z2,z3,z7,z8])],[(0,[z123,z179,z291,z3,z5,z6]),(0,[z203,z1,z2,z204,z5,z6]),(0,[z224,z0,z1,z2,z3,z8]),(0,[z0,z1,z92,z3,z5,z8]),(0,[z0,z1,z843,z3,z5,z6]),(0,[z0,z2,z3,z7,z124,z8]),(0,[z0,z1,z2,z3,z562,z8]),(0,[z844,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z845])]],
   [[(0,[z175,z0,z11,z2,z3,z7])],[(0,[z0,z1,z391,z3,z5,z8]),(0,[z69,z1,z292,z3,z70,z6]),(0,[z0,z1,z2,z95,z5,z151]),(0,[z227,z0,z1,z2,z3,z205]),(0,[z0,z1,z2,z214,z5,z6]),(0,[z0,z1,z3,z785,z5,z6]),(0,[z846,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z840,z5,z6])],[(0,[z0,z1,z2,z3,z5,z847]),(0,[z0,z1,z2,z3,z5,z848]),(0,[z655,z0,z1,z2,z3,z8]),(0,[z69,z0,z1,z168,z3,z8])],[(0,[z0,z1,z2,z849,z5,z6]),(0,[z0,z1,z127,z184,z5,z6]),(0,[z0,z288,z127,z3,z5,z6]),(0,[z0,z850,z2,z3,z5,z6])],[(0,[z0,z851,z2,z3,z5,z6]),(0,[z0,z1,z207,z21,z5,z6]),(0,[z175,z0,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z452,z8])],[(0,[z0,z1,z291,z159,z5,z6]),(0,[z224,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z852,z6]),(0,[z0,z1,z2,z3,z5,z853]),(0,[z0,z1,z2,z39,z113,z5]),(0,[z0,z1,z2,z39,z5,z50])],[(0,[z123,z179,z2,z464,z5,z6]),(0,[z0,z1,z2,z3,z5,z854]),(0,[z0,z1,z2,z3,z5,z855]),(0,[z0,z1,z2,z856,z5,z6]),(0,[z857,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z540,z8]),(0,[z0,z1,z2,z314,z3,z8]),(0,[z0,z744,z2,z3,z5,z6]),(0,[z858,z0,z1,z2,z5,z6])],[(0,[z0,z1,z859,z3,z5,z6]),(0,[z146,z0,z795,z3,z5,z6]),(1,[z0,z207,z21,z5,z6])]],
   [[(0,[z208,z0,z1,z134,z5,z8]),(0,[z0,z1,z2,z3,z5,z860])],[(0,[z0,z1,z2,z138,z3,z8])],[(0,[z0,z34,z2,z3,z100,z6]),(0,[z0,z11,z1,z291,z3,z5]),(0,[z0,z1,z2,z861,z5,z6]),(0,[z0,z1,z2,z3,z5,z244]),(0,[z155,z0,z1,z2,z3,z352]),(0,[z0,z11,z1,z2,z3,z205]),(0,[z862,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z863,z5]),(0,[z321,z34,z2,z3,z5,z6]),(0,[z69,z68,z2,z3,z70,z6]),(0,[z239,z1,z2,z3,z70,z6]),(0,[z0,z1,z2,z864,z5,z6]),(0,[z865,z0,z1,z3,z5,z6]),(0,[z0,z11,z1,z2,z3,z121]),(1,[z0,z1,z2,z743,z5])],[(0,[z0,z11,z1,z2,z464,z5]),(0,[z0,z1,z2,z3,z866,z6]),(0,[z0,z1,z2,z3,z5,z867]),(0,[z0,z868,z2,z3,z5,z6]),(0,[z196,z1,z2,z3,z463,z8]),(0,[z0,z1,z869,z3,z5,z6]),(0,[z0,z1,z2,z3,z121,z23])],[(0,[z0,z1,z2,z159,z100,z6]),(0,[z82,z1,z2,z774,z5,z6]),(0,[z0,z1,z2,z3,z870,z6]),(0,[z0,z871,z1,z2,z3,z5]),(0,[z0,z1,z2,z754,z3,z8]),(0,[z0,z872,z1,z2,z3,z5])],[(0,[z0,z102,z2,z3,z5,z352]),(0,[z0,z1,z2,z3,z5,z873]),(0,[z0,z74,z2,z372,z5,z6]),(0,[z208,z0,z1,z134,z5,z6])],[(0,[z0,z1,z2,z874,z5,z6]),(0,[z0,z1,z2,z3,z5,z875]),(0,[z0,z1,z2,z3,z876,z6]),(0,[z0,z102,z2,z3,z197,z6]),(0,[z0,z1,z2,z3,z877,z8]),(0,[z0,z1,z2,z3,z5,z878]),(0,[z0,z126,z795,z3,z5,z6]),(0,[z0,z1,z879,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z8]),(0,[z0,z1,z2,z491,z3,z8])]],
   [[(0,[z33,z739,z2,z3,z5,z6]),(0,[z0,z880,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z730,z6]),(0,[z0,z2,z3,z7,z730,z6]),(0,[z31,z0,z11,z1,z3,z32])],[(0,[z0,z1,z881,z3,z5,z6]),(0,[z0,z59,z2,z3,z124,z8]),(0,[z0,z1,z2,z3,z5,z882])],[(0,[z883,z0,z1,z2,z3,z5]),(0,[z196,z1,z2,z3,z463,z6]),(0,[z0,z1,z2,z3,z5,z262])],[(0,[z0,z1,z2,z884,z5,z6]),(0,[z561,z1,z2,z3,z197,z6]),(0,[z0,z1,z2,z3,z885,z6]),(1,[z0,z2,z3,z730,z6]),(0,[z0,z1,z2,z3,z32,z116]),(0,[z0,z872,z1,z2,z3,z346]),(0,[z0,z1,z504,z2,z3,z8])],[(0,[z33,z11,z34,z2,z3,z5]),(0,[z0,z1,z2,z3,z276,z8]),(0,[z0,z1,z2,z3,z886,z6])],[(0,[z552,z1,z2,z204,z5,z6]),(0,[z0,z1,z2,z3,z7,z244]),(0,[z0,z11,z1,z2,z184,z5]),(0,[z0,z42,z3,z184,z5,z6]),(0,[z0,z11,z1,z207,z3,z5]),(0,[z208,z0,z11,z1,z134,z5]),(0,[z0,z1,z2,z3,z269,z5])],[(0,[z0,z1,z2,z3,z5,z887]),(0,[z0,z1,z88,z3,z76,z8]),(0,[z0,z1,z2,z3,z888,z5]),(0,[z210,z196,z1,z2,z3,z8]),(0,[z73,z1,z2,z3,z5,z111]),(0,[z0,z180,z2,z3,z121,z23]),(0,[z0,z1,z889,z3,z5,z8])],[(0,[z0,z102,z2,z3,z5,z151]),(0,[z0,z1,z2,z3,z4,z8]),(0,[z0,z59,z2,z3,z124,z6]),(0,[z208,z0,z74,z134,z5,z6]),(0,[z0,z11,z1,z416,z2,z3])]],
   [[(0,[z0,z11,z1,z2,z3,z5]),(0,[z0,z890,z2,z3,z5,z6])],[(0,[z0,z1,z391,z3,z5,z72]),(0,[z0,z1,z291,z3,z5,z8]),(0,[z123,z179,z2,z3,z234,z6]),(0,[z0,z287,z127,z3,z5,z6]),(0,[z0,z1,z292,z3,z5,z8]),(0,[z0,z354,z1,z2,z3,z8]),(0,[z0,z180,z504,z2,z3,z5])],[(0,[z69,z1,z2,z3,z70,z352]),(0,[z0,z1,z891,z3,z5,z6])],[(0,[z69,z1,z2,z3,z756,z6]),(0,[z0,z1,z2,z3,z892,z6]),(0,[z0,z1,z2,z3,z893,z5]),(0,[z0,z1,z3,z894,z5,z8])],[(0,[z0,z1,z2,z3,z895,z6]),(0,[z0,z1,z2,z3,z554,z8]),(0,[z0,z1,z889,z3,z5,z6]),(0,[z0,z1,z3,z719,z5,z6])],[(0,[z0,z1,z2,z896,z5,z6]),(0,[z0,z1,z897,z2,z3,z5]),(0,[z0,z1,z2,z219,z3,z8])],[(0,[z0,z1,z2,z3,z5,z898]),(0,[z0,z1,z2,z899,z3,z5]),(0,[z175,z0,z2,z3,z7,z109]),(0,[z561,z0,z1,z2,z3,z8]),(0,[z31,z0,z1,z3,z32,z8]),(0,[z155,z0,z872,z1,z2,z3]),(0,[z0,z128,z1,z12,z3,z5])],[(0,[z0,z1,z291,z3,z5,z6]),(0,[z0,z1,z2,z159,z234,z6]),(0,[z0,z1,z292,z3,z5,z6]),(0,[z0,z1,z3,z900,z5,z6]),(0,[z0,z1,z2,z901,z5,z6]),(0,[z0,z1,z2,z3,z845,z6]),(0,[z0,z1,z2,z3,z356,z8]),(0,[z653,z1,z2,z3,z5,z463])]],
   [[(0,[z0,z1,z2,z464,z5,z8]),(0,[z0,z902,z2,z3,z5,z6]),(0,[z69,z0,z1,z2,z3,z877]),(0,[z0,z1,z2,z3,z311,z8])],[(0,[z0,z1,z2,z903,z5,z6]),(0,[z0,z1,z3,z894,z5,z6]),(0,[z0,z11,z74,z2,z3,z5])],[(0,[z0,z59,z2,z3,z730,z6])],[(0,[z0,z11,z102,z2,z3,z5]),(0,[z0,z68,z2,z3,z5,z8]),(0,[z69,z1,z2,z3,z70,z151]),(0,[z0,z1,z139,z3,z76,z8])],[(0,[z0,z1,z2,z3,z205,z23]),(0,[z0,z904,z2,z3,z5,z6]),(0,[z31,z0,z1,z3,z32,z6])],[(0,[z0,z1,z2,z905,z5,z6]),(0,[z0,z1,z2,z3,z906,z5]),(0,[z907,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z379,z173,z44])],[(0,[z0,z1,z2,z464,z5,z6]),(0,[z0,z1,z347,z3,z32,z6])],[(0,[z0,z1,z2,z3,z100,z6]),(0,[z0,z1,z2,z3,z438,z8]),(0,[z87,z0,z1,z2,z3,z8])]],
   [[(0,[z0,z1,z2,z908,z5,z6])],[(0,[z0,z68,z2,z3,z5,z6]),(0,[z69,z0,z1,z2,z3,z8]),(0,[z90,z0,z2,z21,z5,z8])],[(0,[z123,z179,z391,z3,z5,z6]),(0,[z909,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z368,z8]),(0,[z0,z11,z872,z1,z2,z3])],[(0,[z1,z2,z3,z5,z111,z765]),(0,[z208,z0,z1,z267,z134,z5]),(0,[z0,z1,z2,z3,z333,z8]),(0,[z0,z1,z2,z96,z3,z269])],[(0,[z1,z739,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z910]),(1,[z1,z722,z3,z5,z6]),(0,[z0,z68,z2,z95,z5,z6]),(0,[z0,z1,z2,z3,z307,z8])],[(0,[z196,z0,z1,z2,z3,z244]),(0,[z0,z1,z2,z3,z911,z6]),(0,[z0,z1,z2,z3,z5,z912])],[(0,[z1,z722,z88,z3,z5,z6]),(0,[z106,z1,z107,z3,z5,z8]),(0,[z0,z11,z1,z2,z99,z5]),(0,[z146,z0,z42,z184,z5,z6]),(0,[z0,z41,z2,z712,z5,z6])],[(0,[z0,z1,z2,z3,z913,z5]),(0,[z90,z0,z2,z21,z5,z6]),(0,[z0,z1,z200,z3,z597,z153]),(0,[z0,z1,z2,z3,z344,z8]),(0,[z286,z0,z1,z3,z40,z5]),(0,[z265,z0,z1,z491,z3,z5])]],
   [[(0,[z0,z1,z391,z159,z5,z6]),(0,[z0,z1,z2,z3,z5,z914]),(0,[z47,z0,z1,z2,z3,z8]),(0,[z0,z361,z1,z2,z3,z8])],[(0,[z0,z1,z291,z3,z5,z72]),(0,[z0,z1,z2,z3,z234,z750]),(0,[z565,z0,z1,z2,z3,z8]),(0,[z155,z0,z1,z165,z2,z3]),(0,[z0,z1,z2,z915,z3,z5])],[(0,[z0,z1,z916,z3,z5,z6]),(0,[z0,z1,z917,z3,z5,z6]),(0,[z0,z1,z2,z3,z333,z153])],[(0,[z0,z1,z2,z3,z234,z8]),(0,[z0,z1,z2,z3,z918,z5]),(0,[z135,z0,z1,z3,z16,z5])],[(0,[z106,z1,z107,z3,z5,z6]),(0,[z919,z0,z1,z2,z3,z6]),(0,[z69,z0,z102,z2,z3,z8]),(0,[z0,z1,z2,z3,z775,z5]),(0,[z0,z1,z2,z3,z652,z8])],[(0,[z0,z1,z2,z3,z5,z920]),(0,[z0,z126,z2,z184,z5,z6]),(0,[z146,z0,z42,z214,z5,z6])],[(0,[z69,z1,z168,z3,z70,z6]),(0,[z0,z1,z2,z814,z5,z6])],[(0,[z0,z1,z292,z99,z5,z6]),(0,[z0,z1,z2,z921,z5,z6])]],
   [[(0,[z0,z1,z922,z3,z5,z6]),(0,[z0,z1,z2,z464,z5,z72]),(0,[z0,z1,z2,z3,z5,z352])],[(0,[z0,z1,z2,z3,z234,z6]),(0,[z0,z1,z2,z3,z5,z116])],[(0,[z0,z1,z2,z3,z5,z923]),(0,[z0,z1,z2,z3,z5,z924])],[(0,[z0,z179,z2,z3,z124,z8])],[(0,[z0,z1,z2,z3,z925,z6]),(0,[z136,z1,z2,z3,z5,z111]),(0,[z0,z1,z2,z3,z501,z8])],[(0,[z0,z1,z291,z3,z5,z45]),(0,[z0,z926,z1,z2,z3,z5]),(0,[z0,z1,z2,z927,z5,z6]),(0,[z0,z795,z42,z3,z5,z6]),(0,[z0,z1,z2,z3,z206,z8]),(0,[z0,z1,z2,z821,z173,z6]),(0,[z0,z1,z2,z138,z3,z813])],[(0,[z0,z1,z2,z3,z928,z5]),(0,[z324,z0,z2,z21,z5,z6])],[(0,[z0,z1,z2,z3,z5,z929]),(0,[z0,z1,z2,z3,z5,z930]),(0,[z69,z0,z1,z2,z99,z8]),(0,[z931,z1,z2,z3,z5,z6]),(0,[z0,z1,z932,z2,z3,z5]),(0,[z175,z0,z2,z3,z730,z6])]],
   [[(0,[z0,z1,z2,z3,z933,z6]),(0,[z0,z1,z2,z934,z5,z6])],[(0,[z0,z1,z2,z3,z935,z6]),(0,[z0,z1,z2,z3,z5,z151]),(0,[z0,z68,z2,z99,z5,z6]),(0,[z0,z1,z2,z557,z3,z8]),(0,[z0,z1,z2,z3,z936,z5])],[],[(0,[z0,z1,z937,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z938]),(0,[z0,z1,z2,z3,z205,z6]),(0,[z0,z1,z74,z134,z5,z6]),(0,[z0,z1,z2,z3,z5,z939]),(0,[z0,z361,z1,z2,z178,z5])],[(0,[z0,z1,z2,z464,z5,z45]),(0,[z0,z1,z2,z3,z940,z6]),(0,[z0,z589,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z941,z6]),(0,[z0,z1,z942,z2,z3,z5])],[(0,[z0,z1,z2,z3,z943,z6]),(0,[z0,z1,z2,z3,z100,z45]),(0,[z0,z1,z2,z3,z5,z944]),(0,[z436,z0,z2,z21,z5,z6]),(0,[z0,z1,z2,z3,z124,z244]),(0,[z639,z0,z42,z3,z5,z6]),(0,[z673,z0,z1,z134,z5,z6]),(0,[z0,z1,z2,z821,z44,z6]),(0,[z0,z1,z945,z3,z5,z8])],[(0,[z0,z1,z946,z3,z5,z6]),(0,[z0,z11,z1,z2,z214,z5]),(0,[z0,z19,z2,z3,z5,z23]),(1,[z0,z74,z134,z5,z6]),(0,[z0,z947,z2,z3,z5,z6]),(0,[z0,z1,z200,z3,z5,z153]),(0,[z17,z0,z1,z2,z743,z5])],[(0,[z0,z1,z107,z3,z76,z8]),(0,[z31,z0,z1,z3,z728,z6])]],
   [[(0,[z1,z2,z53,z774,z5,z6]),(0,[z0,z102,z2,z3,z6,z8]),(0,[z0,z1,z92,z3,z5,z6]),(0,[z0,z2,z42,z184,z5,z6]),(0,[z133,z0,z1,z2,z3,z5]),(0,[z0,z1,z948,z2,z3,z5])],[(0,[z516,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z39,z505,z5])],[(0,[z0,z1,z391,z3,z5,z6]),(0,[z0,z1,z2,z949,z3,z5]),(0,[z0,z950,z2,z3,z5,z6]),(0,[z0,z1,z2,z951,z5,z6]),(0,[z0,z1,z3,z728,z5,z6]),(0,[z0,z128,z1,z2,z3,z8])],[(0,[z0,z1,z2,z3,z234,z72]),(0,[z0,z126,z127,z3,z5,z8]),(0,[z0,z11,z336,z1,z2,z3]),(0,[z0,z1,z75,z3,z76,z116])],[(0,[z0,z952,z1,z2,z3,z5]),(0,[z0,z1,z3,z953,z5,z6])],[(0,[z123,z179,z2,z159,z5,z6]),(0,[z0,z1,z2,z3,z304,z8])],[(0,[z0,z1,z168,z3,z5,z8]),(0,[z0,z1,z2,z821,z3,z6])],[(0,[z0,z11,z1,z92,z3,z5]),(0,[z0,z1,z2,z3,z5,z954]),(0,[z0,z2,z712,z21,z5,z6]),(0,[z0,z1,z139,z3,z5,z518])]],
   [[(0,[z479,z0,z42,z3,z5,z6]),(0,[z0,z1,z2,z99,z5,z352]),(0,[z673,z0,z42,z3,z5,z6]),(0,[z0,z2,z3,z105,z124,z8]),(0,[z0,z1,z2,z3,z5,z955]),(0,[z0,z11,z1,z75,z3,z76]),(0,[z0,z1,z2,z379,z3,z5])],[(0,[z0,z11,z1,z391,z3,z5]),(0,[z0,z126,z127,z3,z5,z6]),(0,[z0,z1,z956,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z957])],[(0,[z175,z0,z2,z3,z27,z6]),(0,[z1,z107,z722,z3,z5,z6]),(0,[z0,z958,z2,z3,z5,z6]),(0,[z1,z2,z3,z197,z756,z6]),(0,[z0,z613,z1,z2,z3,z8]),(1,[z0,z1,z2,z3,z845]),(0,[z0,z1,z3,z16,z719,z5])],[(0,[z34,z739,z2,z3,z5,z6]),(0,[z203,z11,z1,z2,z204,z5]),(0,[z196,z1,z2,z3,z756,z6]),(0,[z31,z0,z1,z219,z3,z32]),(0,[z0,z1,z2,z536,z3,z8]),(0,[z0,z1,z2,z3,z346,z8])],[(0,[z0,z1,z168,z3,z5,z6]),(0,[z0,z872,z1,z2,z3,z8])],[(0,[z142,z0,z1,z2,z669,z5])],[(0,[z0,z1,z2,z3,z5,z959]),(0,[z73,z1,z2,z3,z5,z463]),(0,[z960,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z234,z45]),(0,[z0,z1,z168,z95,z5,z6]),(0,[z0,z1,z2,z3,z5,z961]),(0,[z0,z19,z2,z3,z124,z8]),(0,[z0,z1,z2,z3,z517,z8]),(0,[z0,z1,z2,z3,z505,z8])]],
   [[(0,[z0,z926,z1,z2,z3,z100]),(0,[z0,z1,z2,z3,z962,z5]),(0,[z0,z42,z21,z134,z5,z6]),(0,[z0,z1,z2,z3,z963,z5])],[(0,[z0,z1,z2,z3,z5,z964]),(0,[z0,z1,z722,z3,z5,z6]),(0,[z0,z1,z2,z99,z5,z151]),(0,[z0,z1,z2,z965,z5,z6]),(0,[z0,z1,z2,z3,z966,z5]),(0,[z0,z1,z2,z3,z440,z8]),(0,[z0,z2,z3,z967,z5,z8])],[(0,[z0,z968,z1,z2,z3,z5]),(0,[z0,z1,z2,z969,z5,z6]),(0,[z0,z102,z2,z3,z70,z6]),(0,[z0,z1,z2,z704,z3,z8]),(0,[z0,z1,z200,z3,z259,z5]),(0,[z263,z0,z1,z2,z138,z8]),(0,[z0,z872,z1,z2,z3,z6])],[(0,[z0,z41,z2,z481,z5,z6]),(0,[z0,z1,z2,z3,z970,z6]),(0,[z0,z1,z2,z3,z32,z8])],[(0,[z0,z1,z2,z3,z971,z6]),(0,[z0,z1,z972,z3,z5,z6]),(0,[z0,z1,z2,z3,z76,z116]),(0,[z0,z1,z2,z3,z269,z8])],[(0,[z0,z973,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z974,z5])],[(0,[z0,z975,z1,z2,z3,z5])],[(0,[z0,z1,z2,z976,z5,z6]),(0,[z0,z1,z977,z3,z5,z6]),(0,[z0,z1,z2,z3,z454,z8]),(0,[z0,z1,z2,z3,z978,z5]),(0,[z0,z1,z2,z3,z5,z979]),(0,[z0,z11,z1,z2,z3,z8]),(0,[z0,z1,z2,z980,z5,z8])]],
   [[(0,[z0,z981,z2,z3,z5,z6]),(0,[z0,z1,z3,z32,z728,z6]),(0,[z0,z1,z2,z18,z178,z5])],[(0,[z123,z179,z2,z3,z5,z8]),(0,[z0,z1,z982,z3,z5,z6]),(0,[z0,z983,z2,z3,z5,z6]),(0,[z0,z1,z984,z3,z5,z6])],[(0,[z0,z1,z207,z3,z5,z8]),(0,[z985,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z986,z5,z8])],[(0,[z0,z179,z2,z3,z100,z6]),(0,[z106,z11,z1,z107,z3,z5]),(0,[z69,z1,z2,z3,z70,z8]),(0,[z0,z1,z2,z3,z5,z987]),(0,[z0,z59,z2,z3,z279,z124])],[(0,[z0,z1,z2,z988,z5,z6]),(0,[z155,z0,z102,z2,z3,z6]),(0,[z0,z2,z795,z3,z5,z6]),(0,[z0,z1,z2,z3,z465,z8]),(0,[z0,z1,z2,z3,z989,z5])],[(0,[z0,z1,z2,z3,z5,z990]),(0,[z0,z1,z2,z3,z456,z8]),(0,[z0,z1,z2,z3,z5,z991]),(0,[z0,z1,z2,z980,z5,z6]),(0,[z0,z1,z773,z2,z3,z7])],[(0,[z0,z1,z510,z3,z76,z6]),(0,[z0,z1,z2,z992,z5,z6]),(0,[z639,z0,z2,z21,z5,z6]),(0,[z0,z1,z2,z3,z5,z993])],[(0,[z123,z179,z2,z3,z5,z6]),(0,[z0,z1,z2,z159,z5,z8]),(0,[z0,z994,z1,z2,z3,z5]),(0,[z1,z2,z3,z5,z756,z6]),(0,[z0,z1,z2,z3,z5,z266])]],
   [[(0,[z0,z1,z391,z3,z5,z45]),(0,[z0,z1,z2,z986,z5,z6]),(0,[z0,z1,z2,z3,z22,z205]),(0,[z0,z1,z207,z3,z5,z6]),(0,[z0,z1,z2,z995,z3,z6])],[(0,[z0,z1,z2,z3,z996,z6]),(1,[z1,z2,z774,z5,z6]),(0,[z69,z616,z1,z2,z3,z6]),(0,[z210,z1,z2,z3,z5,z187]),(0,[z0,z1,z2,z3,z22,z121])],[(0,[z0,z1,z2,z3,z997,z6]),(0,[z0,z1,z2,z3,z597,z8]),(0,[z0,z1,z2,z3,z485,z8])],[(0,[z0,z1,z2,z3,z5,z998]),(0,[z0,z1,z2,z999,z5,z6]),(0,[z0,z11,z126,z127,z3,z5]),(0,[z0,z1,z2,z3,z5,z247])],[(0,[z0,z1,z168,z99,z5,z6]),(0,[z69,z1,z2,z95,z70,z6]),(0,[z73,z1,z2,z3,z5,z765]),(0,[z0,z1,z2,z1000,z3,z6]),(0,[z0,z1,z165,z2,z3,z246]),(0,[z0,z11,z1,z2,z3,z378]),(0,[z0,z1,z2,z500,z3,z8]),(0,[z0,z1,z139,z3,z76,z6]),(0,[z31,z0,z1,z3,z32,z262])],[(0,[z0,z1,z2,z3,z5,z1001]),(0,[z0,z1,z2,z3,z1002,z6]),(0,[z0,z1,z2,z3,z1003,z6]),(0,[z0,z1,z2,z3,z1004,z6]),(0,[z0,z102,z168,z3,z5,z6]),(0,[z0,z1,z3,z728,z76,z6])],[(0,[z0,z1,z2,z1005,z5,z6]),(0,[z0,z1,z1006,z3,z5,z6]),(0,[z196,z36,z1,z2,z3,z197]),(0,[z0,z1,z2,z3,z1007,z5]),(0,[z47,z131,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1008,z6]),(0,[z0,z1,z1009,z2,z3,z5]),(0,[z0,z1,z2,z3,z301,z8]),(0,[z17,z0,z1,z2,z669,z5])]],
   [[(0,[z0,z1,z2,z3,z240,z8]),(0,[z0,z1,z2,z3,z246,z8]),(0,[z0,z1,z2,z3,z597,z6]),(0,[z0,z1,z2,z3,z485,z6])],[(0,[z0,z1010,z1,z2,z3,z6]),(0,[z163,z1,z88,z3,z5,z8]),(0,[z0,z11,z59,z2,z3,z124]),(0,[z0,z94,z1,z2,z3,z8])],[(0,[z0,z1,z2,z1011,z5,z6]),(0,[z0,z1,z2,z3,z5,z1012]),(0,[z0,z1,z2,z3,z1013,z6]),(0,[z0,z1,z2,z3,z7,z266]),(0,[z0,z1,z2,z3,z485,z50])],[(0,[z0,z952,z1,z2,z3,z234]),(0,[z224,z0,z1,z2,z3,z352]),(0,[z224,z73,z1,z2,z3,z111]),(0,[z0,z1,z1014,z3,z5,z6])],[(0,[z0,z1,z1015,z3,z5,z6]),(0,[z0,z1,z1016,z3,z5,z6]),(0,[z69,z11,z1,z2,z3,z70]),(0,[z0,z1,z2,z3,z1017,z5]),(0,[z0,z1,z2,z3,z333,z6])],[(0,[z0,z1,z2,z3,z5,z1018]),(0,[z155,z0,z1,z168,z3,z6]),(0,[z227,z1,z2,z3,z5,z187]),(0,[z0,z1,z42,z184,z5,z6]),(0,[z0,z1,z2,z3,z1019,z6])],[(0,[z0,z11,z1,z2,z3,z100]),(0,[z0,z1,z2,z3,z5,z1020]),(0,[z0,z1,z2,z3,z1021,z6]),(0,[z0,z1,z2,z1022,z3,z5]),(0,[z0,z1023,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z246,z6])],[(0,[z163,z1,z88,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1024]),(0,[z366,z0,z42,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z877]),(1,[z0,z42,z184,z5,z6]),(0,[z0,z1025,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z134,z845])],[(0,[z123,z179,z2,z3,z5,z72]),(0,[z0,z1,z2,z1026,z3,z5]),(0,[z0,z1,z2,z3,z1027,z6])],[(0,[z0,z1,z2,z1028,z5,z6]),(0,[z0,z2,z20,z712,z5,z6]),(0,[z0,z1,z469,z2,z3,z8])],[],[(0,[z0,z1,z291,z3,z100,z6]),(0,[z0,z1,z2,z3,z5,z1029]),(0,[z0,z1,z2,z3,z5,z1030]),(0,[z445,z1,z2,z204,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1031]),(0,[z0,z472,z1,z2,z3,z8]),(0,[z0,z1,z2,z1032,z5,z6]),(0,[z0,z1,z2,z1033,z3,z5])],[(0,[z628,z0,z2,z3,z7,z6]),(0,[z0,z1,z200,z2,z3,z485])],[(0,[z0,z1,z2,z159,z5,z72]),(0,[z0,z1,z1034,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1035])]],
   [[(0,[z0,z1,z2,z1036,z5,z6]),(0,[z0,z1,z2,z1037,z5,z6]),(0,[z0,z1038,z2,z3,z5,z6]),(0,[z0,z1,z3,z32,z76,z8]),(0,[z0,z1,z2,z173,z44,z247])],[(0,[z0,z1,z2,z3,z5,z8]),(0,[z0,z180,z2,z3,z775,z5])],[(0,[z0,z11,z1,z2,z3,z234]),(0,[z69,z102,z2,z3,z70,z6]),(0,[z0,z354,z1,z2,z3,z121]),(0,[z0,z1039,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1040,z6])],[(0,[z0,z1,z2,z464,z100,z6]),(1,[z1,z2,z3,z756,z6]),(0,[z1041,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1042]),(0,[z208,z0,z1,z785,z5,z6])],[(0,[z0,z229,z2,z20,z5,z6]),(0,[z0,z1,z2,z95,z5,z8]),(0,[z0,z11,z1,z2,z3,z597]),(0,[z384,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z18,z743,z5]),(0,[z155,z0,z11,z1,z2,z3])],[(0,[z123,z179,z2,z3,z5,z45]),(0,[z0,z1043,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1044]),(0,[z0,z1,z2,z219,z3,z597]),(0,[z0,z1,z2,z3,z544,z8])],[(0,[z0,z1,z2,z1045,z5,z6]),(0,[z0,z1,z1046,z2,z3,z5]),(0,[z0,z1,z2,z3,z546,z8]),(0,[z497,z1,z88,z3,z5,z6]),(0,[z0,z1047,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1048,z3,z5]),(0,[z509,z0,z1,z134,z5,z6]),(0,[z0,z702,z2,z20,z5,z6]),(1,[z0,z1,z3,z719,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z1049])],[(0,[z0,z1,z2,z3,z5,z1050]),(0,[z284,z1,z2,z3,z5,z187]),(0,[z0,z1,z773,z2,z3,z5]),(0,[z135,z0,z1,z2,z3,z485])],[(0,[z0,z1,z1051,z3,z5,z6]),(0,[z0,z1052,z2,z3,z5,z6]),(0,[z0,z1,z2,z95,z5,z6]),(0,[z0,z1,z2,z99,z6,z8])],[(0,[z33,z34,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z1053,z6])],[(0,[z0,z41,z2,z20,z5,z8]),(0,[z0,z1,z2,z3,z7,z8])],[(0,[z123,z739,z2,z3,z5,z6]),(0,[z239,z179,z2,z3,z5,z6]),(0,[z0,z1,z292,z3,z5,z352]),(0,[z0,z1,z1054,z2,z3,z267])],[(0,[z0,z1,z1055,z3,z5,z6]),(0,[z0,z1,z2,z3,z1056,z6]),(0,[z227,z1,z2,z3,z5,z765]),(0,[z0,z1,z2,z3,z566,z8]),(0,[z0,z1,z945,z3,z5,z6]),(0,[z17,z0,z1,z2,z18,z5])],[(0,[z0,z1057,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z568,z8]),(0,[z0,z11,z1,z2,z3,z189])]],
   [[(0,[z0,z1,z2,z1058,z5,z6]),(0,[z0,z1,z2,z3,z5,z1059])],[(0,[z0,z1,z2,z1060,z5,z6]),(0,[z0,z1,z2,z3,z5,z815]),(0,[z0,z1,z795,z3,z5,z6])],[(0,[z0,z1061,z2,z3,z5,z6]),(0,[z0,z41,z2,z20,z5,z6])],[(0,[z0,z160,z1,z2,z3,z8]),(0,[z0,z1,z2,z1062,z5,z6]),(0,[z0,z359,z2,z3,z124,z6]),(0,[z196,z1,z2,z3,z197,z8]),(0,[z0,z1,z2,z3,z1063,z5]),(0,[z0,z1,z3,z40,z76,z8])],[(0,[z325,z1,z88,z3,z5,z6]),(0,[z1,z2,z3,z5,z765,z6]),(1,[z0,z795,z3,z5,z6]),(0,[z0,z74,z89,z3,z5,z6]),(0,[z0,z1,z2,z598,z5,z50]),(0,[z0,z1,z1064,z3,z5,z8])],[(0,[z0,z1,z1065,z3,z5,z6]),(0,[z0,z1,z1054,z2,z3,z6]),(0,[z135,z0,z1,z3,z40,z5])],[(0,[z0,z1,z2,z3,z1066,z6]),(0,[z0,z1,z2,z774,z5,z6]),(0,[z0,z1,z292,z3,z5,z151]),(0,[z0,z1067,z2,z3,z5,z6]),(0,[z0,z11,z43,z2,z3,z5]),(0,[z0,z1,z2,z3,z267,z845]),(0,[z0,z1,z2,z173,z44,z8])],[(0,[z0,z1,z2,z3,z5,z1068]),(0,[z0,z11,z1,z2,z3,z671])]],
   [[(0,[z675,z1,z2,z3,z5,z111]),(0,[z324,z0,z1,z134,z5,z6])],[(0,[z0,z1,z2,z3,z5,z72]),(0,[z0,z1,z2,z3,z1069,z6]),(0,[z0,z1,z2,z1070,z5,z6]),(0,[z196,z1,z2,z3,z197,z6]),(0,[z0,z1,z102,z2,z3,z8]),(0,[z0,z1,z2,z99,z5,z8]),(0,[z0,z1,z785,z134,z5,z6])],[(0,[z1071,z0,z1,z2,z3,z6]),(0,[z0,z102,z2,z3,z5,z8]),(0,[z0,z1,z1064,z3,z5,z6]),(0,[z0,z207,z3,z21,z5,z6]),(0,[z0,z2,z3,z712,z5,z6])],[],[(1,[z0,z102,z2,z3,z8]),(0,[z0,z1,z2,z1072,z5,z6]),(0,[z0,z1,z2,z3,z1073,z6]),(0,[z0,z1074,z2,z3,z5,z6]),(0,[z325,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z173,z44,z6]),(0,[z0,z1,z1075,z3,z5,z8])],[(0,[z0,z1076,z2,z3,z5,z6]),(0,[z0,z11,z1,z2,z95,z5]),(0,[z0,z1,z2,z3,z1077,z5]),(0,[z0,z1,z2,z3,z5,z93]),(0,[z136,z0,z1,z2,z3,z8])],[(0,[z0,z1,z1078,z3,z5,z6]),(0,[z0,z1,z2,z3,z442,z8])],[(0,[z0,z1,z1079,z3,z5,z6]),(0,[z0,z1,z2,z3,z609,z8]),(0,[z0,z1,z2,z3,z5,z1080]),(1,[z0,z1,z3,z728,z6]),(0,[z0,z1,z2,z579,z3,z8]),(1,[z0,z872,z1,z2,z3])]],
   [[(0,[z0,z102,z2,z3,z5,z6]),(0,[z0,z1081,z1,z2,z3,z5]),(0,[z0,z68,z2,z3,z5,z151]),(0,[z0,z1,z2,z712,z5,z6]),(0,[z0,z19,z2,z3,z124,z6]),(0,[z0,z1,z2,z39,z3,z333]),(0,[z0,z1,z2,z3,z281,z8])],[(0,[z1,z2,z774,z204,z5,z6])],[(0,[z0,z1082,z2,z3,z5,z6]),(0,[z0,z2,z3,z967,z5,z6]),(0,[z0,z1,z2,z3,z124,z266]),(0,[z0,z1,z1075,z3,z5,z6])],[(0,[z123,z11,z179,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1083]),(0,[z0,z1084,z2,z3,z5,z6]),(0,[z0,z102,z2,z95,z5,z6]),(1,[z0,z2,z712,z5,z6]),(0,[z0,z19,z2,z3,z5,z104])],[(0,[z0,z1085,z2,z3,z5,z6]),(0,[z196,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z3,z1086,z6]),(0,[z0,z1,z2,z3,z1087,z5]),(0,[z0,z180,z2,z3,z246,z23])],[(0,[z0,z1,z2,z3,z5,z45]),(0,[z0,z1,z2,z3,z1088,z6]),(0,[z0,z1,z2,z3,z352,z8]),(0,[z0,z1,z2,z3,z5,z1089]),(0,[z0,z1,z2,z3,z1090,z5]),(0,[z0,z1,z2,z3,z813,z5])],[(0,[z106,z1,z722,z3,z5,z6])],[(0,[z0,z1,z391,z3,z100,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 530) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 530).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1057).take 112) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1169)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [530, 527, 112] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 112).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 225).take 31).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [112, 113, 31] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_43982

theorem PEqualNP.Outside.L_meta_43982 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276791432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276791432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43982.solve
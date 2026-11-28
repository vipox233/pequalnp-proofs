import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38873

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
  Nat.testBit (4276808936 * 2 ^ 32 + 4272611488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x001027016108b0ac#64 ++ 0x200204e02c211615#64 ++ 0xb831ef03e11ff1ff#64 ++ 0xd7063de07c23fe3f#64 : BitVec 256),
   (0x0846816cb1659666#64 ++ 0x4108d02d962cb2cc#64 ++ 0xe8ce93fcf1e59e67#64 ++ 0xbd19d27f9e3cb3cc#64 : BitVec 256),
   (0x030b181616060b50#64 ++ 0x80616302c2c0c16a#64 ++ 0xf70f1c1f1e061fff#64 ++ 0x7ee1e383e3c0c3ff#64 : BitVec 256),
   (0x15b01fa00bb81d87#64 ++ 0x02b603f4017703b0#64 ++ 0xdff01fe01ff81f86#64 ++ 0xfbfe03fc03ff03f0#64 : BitVec 256),
   (0x06efc0001cd74000#64 ++ 0x00ddf800039ae800#64 ++ 0x9fffe0001fffe005#64 ++ 0xf3fffc0003fffc00#64 : BitVec 256),
   (0x27fdfedbc0000000#64 ++ 0x04ffbfdb78000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [11, 2]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [8, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xb831ef03e11ff1ff 0xd7063de07c23fe3f

def z1 : W := mkw 0x0046804890450000 0x0008d0091208a000 0xe8ce93fcf1e58007 0xbd19d27f9e3cb000

def z2 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xf70f1c1f1e061fff 0x7ee1e383e3c0c3ff

def z3 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z4 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xe8ce93fcf1e59e67 0xbd19d27f9e3cb3cc

def z5 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xdff01fe01ff81f86 0xfbfe03fc03ff03f0

def z6 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z7 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x173fe0000e1fe001 0x42e7fc0001c3fc00

def z8 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xfff1ffe3ffffffff 0xfffe3ffc7fffffff

def z9 : W := mkw 0x0802016cb1249666 0x4100402d962492cc 0xe00e13fcf0041e67 0x3c01c27f9e0083cc

def z10 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x9830ef00e119f186 0xd3061de01c233e30

def z11 : W := mkw 0x0044804880000000 0x0008900910000000 0xe0ce93fce0000003 0xbc19d27f9c000000

def z12 : W := mkw 0x27fffedfd6060b50 0x84ffffdbfac0c16a 0xf7fffffffe061fff 0xfeffffffffc0c3ff

def z13 : W := mkw 0x0046800010450000 0x0008d0000208a000 0x88ce800011e58005 0xb119d000023cb000

def z14 : W := mkw 0x0eefc16cbdf7d666 0x41ddf82d97befacc 0xfffff3fcfffffe67 0xfffffe7f9fffffcc

def z15 : W := mkw 0x1cf487e8a9f994a7 0x439e90fd153f3294 0x08f083e0e1f98000 0x811e107c1c3f3000

def z16 : W := mkw 0x0846804cb0458260 0x4108d0099608b04c 0x200e801ce0058061 0x0401d0039c00b00c

def z17 : W := mkw 0x15b01e800a980981 0x02b603d001530130 0x17300c000e180180 0x42e6018001c30030

def z18 : W := mkw 0x0846806c90650642 0x4108d00d920ca0c8 0x40ce10fc10e00e00 0x2819c21f821c01c0

def z19 : W := mkw 0x0856a76df16db6ee 0x610ad4edbe2db6dd 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z20 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0x47c010e01ee00e00 0x28f8021c03dc01c0

def z21 : W := mkw 0x07efd8161ed74b50 0x80fdfb02c3dae96a 0xfffffc1f1fffffff 0xffffff83e3ffffff

def z22 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0x0800000011e59e64 0x01000000023cb3cc

def z23 : W := mkw 0x0309181206020910 0x8061230240c04122 0x17010c030e020198 0x42e0218061c04033

def z24 : W := mkw 0x27fdfedbc6020910 0x84ffbfdb78c04122 0xf7ffffffee02019b 0xfefffffffdc04033

def z25 : W := mkw 0x17bb1fb61fbe1fd7 0x82f763f6c3f7c3fa 0xffff1fff1ffe1fff 0xffffe3ffe3ffc3ff

def z26 : W := mkw 0x06efc0489cd74000 0x00ddf809139ae800 0xfffff3fcffffe007 0xfffffe7f9ffffc00

def z27 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x97cf00001ee60005 0x72f9e00003dcc000

def z28 : W := mkw 0x020b000014060000 0x004160000280c000 0x970f00001e060005 0x72e1e00003c0c000

def z29 : W := mkw 0x06edc00000000000 0x00ddb80000000000 0x87ffe00000000001 0xf0fffc0000000000

def z30 : W := mkw 0x0100181602000b50 0x80200302c040016a 0x60001c1f00001ffa 0x0c000383e00003ff

def z31 : W := mkw 0x031b3f17770ebbfc 0xa06367e2eee1d77f 0xff3fff1fff1fffff 0xffe7ffe3ffe3ffff

def z32 : W := mkw 0x06ffe7017ddff0ac 0x20dffce02fbbfe15 0xbfffef03fffff1ff 0xf7fffde07ffffe3f

def z33 : W := mkw 0x27fdffdbe108b0ac 0x24ffbffb7c211615 0xe7ffffffe00011fb 0xfcfffffffc00023f

def z34 : W := mkw 0x0010070001081084 0x000200e000210210 0x98300f0001181186 0xd30601e000230230

def z35 : W := mkw 0x27b97f936108b0ac 0x24f72ff26c211615 0xbf31ef03e11ff1ff 0xd7e63de07c23fe3f

def z36 : W := mkw 0x04a0000008900000 0x0094000001120000 0x08f0000001f80000 0x811e0000003f0000

def z37 : W := mkw 0x2ffffffff7679f76 0xc5fffffffeecf3ee 0xffffffffffe79fff 0xfffffffffffcf3ff

def z38 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x57301fe00e181f82 0x4ae603fc01c303f0

def z39 : W := mkw 0x0010072001281486 0x000200e400250290 0xd8f01fe011f81f86 0xfb1e03fc023f03f0

def z40 : W := mkw 0x0010260140082088 0x200204c028010411 0x10316c03001a6198 0x42062d8060034c33

def z41 : W := mkw 0x0000012001201406 0x0000002400240280 0xc8c013e011e01e06 0xb918027c023c03c0

def z42 : W := mkw 0x04e4c00008d14000 0x009c9800011a2800 0x08f0e00001f9e000 0x811e1c00003f3c00

def z43 : W := mkw 0x06a940000c924000 0x00d5280001924800 0x173160000e1a6000 0x42e62c0001c34c00

def z44 : W := mkw 0x0802012437679f76 0xc100402486ecf3ee 0x180000001fe79ffc 0x0300000003fcf3ff

def z45 : W := mkw 0x0000000006020910 0x8000000000c04122 0x100000000e020198 0x0200000001c04033

def z46 : W := mkw 0x0010260140082088 0x200204c028010411 0xb0316c03001e71ff 0x56062d806003ce3f

def z47 : W := mkw 0x0000010021009024 0x0000002004201204 0xa8008300e1059067 0x950010601c20b20c

def z48 : W := mkw 0x100000200ab00d03 0x02000004015601a0 0x000000001ee00e00 0x0000000003dc01c0

def z49 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x07f1efe3e0000000 0xc0fe3dfc7c000000

def z50 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x1830e300e11ff1fc 0x83061c601c23fe3f

def z51 : W := mkw 0x0a4fc04cb447c260 0x4149f8099688f84c 0x200fe01ce007e061 0x0401fc039c00fc0c

def z52 : W := mkw 0x020b001614060250 0x80416002c280c04a 0x200f001f00060079 0x0401e003e000c00f

def z53 : W := mkw 0x27fdfedbc8d14000 0x04ffbfdb791a2800 0xefffffffe1f9e003 0xfdfffffffc3f3c00

def z54 : W := mkw 0x020b001614060250 0x80416002c280c04a 0xe00f101f10061e7f 0x3c01e203e200c3cf

def z55 : W := mkw 0x17efd8a01ef74d03 0x02fdfb1403dee9a0 0xdffff0e01fffee05 0xfbfffe1c03fffdc0

def z56 : W := mkw 0x0054a749e108b0ac 0x200a94e93c211615 0xf8ffffffe11ff1ff 0xff1ffffffc23fe3f

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0x9831e000011fe005 0xd3063c000023fc00

def z58 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x670e1c1f1e001ffa 0x2ce1c383e3c003ff

def z59 : W := mkw 0x27fdffdbe108b0ac 0x24ffbffb7c211615 0xffffffffe11ff1ff 0xfffffffffc23fe3f

def z60 : W := mkw 0x04a0000008900000 0x0094000001120000 0x9ff000001ff80004 0xf3fe000003ff0000

def z61 : W := mkw 0x0000012001201406 0x0000002400240280 0x400013e000001e02 0x0800027c000003c0

def z62 : W := mkw 0x030b180016060900 0x0061630002c0c120 0xd70f1c001e061f87 0x7ae1e38003c0c3f0

def z63 : W := mkw 0x2a4fe17ff1659666 0x4549fc2ffe2cb2cc 0xe8cff3fff1e59e67 0xbd19fe7ffe3cb3cc

def z64 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x67ce1fffe0000002 0x2cf9c3fffc000000

def z65 : W := mkw 0x000200001cd74000 0x00004000039ae800 0x180000001fffe004 0x0300000003fffc00

def z66 : W := mkw 0x0046800410450240 0x0008d0008208a048 0xe8ce901c11e59e67 0xbd19d203823cb3cc

def z67 : W := mkw 0x21103edbc0000000 0x042207db78000000 0x60001fffe0000002 0x0c0003fffc000000

def z68 : W := mkw 0x27ffffdff70ebbfc 0xa4fffffbfee1d77f 0xffffffffff1fffff 0xffffffffffe3ffff

def z69 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x470e101c1e000e00 0x28e1c20383c001c0

def z70 : W := mkw 0x0b4f997eb7679f76 0xc169f32fd6ecf3ee 0xefce93fcffe59e67 0xbdf9d27f9ffcb3cc

def z71 : W := mkw 0x27b97e9340000000 0x04f72fd268000000 0x07316c0300000000 0x40e62d8060000000

def z72 : W := mkw 0x0000010021009024 0x0000002004201204 0x0800000001059064 0x010000000020b20c

def z73 : W := mkw 0x1846816cbbfd9fe7 0x4308d02d977fb3fc 0xf8ce93fcfffd9fe7 0xbf19d27f9fffb3fc

def z74 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0xbfffec031ffff1ff 0xf7fffd8063fffe3f

def z75 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x20000f03e00011fa 0x040001e07c00023f

def z76 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x07ce00001ee00000 0x20f9c00003dc0000

def z77 : W := mkw 0x0054a649c0000000 0x000a94c938000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z78 : W := mkw 0x2ffffffff16db6ee 0x65fffffffe2db6dd 0xfffffffff1ffffff 0xfffffffffe3fffff

def z79 : W := mkw 0x35f4ffe9cbb81d87 0x06be9ffd397703b0 0xdff0ffe0fff81f86 0xfbfe1ffc1fff03f0

def z80 : W := mkw 0x180201243bfd9fe7 0x43004024877fb3fc 0x180000001ffd9fe4 0x0300000003ffb3fc

def z81 : W := mkw 0x1df69fecbbfd9fe7 0x43bed3fd977fb3fc 0xfffe9ffcfffd9fe7 0xffffd3ff9fffb3fc

def z82 : W := mkw 0x15b03e814a982989 0x22b607d029530531 0x17316c030e1a6198 0x42e62d8061c34c33

def z83 : W := mkw 0x08448168a1619426 0x4108902d142c3284 0x08c083e0e1e18000 0x8118107c1c3c3000

def z84 : W := mkw 0x37fffffbdfff5d87 0x06ffffff7bffebb0 0xffffffffffffff87 0xfffffffffffffff0

def z85 : W := mkw 0x27fffedbdcd74000 0x04ffffdb7b9ae800 0xffffffffffffe007 0xfffffffffffffc00

def z86 : W := mkw 0x024fc0001cd74000 0x0049f800039ae800 0x180fe0001fffe005 0x0301fc0003fffc00

def z87 : W := mkw 0x06edc0000cd34000 0x00ddb800019a6800 0x1ff1e0000ffbe000 0xc3fe3c0001ff7c00

def z88 : W := mkw 0x24b0668140000000 0x04960cd028000000 0x0030600000000000 0x00060c0000000000

def z89 : W := mkw 0x0000010021009024 0x0000002004201204 0xb831e300e11ff067 0xd7063c601c23fe0c

def z90 : W := mkw 0x034fd81616474b50 0x8069fb02c2c8e96a 0xf70ffc1f1e07ffff 0x7ee1ff83e3c0ffff

def z91 : W := mkw 0x0102180412040b40 0x0020430082408168 0xf70e1c1c1e041fe7 0x7ee1c38383c083fc

def z92 : W := mkw 0x2209601340000000 0x04412c0268000000 0x0001600300000000 0x00002c0060000000

def z93 : W := mkw 0x110018a002200d03 0x02200314004401a0 0x400010e000000e00 0x0800021c000001c0

def z94 : W := mkw 0x27fdfe9340000000 0x04ffbfd268000000 0x87ffec0300000001 0xf0fffd8060000000

def z95 : W := mkw 0x2ffffffff1659666 0x45fffffffe2cb2cc 0xeffffffff1e59e67 0xfdfffffffe3cb3cc

def z96 : W := mkw 0x020b001614060250 0x80416002c280c04a 0x000e001c00000000 0x0001c00380000000

def z97 : W := mkw 0x0000000000000000 0x0000000000000000 0x8031e00000000001 0xd0063c0000000000

def z98 : W := mkw 0x04a0000008900000 0x0094000001120000 0x9ff1e0001fffe005 0xf3fe3c0003fffc00

def z99 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xe70f1c1f1e000e03 0x7ce1e383e3c001c0

def z100 : W := mkw 0x14b007a009b81487 0x029600f401370290 0x08f003e001f80000 0x811e007c003f0000

def z101 : W := mkw 0x1cf687ecb9fd96e7 0x439ed0fd973fb2dc 0xe8fe93fcf1fd9e67 0xbd1fd27f9e3fb3cc

def z102 : W := mkw 0x0846816cbdf7d666 0x4108d02d97befacc 0xf8ce93fcfffffe67 0xbf19d27f9fffffcc

def z103 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xfff11fe31ffe1fff 0xfffe23fc63ffc3ff

def z104 : W := mkw 0x00448148a1009024 0x0008902914201204 0xe8ce93fce1059067 0xbd19d27f9c20b20c

def z105 : W := mkw 0x15b21fa41bbc1fc7 0x02b643f4837783f8 0xfffe1ffc1ffc1fe7 0xffffc3ff83ff83fc

def z106 : W := mkw 0x0102181612040b50 0x80204302c240816a 0xe00e1c1f10041fff 0x3c01c383e20083ff

def z107 : W := mkw 0x0000000000000000 0x0000000000000000 0xb0010c03000611ff 0x560021806000c23f

def z108 : W := mkw 0x224de05bc0000000 0x0449bc0b78000000 0x200fe01fe0000001 0x0401fc03fc000000

def z109 : W := mkw 0x01103f016308b9ac 0x202207e02c611735 0xff31ff03ff1fffff 0xffe63fe07fe3ffff

def z110 : W := mkw 0x0802002410650642 0x41004004820ca0c8 0x0000000010e00e00 0x00000000021c01c0

def z111 : W := mkw 0x0209000004020000 0x0041200000804000 0x170100000e020000 0x42e0200001c04000

def z112 : W := mkw 0x27fdfedbc8900000 0x04ffbfdb79120000 0xfffffffffff80007 0xffffffffffff0000

def z113 : W := mkw 0x21103fdbe108b0ac 0x242207fb7c211615 0xf831ffffe11ff1ff 0xdf063ffffc23fe3f

def z114 : W := mkw 0x100001200bb81d87 0x02000024017703b0 0x180000001ff81f84 0x0300000003ff03f0

def z115 : W := mkw 0x14b027a169b8b4af 0x229604f42d371695 0x08f0e3e0e1f9e000 0x811e1c7c1c3f3c00

def z116 : W := mkw 0x0100180002000900 0x0020030000400120 0xf7011c031e061fff 0x7ee0238063c0c3ff

def z117 : W := mkw 0x25f4fedbc0000000 0x04be9fdb78000000 0x60f0ffffe0000002 0x8c1e1ffffc000000

def z118 : W := mkw 0x11101fa003281d87 0x022203f4006503b0 0x40001fe000001f82 0x080003fc000003f0

def z119 : W := mkw 0x0946997eb3659f76 0xc128d32fd66cb3ee 0xe8ce9ffff1e59fff 0xbd19d3fffe3cb3ff

def z120 : W := mkw 0x06ab40001c964000 0x00d568000392c800 0x973f60001e1e6005 0x72e7ec0003c3cc00

def z121 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x47fef3fce0000000 0xa8ffde7f9c000000

def z122 : W := mkw 0x0046810031459024 0x0008d0200628b204 0xa8ce8300f1e59067 0xb519d0601e3cb20c

def z123 : W := mkw 0x0309181200000000 0x0061230240000000 0xe70f1c1f00000003 0x7ce1e383e0000000

def z124 : W := mkw 0x27b97e9340000000 0x04f72fd268000000 0xc7f17fe300000002 0xf8fe2ffc60000000

def z125 : W := mkw 0x2fefd8fe90650642 0x45fdfb1fd20ca0c8 0x47ce10fc10e00e00 0x28f9c21f821c01c0

def z126 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xdff1ffe01fffff87 0xfbfe3ffc03fffff0

def z127 : W := mkw 0x101007200bb81d87 0x020200e4017703b0 0x98300f001ff81f86 0xd30601e003ff03f0

def z128 : W := mkw 0x0209001204020010 0x8041200240804002 0x0001000300020018 0x0000200060004003

def z129 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x08c083e0f1e59e64 0x8118107c1e3cb3cc

def z130 : W := mkw 0x15f69fa01bfd1d87 0x02bed3f4037fa3b0 0xdffe9fe01ffd9f87 0xfbffd3fc03ffb3f0

def z131 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x370f0c1f0e0601f9 0x46e1e183e1c0c03f

def z132 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x87ffe0001ee00001 0xf0fffc0003dc0000

def z133 : W := mkw 0x04a0012009b01406 0x0094002401360280 0xdff013e01ff81e06 0xfbfe027c03ff03c0

def z134 : W := mkw 0x001026016008a0a8 0x200204c02c011415 0x3031ec03e01fe1f9 0x46063d807c03fc3f

def z135 : W := mkw 0x0856a74df14db2ec 0x610ad4e9be29b65d 0xb83fef1fe11ff1ff 0xd707fde3fc23fe3f

def z136 : W := mkw 0x000021016100b02c 0x200004202c201605 0xa801e303e107f07f 0x95003c607c20fe0f

def z137 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xff3ffc1f1f1fffff 0xffe7ff83e3e3ffff

def z138 : W := mkw 0x0800016ca1209666 0x4100002d942412cc 0x600013fce0001e62 0x0c00027f9c0003cc

def z139 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xb8300f03e11811fe 0xd70601e07c23023f

def z140 : W := mkw 0x08122725716db6ee 0x610244e4ae2db6dd 0xb831ef03f1ffffff 0xd7063de07e3fffff

def z141 : W := mkw 0x07bb1e9616060b50 0x80f763d2c2c0c16a 0xf7ff1fff1e061fff 0xfeffe3ffe3c0c3ff

def z142 : W := mkw 0x08020124316db6ee 0x61004024862db6dd 0x1800000011fffffc 0x03000000023fffff

def z143 : W := mkw 0x15a019a00bb81d87 0x02b40334017703b0 0x5fc010e01ff81f84 0x2bf8021c03ff03f0

def z144 : W := mkw 0x04e4c00008d14000 0x009c9800011a2800 0x9ff0e0001ff9e004 0xf3fe1c0003ff3c00

def z145 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xa831ef03e119e003 0xd5063de07c233c00

def z146 : W := mkw 0x24f4e6c9c0000000 0x049e9cd938000000 0x00f0e3e0e0000000 0x801e1c7c1c000000

def z147 : W := mkw 0x0000010021009024 0x0000002004201204 0x20000300e0001062 0x040000601c00020c

def z148 : W := mkw 0x1000012009b81487 0x0200002401370290 0x0800000001f80000 0x01000000003f0000

def z149 : W := mkw 0x06edc04880000000 0x00ddb80910000000 0xe7fff3fce0000003 0xfcfffe7f9c000000

def z150 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x48ce93fcf1e18e00 0xa919d27f9e3c31c0

def z151 : W := mkw 0x1df6bfedfbfdbfef 0x63bed7fdbf7fb7fd 0xffffffffffffffff 0xffffffffffffffff

def z152 : W := mkw 0x05b01e8000000000 0x00b603d000000000 0xc7f01fe000000002 0xf8fe03fc00000000

def z153 : W := mkw 0x0309181200000000 0x0061230240000000 0xf70f1c1f000611ff 0x7ee1e383e000c23f

def z154 : W := mkw 0x03193f136108b0ac 0x206327e26c211615 0xff3fff1fe11ff1ff 0xffe7ffe3fc23fe3f

def z155 : W := mkw 0x06efc1201df75406 0x00ddf82403beea80 0xdffff3e01ffffe07 0xfbfffe7c03ffffc0

def z156 : W := mkw 0x000001002108b0ac 0x2000002004211615 0xb8008300e11ff1ff 0x970010601c23fe3f

def z157 : W := mkw 0x0100180002000900 0x0020030000400120 0xd7001c001e001f86 0x7ae0038003c003f0

def z158 : W := mkw 0x0046804c90040240 0x0008d00992008048 0xe0ce93fcf0041e67 0xbc19d27f9e0083cc

def z159 : W := mkw 0x27fdfedbcc924000 0x04ffbfdb79924800 0xf7ffffffee1a6003 0xfefffffffdc34c00

def z160 : W := mkw 0x0046812011651406 0x0008d024022ca280 0xc8ce93e011e59e07 0xb919d27c023cb3c0

def z161 : W := mkw 0x000001002108b0ac 0x2000002004211615 0x9831e000011ff1fd 0xd3063c000023fe3f

def z162 : W := mkw 0x17ab18b61eb60f53 0x82f56316c3d6c1ea 0xf7cf1cff1ee61fff 0x7ef9e39fe3dcc3ff

def z163 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00e101c00000003 0x3c01c20380000000

def z164 : W := mkw 0x2cf4e7e9e1619426 0x459e9cfd3c2c3284 0x08f0e3e0e1e18000 0x811e1c7c1c3c3000

def z165 : W := mkw 0x04b0070009981084 0x009600e001330210 0x9ff00f001ff81186 0xf3fe01e003ff0230

def z166 : W := mkw 0x0002000410040240 0x0000400082008048 0xf00f1c1f10061fff 0x7e01e383e200c3ff

def z167 : W := mkw 0x0100180002000900 0x0020030000400120 0x17000c000e000180 0x42e0018001c00030

def z168 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x600e93fce0059e63 0x0c01d27f9c00b3cc

def z169 : W := mkw 0x06ffe6015cdf6088 0x20dffcc02b9bec11 0x9fffec031fffe19d 0xf3fffd8063fffc33

def z170 : W := mkw 0x0002000410040240 0x0000400082008048 0x0000000010041e64 0x00000000020083cc

def z171 : W := mkw 0x0846816cb7679f76 0xc108d02d96ecf3ee 0xf8ce93fcffe79fff 0xbf19d27f9ffcf3ff

def z172 : W := mkw 0x000000000c924000 0x0000000001924800 0x100000000e1a6000 0x0200000001c34c00

def z173 : W := mkw 0x224fe05bd4474000 0x0449fc0b7a88e800 0x200fe01fe007e001 0x0401fc03fc00fc00

def z174 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xfff01fe3fff81ffe 0xfffe03fc7fff03ff

def z175 : W := mkw 0x024fc00014474000 0x0049f8000288e800 0x000fe0000007e001 0x0001fc000000fc00

def z176 : W := mkw 0x07efd8001ed74900 0x00fdfb0003dae920 0xdffffc001fffff87 0xfbffff8003fffff0

def z177 : W := mkw 0x27efd8de96060b50 0x84fdfb1bd2c0c16a 0x47ce10fc1e000e00 0x28f9c21f83c001c0

def z178 : W := mkw 0x06efc00014060000 0x00ddf8000280c000 0x97ffe0001e060005 0xf2fffc0003c0c000

def z179 : W := mkw 0x11101fa003281d87 0x022203f4006503b0 0xd8301fe001181f86 0xdb0603fc002303f0

def z180 : W := mkw 0x000020016000a028 0x200004002c001405 0x2001e003e007e079 0x04003c007c00fc0f

def z181 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x17010c031e061ffc 0x42e0218063c0c3ff

def z182 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0xa8008300f1e59e67 0x950010601e3cb3cc

def z183 : W := mkw 0x0854a769e169b4ae 0x610a94ed3c2d3695 0xb8f1efe3e1fff1ff 0xd71e3dfc7c3ffe3f

def z184 : W := mkw 0x37b97e934a980981 0x06f72fd269530130 0x17316c030e180180 0x42e62d8061c30030

def z185 : W := mkw 0x27edd8da80000000 0x04fdbb1b50000000 0x47ce10fc00000000 0x28f9c21f80000000

def z186 : W := mkw 0x07a958120e924910 0x80f52b0241d24922 0x17316c030e1a6198 0x42e62d8061c34c33

def z187 : W := mkw 0x001007002108b0ac 0x200200e004211615 0x98300f00011ff1fe 0xd30601e00023fe3f

def z188 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xb0010f03e00611ff 0x560021e07c00c23f

def z189 : W := mkw 0x0800004ca0008260 0x410000099400104c 0x2000001ce0000060 0x040000039c00000c

def z190 : W := mkw 0x17ffdfa01fff5d87 0x02fffbf403ffebb0 0xdfffffe01fffff87 0xfbfffffc03fffff0

def z191 : W := mkw 0x0010260140082088 0x200204c028010411 0xb031ef03e01a619b 0xd6063de07c034c33

def z192 : W := mkw 0x0846806cb0658662 0x4108d00d960cb0cc 0x60ce90fcf0e58e61 0x2c19d21f9e1cb1cc

def z193 : W := mkw 0x0b4f997eb7679f76 0xc169f32fd6ecf3ee 0xffcf9fffffe79fff 0xfff9f3fffffcf3ff

def z194 : W := mkw 0x06efe0017cd7e028 0x20ddfc002f9afc05 0xbfffe003ffffe07d 0xf7fffc007ffffc0f

def z195 : W := mkw 0x11101fa003281d87 0x022203f4006503b0 0xd7001fe01e001f86 0x7ae003fc03c003f0

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0c013e000000002 0xb818027c00000000

def z197 : W := mkw 0x05f49ec880000000 0x00be93d910000000 0xe7fe9ffce0000003 0xfcffd3ff9c000000

def z198 : W := mkw 0x06a940000c924000 0x00d5280001924800 0x9ff160001ffa6004 0xf3fe2c0003ff4c00

def z199 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x4ff013e01ff80e00 0xa9fe027c03ff01c0

def z200 : W := mkw 0x0effe76dfdfff6ee 0x61dffcedbfbffedd 0xffffffffffffffff 0xffffffffffffffff

def z201 : W := mkw 0x001027216128b4ae 0x200204e42c251695 0xf8f1ffe3f1ffffff 0xff1e3ffc7e3fffff

def z202 : W := mkw 0x15f49fe88bb81d87 0x02be93fd117703b0 0xfffe9ffcfff81f87 0xffffd3ff9fff03f0

def z203 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x0830e300e119e000 0x81061c601c233c00

def z204 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xf8fff3fcf1fffe67 0xff1ffe7f9e3fffcc

def z205 : W := mkw 0x0100180002000900 0x0020030000400120 0x40001c0000001f82 0x08000380000003f0

def z206 : W := mkw 0x034f985e96060b50 0x8069f30bd2c0c16a 0xf7cf9ffffe061fff 0xfef9f3ffffc0c3ff

def z207 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xffffffffe11fe007 0xfffffffffc23fc00

def z208 : W := mkw 0x15b03fa14bb83d8f 0x22b607f4297707b1 0xdff17fe31ffa7f9e 0xfbfe2ffc63ff4ff3

def z209 : W := mkw 0x37fdfffbcbb81d87 0x06ffbfff797703b0 0xfffffffffff81f87 0xffffffffffff03f0

def z210 : W := mkw 0x0010070001081084 0x000200e000210210 0x0830030001180000 0x8106006000230000

def z211 : W := mkw 0x000001002108b0ac 0x2000002004211615 0x18000000011ff1fc 0x030000000023fe3f

def z212 : W := mkw 0x15b01fa009b81487 0x02b603f401370290 0xcff01fe001f80002 0xf9fe03fc003f0000

def z213 : W := mkw 0x0000000000000000 0x0000000000000000 0x9830000001180004 0xd306000000230000

def z214 : W := mkw 0x0010260140000000 0x000204c028000000 0xa031ef03e0000003 0xd4063de07c000000

def z215 : W := mkw 0x0002000416060b50 0x8000400082c0c16a 0x100000001e061ffc 0x0200000003c0c3ff

def z216 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x9ffe00001ff80004 0xf3ffc00003ff0000

def z217 : W := mkw 0x000021016108b0ac 0x200004202c211615 0x3801e003e11ff1fd 0x07003c007c23fe3f

def z218 : W := mkw 0x030b191637069b74 0x80616322c6e0d36e 0xff0f9f1fff079fff 0xffe1f3e3ffe0f3ff

def z219 : W := mkw 0x021b2701750eb0ac 0x204364e02ea1d615 0xbf3fef03ff1ff1ff 0xf7e7fde07fe3fe3f

def z220 : W := mkw 0x08448168a1619426 0x4108902d142c3284 0xc8c093e0f1e19e06 0xb918127c1e3c33c0

def z221 : W := mkw 0x37fddffa8bb81d87 0x06ffbbff517703b0 0xdffe1ffc1ff81f86 0xfbffc3ff83ff03f0

def z222 : W := mkw 0x0044804880000000 0x0008900910000000 0x00c083e0e0000000 0x8018107c1c000000

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000000041067 0x140000000000820c

def z224 : W := mkw 0x020b000014060000 0x004160000280c000 0xb70f0c031e0611ff 0x76e1e18063c0c23f

def z225 : W := mkw 0x0846806c90650642 0x4108d00d920ca0c8 0xe0ce93fcf0e00e03 0xbc19d27f9e1c01c0

def z226 : W := mkw 0x024fc01614474250 0x8049f802c288e84a 0x200fe01f0007e079 0x0401fc03e000fc0f

def z227 : W := mkw 0x2044e049c0000000 0x04089c0938000000 0x0000e000e0000000 0x00001c001c000000

def z228 : W := mkw 0x0309181606020b50 0x80612302c0c0416a 0x77011c1f0e021ffa 0x4ee02383e1c043ff

def z229 : W := mkw 0x37fdfffbebb8bdaf 0x26ffbfff7d7717b5 0xffffffffffffffff 0xffffffffffffffff

def z230 : W := mkw 0x37fdfffbc9b81487 0x06ffbfff79370290 0xefffffffe1f80003 0xfdfffffffc3f0000

def z231 : W := mkw 0x04e4c00008d14000 0x009c9800011a2800 0x00c0000000e00000 0x00180000001c0000

def z232 : W := mkw 0x27fffedbdcd74000 0x04ffffdb7b9ae800 0xe7fffffffee00003 0xfcffffffffdc0000

def z233 : W := mkw 0x0000004880000000 0x0000000910000000 0x600013fce0000002 0x0c00027f9c000000

def z234 : W := mkw 0x06b966014c9a6088 0x20d72cc029934c11 0x17316c030e1a6198 0x42e62d8061c34c33

def z235 : W := mkw 0x224de05be000a028 0x2449bc0b7c001405 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z236 : W := mkw 0x04a0000008900000 0x0094000001120000 0x173000000e180000 0x42e6000001c30000

def z237 : W := mkw 0x0010260140082088 0x200204c028010411 0x0030600000186000 0x00060c0000030c00

def z238 : W := mkw 0x0856a76df16db6ee 0x610ad4edbe2db6dd 0xe8ce9ffff1e59fff 0xbd19d3fffe3cb3ff

def z239 : W := mkw 0x01103f176308bbfc 0xa02207e2ec61177f 0xf831ff1fe11fffff 0xdf063fe3fc23ffff

def z240 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x18316c03011ff1fc 0x43062d806023fe3f

def z241 : W := mkw 0x26fde6dbc0000000 0x04dfbcdb78000000 0x20ffe3ffe0000001 0x841ffc7ffc000000

def z242 : W := mkw 0x15b03f816b98b9ad 0x22b607f02d731735 0xbf31ef03ef1ff1ff 0xd7e63de07de3fe3f

def z243 : W := mkw 0x030b181610040240 0x00616302c2008048 0xe70f1c1f10041e67 0x7ce1e383e20083cc

def z244 : W := mkw 0x0100181602000b50 0x80200302c040016a 0xf0011c1f00061fff 0x5e002383e000c3ff

def z245 : W := mkw 0x17ffdfb61fff5fd7 0x82fffbf6c3ffebfa 0xffffffff1fffffff 0xffffffffe3ffffff

def z246 : W := mkw 0x0002000410040240 0x0000400082008048 0x200e001c00040061 0x0401c0038000800c

def z247 : W := mkw 0x2ffffffffdf7d666 0x45ffffffffbefacc 0xfffffffffffffe67 0xffffffffffffffcc

def z248 : W := mkw 0x11101fa003281d87 0x022203f4006503b0 0xc8c01fe011e01f86 0xb91803fc023c03f0

def z249 : W := mkw 0x101027216bb8bdaf 0x220204e42d7717b5 0xb831ef03ffffffff 0xd7063de07fffffff

def z250 : W := mkw 0x27fdfedbc2000900 0x04ffbfdb78400120 0xf7fffffffe001f87 0xfeffffffffc003f0

def z251 : W := mkw 0x0209001200000000 0x0041200240000000 0x200f001f00000001 0x0401e003e0000000

def z252 : W := mkw 0x1000012003281d87 0x02000024006503b0 0x0000000000001f80 0x00000000000003f0

def z253 : W := mkw 0x001027014108308c 0x200204e028210611 0x98316f03011a719e 0xd3062de060234e33

def z254 : W := mkw 0x0b4f985eb6478b70 0xc169f30bd6c8f16e 0xf70f9c1ffe079fff 0x7ee1f383ffc0f3ff

def z255 : W := mkw 0x17ffffa17ffffdaf 0x22fffff42fffffb5 0xffffffe3ffffffff 0xfffffffc7fffffff

def z256 : W := mkw 0x27fdffdbe1009024 0x04ffbffb7c201204 0xefffffffe1059067 0xfdfffffffc20b20c

def z257 : W := mkw 0x0309181206020910 0x8061230240c04122 0xf70f1c1f0e02019b 0x7ee1e383e1c04033

def z258 : W := mkw 0x031b1f16170e1bd4 0x806363e2c2e1c37a 0xff3f1f1f1f1e1fff 0xffe7e3e3e3e3c3ff

def z259 : W := mkw 0x0100180000000000 0x0020030000000000 0xc7001c0000000002 0x78e0038000000000

def z260 : W := mkw 0x0846806c90650642 0x4108d00d920ca0c8 0xc8ce90fc11e58e05 0xb919d21f823cb1c0

def z261 : W := mkw 0x15b01fa02bb89da7 0x02b603f4057713b4 0xfff09fe0fffd9fe7 0xfffe13fc1fffb3fc

def z262 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x07cfe0001ee7e001 0x20f9fc0003dcfc00

def z263 : W := mkw 0x27b97e9346020910 0x84f72fd268c04122 0x17316c030e020198 0x42e62d8061c04033

def z264 : W := mkw 0x024f800014470000 0x0049f0000288e000 0x9fcf80001fe78005 0xf3f9f00003fcf000

def z265 : W := mkw 0x15a018800a900901 0x02b4031001520120 0x070000000e000000 0x00e0000001c00000

def z266 : W := mkw 0x235dfedbc0000000 0x046bbfdb78000000 0x600fffffe0000003 0x0c01fffffc000000

def z267 : W := mkw 0x37edd8fa8ab00d03 0x06fdbb1f515601a0 0x47ce10fc1ee00e00 0x28f9c21f83dc01c0

def z268 : W := mkw 0x0309181202000900 0x0061230240400120 0xf70f1c1f1e001f87 0x7ee1e383e3c003f0

def z269 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000c03000011fa 0x040001806000023f

def z270 : W := mkw 0x1fff9ffebfff9ff7 0xc3fff3ffd7fff3fe 0xffff9fffffff9fff 0xfffff3fffffff3ff

def z271 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x273fec1fe0000001 0x44e7fd83fc000000

def z272 : W := mkw 0x17bb3fb77fbebfff 0xa2f767f6eff7d7ff 0xffffffffffffffff 0xffffffffffffffff

def z273 : W := mkw 0x27fdfedbc0082088 0x24ffbfdb78010411 0xf7ffffffe01a619b 0xfefffffffc034c33

def z274 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x28ce83fce1e58061 0x8519d07f9c3cb00c

def z275 : W := mkw 0x020b001614060250 0x80416002c280c04a 0xb70f001f1e06007d 0x76e1e003e3c0c00f

def z276 : W := mkw 0x030b181214060000 0x006163024280c000 0xf70f1c1f1e060007 0x7ee1e383e3c0c000

def z277 : W := mkw 0x1de699ecbbf59f67 0x43bcd33d977eb3ec 0xefce93fcffe59e67 0xbdf9d27f9ffcb3cc

def z278 : W := mkw 0x27fffedbd0450000 0x04ffffdb7a08a000 0xeffffffff1e58007 0xfdfffffffe3cb000

def z279 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xa031ef03e00011fb 0xd4063de07c00023f

def z280 : W := mkw 0x15b01fa02bb8bdaf 0x22b603f4057717b5 0xdff01fe01ffffffe 0xfbfe03fc03ffffff

def z281 : W := mkw 0x14a001200bb81d87 0x02940024017703b0 0x9ff000001ff81f84 0xf3fe000003ff03f0

def z282 : W := mkw 0x0846804cb0458260 0x4108d0099608b04c 0xe0ce93fce0058063 0xbc19d27f9c00b00c

def z283 : W := mkw 0x11103fa16328bdaf 0x222207f42c6517b5 0x60001fe3e0001ffa 0x0c0003fc7c0003ff

def z284 : W := mkw 0x06efc0041cd74240 0x00ddf800839ae848 0xfffff01c1ffffe67 0xfffffe0383ffffcc

def z285 : W := mkw 0x0002000410040240 0x0000400082008048 0xe00e101c10041e67 0x3c01c203820083cc

def z286 : W := mkw 0x11103fa16328bdaf 0x222207f42c6517b5 0xf831ffe3e11fffff 0xdf063ffc7c23ffff

def z287 : W := mkw 0x15b01e800a980981 0x02b603d001530130 0x9ff00c001ff80184 0xf3fe018003ff0030

def z288 : W := mkw 0x0800012421209666 0x41000024842412cc 0x0000000000001e60 0x00000000000003cc

def z289 : W := mkw 0x0802000430458260 0x410040008608b04c 0x0000000000058060 0x000000000000b00c

def z290 : W := mkw 0x17bb1fa01fbe1d87 0x02f763f403f7c3b0 0xdfff1fe01ffe1f87 0xfbffe3fc03ffc3f0

def z291 : W := mkw 0x030b181216060910 0x8061630242c0c122 0x970f0c031e06019d 0x72e1e18063c0c033

def z292 : W := mkw 0x17ffde801edf4981 0x02fffbd003dbe930 0x9fffec001fffe185 0xf3fffd8003fffc30

def z293 : W := mkw 0x37fdfedbca980981 0x06ffbfdb79530130 0xf7ffffffee180183 0xfefffffffdc30030

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x10010c0300020198 0x4200218060004033

def z295 : W := mkw 0x0846804c90450240 0x4108d0099208a048 0x000e001c00000000 0x0001c00380000000

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000011fe004 0x030000000023fc00

def z297 : W := mkw 0x1fffdfecbfffdfe7 0x43fffbfd97fffbfc 0xfffffffcffffffe7 0xffffffff9ffffffc

def z298 : W := mkw 0x06ab40001cd74000 0x00d56800039ae800 0x1f3160001fffe004 0x43e62c0003fffc00

def z299 : W := mkw 0x07ffde801cd74000 0x00fffbd0039ae800 0xdfffffe01fffe007 0xfbfffffc03fffc00

def z300 : W := mkw 0x0309181200000000 0x0061230240000000 0x07010c0300000000 0x40e0218060000000

def z301 : W := mkw 0x05b01e8002000900 0x00b603d000400120 0xd7f01fe01e001f86 0xfafe03fc03c003f0

def z302 : W := mkw 0x15b03fa14bb81d87 0x02b607f4297703b0 0xfff1ffe3fff81f87 0xfffe3ffc7fff03f0

def z303 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x9831e300e11fe005 0xd3063c601c23fc00

def z304 : W := mkw 0x04a0400008904000 0x0094080001120800 0x0030600000186000 0x00060c0000030c00

def z305 : W := mkw 0x00122705770ebbfc 0xa00244e0aee1d77f 0xb831ef03ff1fffff 0xd7063de07fe3ffff

def z306 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000100010001e06 0x38000200020003c0

def z307 : W := mkw 0x034d985a80000000 0x0069b30b50000000 0xe7cf9fffe0000003 0xfcf9f3fffc000000

def z308 : W := mkw 0x27b97e934c924000 0x04f72fd269924800 0x17316c030e1a6000 0x42e62d8061c34c00

def z309 : W := mkw 0x0044804880000000 0x0008900910000000 0x200e801ce0000001 0x0401d0039c000000

def z310 : W := mkw 0x27bb7e9756060b50 0x84f76fd2eac0c16a 0xf73f7c1f1e061fff 0x7ee7ef83e3c0c3ff

def z311 : W := mkw 0x01103f176308bbfc 0xa02207e2ec61177f 0x60001f1fe0001ffa 0x0c0003e3fc0003ff

def z312 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x1fce00001fffe004 0x23f9c00003fffc00

def z313 : W := mkw 0x001026016000a028 0x200204c02c001405 0xa031ef03e007e07b 0xd4063de07c00fc0f

def z314 : W := mkw 0x0002000410040240 0x0000400082008048 0x400e101c10000e00 0x2801c203820001c0

def z315 : W := mkw 0x021b2717750eb2fc 0xa04364e2eea1d65f 0xb83fef1fe11ff1ff 0xd707fde3fc23fe3f

def z316 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0008300e0000003 0x940010601c000000

def z317 : W := mkw 0x100201241fbe1fd7 0x8200402483f7c3fa 0x180000001ffe1ffc 0x0300000003ffc3ff

def z318 : W := mkw 0x225de65bc0000000 0x044bbccb78000000 0xa03fef1fe0000003 0xd407fde3fc000000

def z319 : W := mkw 0x020b001614060250 0x80416002c280c04a 0xb00f0c1f000611ff 0x5601e183e000c23f

def z320 : W := mkw 0x0900197ea3209f76 0xc120032fd46413ee 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z321 : W := mkw 0x05b01e8008900000 0x00b603d001120000 0xdff01fe01ff80006 0xfbfe03fc03ff0000

def z322 : W := mkw 0x21103fdbe108b0ac 0x242207fb7c211615 0x60001fffe00011fa 0x0c0003fffc00023f

def z323 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x48f01fe001f81f82 0x891e03fc003f03f0

def z324 : W := mkw 0x07edd81200000000 0x00fdbb0240000000 0xe7fffc1f00000003 0xfcffff83e0000000

def z325 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x1ff00fe00ff80180 0xc3fe01fc01ff0030

def z326 : W := mkw 0x0102181616060b50 0x80204302c2c0c16a 0x70001c1f1e061ffe 0x0e000383e3c0c3ff

def z327 : W := mkw 0x224dc05a80000000 0x0449b80b50000000 0x000e001c00000000 0x0001c00380000000

def z328 : W := mkw 0x08448168a1619426 0x4108902d142c3284 0xe8ce93fce1e18003 0xbd19d27f9c3c3000

def z329 : W := mkw 0x06efc00014474000 0x00ddf8000288e800 0x87ffe0000007e001 0xf0fffc000000fc00

def z330 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x00000300e0000000 0x000000601c000000

def z331 : W := mkw 0x030b38177606ab78 0xa0616702eec0d56f 0xf70ffc1ffe07ffff 0x7ee1ff83ffc0ffff

def z332 : W := mkw 0x37fdfffbc3281d87 0x06ffbfff786503b0 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z333 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xd70e1c1c1e001f86 0x7ae1c38383c003f0

def z334 : W := mkw 0x07ab18161e960b50 0x80f56302c3d2c16a 0xffff1c1f1ffe1fff 0xffffe383e3ffc3ff

def z335 : W := mkw 0x0800012021619426 0x41000024042c3284 0x0800000001e18000 0x01000000003c3000

def z336 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x47c01fe01ee01f82 0x28f803fc03dc03f0

def z337 : W := mkw 0x0946996cb3659f66 0x4128d32d966cb3ec 0xffce9ffcffe59fe7 0xfff9d3ff9ffcb3fc

def z338 : W := mkw 0x16efc1201fff5d87 0x02ddf82403ffebb0 0x9fffe0001fffff85 0xf3fffc0003fffff0

def z339 : W := mkw 0x06ffc7001ddf5084 0x00dff8e003bbea10 0x9fffef001ffff187 0xf3fffde003fffe30

def z340 : W := mkw 0x0010060000000000 0x000200c000000000 0x80300f0000000002 0xd00601e000000000

def z341 : W := mkw 0x07efd8161ed74b50 0x80fdfb02c3dae96a 0x47ce101c1ee00e00 0x28f9c20383dc01c0

def z342 : W := mkw 0x27fffedfd4060250 0x84ffffdbfa80c04a 0xe7ffffffe006007b 0xfcfffffffc00c00f

def z343 : W := mkw 0x0a4fc16cb567d666 0x4149f82d96acfacc 0xe8cff3fcf1e7fe67 0xbd19fe7f9e3cffcc

def z344 : W := mkw 0x2a4fe05ff0458260 0x4549fc0bfe08b04c 0x200fe01fe0058061 0x0401fc03fc00b00c

def z345 : W := mkw 0x100001202bb8bdaf 0x22000024057717b5 0x180000001ffffffc 0x0300000003ffffff

def z346 : W := mkw 0x24f4e7c9e108b0ac 0x249e9cf93c211615 0x08f0e3e0e119e000 0x811e1c7c1c233c00

def z347 : W := mkw 0x024fc00014474000 0x0049f8000288e800 0x970fe0001e07e005 0x72e1fc0003c0fc00

def z348 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x2001ef03e007f1fb 0x04003de07c00fe3f

def z349 : W := mkw 0x14b007a009b81487 0x029600f401370290 0x9ff003e01ff80004 0xf3fe007c03ff0000

def z350 : W := mkw 0x14b007a009b81487 0x029600f401370290 0xc8f013e011f81e06 0xb91e027c023f03c0

def z351 : W := mkw 0x0044800000410000 0x0008900000082000 0x08c0800001e18000 0x81181000003c3000

def z352 : W := mkw 0x27fffedfd0040240 0x04ffffdbfa008048 0xe7fffffff0041e67 0xfcfffffffe0083cc

def z353 : W := mkw 0x06efc0161cd74250 0x80ddf802c39ae84a 0xbfffe01f1fffe07d 0xf7fffc03e3fffc0f

def z354 : W := mkw 0x04e4c00008d14000 0x009c9800011a2800 0x98f1e00001ffe005 0xd31e3c00003ffc00

def z355 : W := mkw 0x27fffedfded74b50 0x84ffffdbfbdae96a 0xffffffffffffffff 0xffffffffffffffff

def z356 : W := mkw 0x06edc00008d14000 0x00ddb800011a2800 0x8fffe00001f9e001 0xf1fffc00003f3c00

def z357 : W := mkw 0x14b0068008980081 0x029600d001130010 0x0030000000180000 0x0006000000030000

def z358 : W := mkw 0x3ffffffffbfd9fe7 0x47ffffffff7fb3fc 0xfffffffffffd9fe7 0xffffffffffffb3fc

def z359 : W := mkw 0x0309181206020910 0x8061230240c04122 0xd7011c031e021f9e 0x7ae0238063c043f3

def z360 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x1f300c001ff81f84 0x43e6018003ff03f0

def z361 : W := mkw 0x06efc1003dd7d024 0x00ddf82007bafa04 0xbfffe300fffff067 0xf7fffc601ffffe0c

def z362 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x48ce10fc11e59e64 0x2919c21f823cb3cc

def z363 : W := mkw 0x0100181200000000 0x0020030240000000 0x60001c1f00000002 0x0c000383e0000000

def z364 : W := mkw 0x0a4f817eb5679676 0xc149f02fd6acf2ce 0xe8cf93fff1e79e7f 0xbd19f27ffe3cf3cf

def z365 : W := mkw 0x031b3e17560e2bd8 0xa06367c2eac1c57b 0xf73f7c1f1e1e7fff 0x7ee7ef83e3c3cfff

def z366 : W := mkw 0x0000200140000000 0x0000040028000000 0x2001e003e0000001 0x04003c007c000000

def z367 : W := mkw 0x19101feca3289fe7 0x432203fd946513fc 0x60001ffce0001fe2 0x0c0003ff9c0003fc

def z368 : W := mkw 0x14a000a008b00403 0x0294001401160080 0x00c000e000e00000 0x0018001c001c0000

def z369 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0xdff010e01ff80e04 0xfbfe021c03ff01c0

def z370 : W := mkw 0x0000010001001004 0x0000002000200200 0x8800030001001006 0x9100006000200200

def z371 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xe70e101c1e041e67 0x3ce1c20383c083cc

def z372 : W := mkw 0x0100181602000b50 0x80200302c040016a 0xf7001c1f1e001ffe 0x7ee00383e3c003ff

def z373 : W := mkw 0x0100181202000910 0x8020030240400122 0x00000c0300000198 0x0000018060000033

def z374 : W := mkw 0x0eefc04cbcd7c260 0x41ddf809979af84c 0xbfffe01cffffe065 0xf7fffc039ffffc0c

def z375 : W := mkw 0x27edf8dbc0000000 0x04fdbf1b78000000 0x67cff0ffe0000001 0x2cf9fe1ffc000000

def z376 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x0ffee0001ff9e000 0xa1ffdc0003ff3c00

def z377 : W := mkw 0x15b01ea00ab80d83 0x02b603d4015701b0 0x57f01ce01ef80f80 0x6afe039c03df01f0

def z378 : W := mkw 0x201026c9c0000000 0x040204d938000000 0x000003e0e0000000 0x0000007c1c000000

def z379 : W := mkw 0x04e6c0001cd74000 0x009cd800039ae800 0x18f0e0001fffe004 0x831e1c0003fffc00

def z380 : W := mkw 0x27edd8da80000000 0x04fdbb1b50000000 0xe7ce93fce0000003 0xbcf9d27f9c000000

def z381 : W := mkw 0x0010260140000000 0x000204c028000000 0x00316c0300000000 0x40062d8060000000

def z382 : W := mkw 0x0eefc168bdf7d426 0x41ddf82d17befa84 0x9fffe3e0ffffe005 0xf3fffc7c1ffffc00

def z383 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0xe80e101c11e59e67 0x3d01c203823cb3cc

def z384 : W := mkw 0x06edc00008900000 0x00ddb80001120000 0x9fffe0001ff80005 0xf3fffc0003ff0000

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000000000611fc 0x020000000000c23f

def z386 : W := mkw 0x24e4c0c880000000 0x049c981910000000 0x00c000e000000000 0x0018001c00000000

def z387 : W := mkw 0x0846806c90650642 0x4108d00d920ca0c8 0xe0ce10fc10e41e67 0x3c19c21f821c83cc

def z388 : W := mkw 0x024fc00014474000 0x0049f8000288e800 0x000e000000000000 0x0001c00000000000

def z389 : W := mkw 0x0800016ca1209666 0x4100002d942412cc 0xe8c013fcf1e01e66 0xbd18027f9e3c03cc

def z390 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xf7ffffffe00611ff 0xfefffffffc00c23f

def z391 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001e0000007e001 0x00003c000000fc00

def z392 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x17ff60001efa6000 0x62ffec0003df4c00

def z393 : W := mkw 0x0846816cb16db6ee 0x6108d02d962db6dd 0xf8ce93fcf1ffffff 0xbf19d27f9e3fffff

def z394 : W := mkw 0x0010060000080080 0x000200c000010010 0x10300c0000180180 0x4206018000030030

def z395 : W := mkw 0x0eefc06c9cf74642 0x41ddf80d939ee8c8 0xdffff0fc1fffee05 0xfbfffe1f83fffdc0

def z396 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z397 : W := mkw 0x0046800010450000 0x0008d0000208a000 0x98ffe00011ffe005 0xf31ffc00023ffc00

def z398 : W := mkw 0x15b01f800b981985 0x02b603f001730330 0x9f300f000f181186 0xd3e601e001e30230

def z399 : W := mkw 0x15b21fa01fff5d87 0x02b643f403ffebb0 0xdff01fe01fffff86 0xfbfe03fc03fffff0

def z400 : W := mkw 0x020b20177406a278 0xa0416402ee80d44f 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z401 : W := mkw 0x27b97e9340082088 0x24f72fd268010411 0x17316c03001a6198 0x42e62d8060034c33

def z402 : W := mkw 0x15b01fb60bb81fd7 0x82b603f6c17703fa 0xfff01fff1ff81ffe 0xfffe03ffe3ff03ff

def z403 : W := mkw 0x23193edbc0000000 0x046327db78000000 0xe70f1fffe0000003 0x7ce1e3fffc000000

def z404 : W := mkw 0x05b01f8001081084 0x00b603f000210210 0xdff01fe001181186 0xfbfe03fc00230230

def z405 : W := mkw 0x234ff85fd6060b50 0x8469ff0bfac0c16a 0xf70ffc1ffe061fff 0x7ee1ff83ffc0c3ff

def z406 : W := mkw 0x07efd8161ed74b50 0x80fdfb02c3dae96a 0xdffff01c1fffee05 0xfbfffe0383fffdc0

def z407 : W := mkw 0x031b3f17770ebbfc 0xa06367e2eee1d77f 0xf70f1f1ffe061fff 0x7ee1e3e3ffc0c3ff

def z408 : W := mkw 0x04a0000008900000 0x0094000001120000 0x07c000001ee00000 0x20f8000003dc0000

def z409 : W := mkw 0x0000000000000000 0x0000000000000000 0xb831ec03011ff1ff 0xd7063d806023fe3f

def z410 : W := mkw 0x030b193617261f56 0x80616326c2e4c3ea 0xffcf1fff1fe61fff 0xfff9e3ffe3fcc3ff

def z411 : W := mkw 0x06ffe7017ddff0ac 0x20dffce02fbbfe15 0x9fffe300ffffe005 0xf3fffc601ffffc00

def z412 : W := mkw 0x131b1fb6172e1fd7 0x826363f6c2e5c3fa 0xf70f1fff1e061fff 0x7ee1e3ffe3c0c3ff

def z413 : W := mkw 0x06a9400000000000 0x00d5280000000000 0x0731600000000000 0x40e62c0000000000

def z414 : W := mkw 0x030b18161ed74b50 0x80616302c3dae96a 0xff0f1c1f1fffffff 0x7fe1e383e3ffffff

def z415 : W := mkw 0x0309181206020910 0x8061230240c04122 0x070000000e000000 0x00e0000001c00000

def z416 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x38000f03e11ff1fe 0x070001e07c23fe3f

def z417 : W := mkw 0x0b0b193637679f76 0xc1616326c6ecf3ee 0xff0f1c1f1fe79fff 0x7fe1e383e3fcf3ff

def z418 : W := mkw 0x06fde60140000000 0x00dfbcc028000000 0xa7ffef03e0000003 0xf4fffde07c000000

def z419 : W := mkw 0x0846814cb1459264 0x4108d0299628b24c 0xa80e831ce1059067 0x9501d0639c20b20c

def z420 : W := mkw 0x04b0068000000000 0x009600d000000000 0x00f003e000000000 0x801e007c00000000

def z421 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xdff0ffe0fff9ff86 0xfbfe1ffc1fff3ff0

def z422 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x570f1c1f1e020f98 0x6ae1e383e3c041f3

def z423 : W := mkw 0x0010260140082088 0x200204c028010411 0x00000c0300000198 0x0000018060000033

def z424 : W := mkw 0x0000010001081084 0x0000002000210210 0x1800000001181184 0x0300000000230230

def z425 : W := mkw 0x0000012001201406 0x0000002400240280 0x0800000011e01e04 0x01000000023c03c0

def z426 : W := mkw 0x27efd8da9cd74000 0x04fdfb1b539ae800 0xdffff0fc1fffe005 0xfbfffe1f83fffc00

def z427 : W := mkw 0x0044c00000414000 0x0008980000082800 0x0000e0000001e000 0x00001c0000003c00

def z428 : W := mkw 0x37fdfefbcab00d03 0x06ffbfdf795601a0 0xe7fffffffee00e03 0xfcffffffffdc01c0

def z429 : W := mkw 0x25f4fec9c0000000 0x04be9fd938000000 0xc7f0ffe0e0000002 0xf8fe1ffc1c000000

def z430 : W := mkw 0x11101e8002080981 0x022203d000410130 0x00000c0000000180 0x0000018000000030

def z431 : W := mkw 0x0ce6816cb9f59666 0x419cd02d973eb2cc 0xfffe93fcfffd9e67 0xffffd27f9fffb3cc

def z432 : W := mkw 0x06edc00000000000 0x00ddb80000000000 0x07ce000000000000 0x20f9c00000000000

def z433 : W := mkw 0x0002000014060000 0x000040000280c000 0x100000001e060004 0x0200000003c0c000

def z434 : W := mkw 0x0000000008d14000 0x00000000011a2800 0x0800000001f9e000 0x01000000003f3c00

def z435 : W := mkw 0x01101e8000000000 0x002203d000000000 0x40001fe000000002 0x080003fc00000000

def z436 : W := mkw 0x06fde7016108b0ac 0x20dfbce02c211615 0xbfffef03e11ff1ff 0xf7fffde07c23fe3f

def z437 : W := mkw 0x00020104370ebbfc 0xa000402086e1d77f 0x180000001f1ffffc 0x0300000003e3ffff

def z438 : W := mkw 0x000200041ed74b50 0x8000400083dae96a 0x180000001ffffffc 0x0300000003ffffff

def z439 : W := mkw 0x0b5fbf7ff76fbffe 0xe16bf7effeedf7ff 0xffffffffffffffff 0xffffffffffffffff

def z440 : W := mkw 0x000201003ddff0ac 0x2000402007bbfe15 0x180000001ffff1fc 0x0300000003fffe3f

def z441 : W := mkw 0x15a019a00bb01d07 0x02b40334017603a0 0xcfc013e01fe01e06 0xb9f8027c03fc03c0

def z442 : W := mkw 0x1df69fec9bfd1fc7 0x43bed3fd937fa3f8 0xdffe1ffc1ff81f86 0xfbffc3ff83ff03f0

def z443 : W := mkw 0x2154bedbc0000000 0x042a97db78000000 0xe0ce9fffe0000003 0xbc19d3fffc000000

def z444 : W := mkw 0x1db01fecabb89fe7 0x43b603fd957713fc 0xfff01ffcfff81fe6 0xfffe03ff9fff03fc

def z445 : W := mkw 0x14f4c7a009f95487 0x029e98f4013f2a90 0x08f0e3e001f9e000 0x811e1c7c003f3c00

def z446 : W := mkw 0x05b01e8000000000 0x00b603d000000000 0x07300c0000000000 0x40e6018000000000

def z447 : W := mkw 0x26efe05bdcd74000 0x04ddfc0b7b9ae800 0xbfffe01fffffe005 0xf7fffc03fffffc00

def z448 : W := mkw 0x2ffdffffe1209666 0x45ffbffffc2412cc 0xe7ffffffe0001e63 0xfcfffffffc0003cc

def z449 : W := mkw 0x05a0188000000000 0x00b4031000000000 0x47c010e000000000 0x28f8021c00000000

def z450 : W := mkw 0x06edc0000c924000 0x00ddb80001924800 0x97ffe0000e1a6001 0xf2fffc0001c34c00

def z451 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x60ce13fcf0e01e62 0x2c19c27f9e1c03cc

def z452 : W := mkw 0x0002000416060b50 0x8000400082c0c16a 0xb0010c031e061fff 0x5600218063c0c3ff

def z453 : W := mkw 0x08000168a1209426 0x4100002d14241284 0x000003e0e0000000 0x0000007c1c000000

def z454 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xa830e300e11df067 0x95061c601c23be0c

def z455 : W := mkw 0x07efd81616060b50 0x80fdfb02c2c0c16a 0xf7fffc1f1e061fff 0xfeffff83e3c0c3ff

def z456 : W := mkw 0x0044804880000000 0x0008900910000000 0x40ce10fc00000000 0x2819c21f80000000

def z457 : W := mkw 0x0046800010450000 0x0008d0000208a000 0x000e800000058001 0x0001d0000000b000

def z458 : W := mkw 0x224de05bc0000000 0x0449bc0b78000000 0xe0cff3ffe0000003 0xbc19fe7ffc000000

def z459 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x670f101f1e060e79 0x2ce1e203e3c0c1cf

def z460 : W := mkw 0x17b91e920e9a0991 0x82f723d241d34132 0x17310c030e1a0198 0x42e6218061c34033

def z461 : W := mkw 0x14b007a00bb81d87 0x029600f4017703b0 0x18f003e01ff81f84 0x831e007c03ff03f0

def z462 : W := mkw 0x0044800000000000 0x0008900000000000 0x80ce800000000001 0xb019d00000000000

def z463 : W := mkw 0x0002000010450000 0x000040000208a000 0x0800000011e58004 0x01000000023cb000

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000001e000004 0x72e0000003c00000

def z465 : W := mkw 0x0002012411241646 0x00004024822482c8 0xe8ce13fc11e41e67 0xbd19c27f823c83cc

def z466 : W := mkw 0x27fffedfd6060b50 0x84ffffdbfac0c16a 0xe7fffffffe000e03 0xfcffffffffc001c0

def z467 : W := mkw 0x27b97edbc0000000 0x04f72fdb78000000 0x67317fffe0000002 0x4ce62ffffc000000

def z468 : W := mkw 0x06a940000c924000 0x00d5280001924800 0x070000000e000000 0x00e0000001c00000

def z469 : W := mkw 0x2ffffeffd0650642 0x45ffffdffa0ca0c8 0xe7fffffff0e00e03 0xfcfffffffe1c01c0

def z470 : W := mkw 0x15b01e800a980981 0x02b603d001530130 0xd7f01fe00e180182 0xfafe03fc01c30030

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x2001000300060079 0x040020006000c00f

def z472 : W := mkw 0x27edd8da80000000 0x04fdbb1b50000000 0xc7fff0fc00000001 0xf8fffe1f80000000

def z473 : W := mkw 0x0046800010450000 0x0008d0000208a000 0x00ce000010e00000 0x2019c000021c0000

def z474 : W := mkw 0x05b03e8140000000 0x00b607d028000000 0xe7f1ffe3e0000003 0xfcfe3ffc7c000000

def z475 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0xd7c01ce01ee01f86 0x7af8039c03dc03f0

def z476 : W := mkw 0x37ffffffdfbe1fd7 0x86fffffffbf7c3fa 0xfffffffffffe1fff 0xffffffffffffc3ff

def z477 : W := mkw 0x15b01fa003281d87 0x02b603f4006503b0 0xc7f01fe000001f82 0xf8fe03fc000003f0

def z478 : W := mkw 0x0844816ca1619666 0x4108902d942c32cc 0x68c093fce1e19e62 0x8d18127f9c3c33cc

def z479 : W := mkw 0x26ede05bc0000000 0x04ddbc0b78000000 0xa7ffe01fe0000001 0xf4fffc03fc000000

def z480 : W := mkw 0x000001002108b0ac 0x2000002004211615 0xb8010c03011ff1ff 0x570021806023fe3f

def z481 : W := mkw 0x26ffe6c9dcd74000 0x04dffcd93b9ae800 0x9fffe3e0ffffe005 0xf3fffc7c1ffffc00

def z482 : W := mkw 0x0eefc06c9cf74642 0x41ddf80d939ee8c8 0x47ce10fc1ee00e00 0x28f9c21f83dc01c0

def z483 : W := mkw 0x0000000020008020 0x0000000004001004 0x20008000e0058061 0x040010001c00b00c

def z484 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x2830ef03e119f1fa 0x85061de07c233e3f

def z485 : W := mkw 0x0000002000200402 0x0000000400040080 0x40c010e010e00e00 0x2818021c021c01c0

def z486 : W := mkw 0x27b97e9340000000 0x04f72fd268000000 0xe73f7c1f00000003 0x7ce7ef83e0000000

def z487 : W := mkw 0x15b01ea00ab00d03 0x02b603d4015601a0 0xc7f01fe01ee00e02 0xf8fe03fc03dc01c0

def z488 : W := mkw 0x0000010021009024 0x0000002004201204 0xb8018f03e10791ff 0xd70031e07c20f23f

def z489 : W := mkw 0x0044816881201406 0x0008902d10240280 0xe8ce93fcf1e01e07 0xbd19d27f9e3c03c0

def z490 : W := mkw 0x101007a001281487 0x020200f400250290 0x000003e000000000 0x0000007c00000000

def z491 : W := mkw 0x37b97fb34bb81d87 0x06f72ff6697703b0 0xdff17fe31ff81f86 0xfbfe2ffc63ff03f0

def z492 : W := mkw 0x17fddfa00bb81d87 0x02ffbbf4017703b0 0xdfffffe01ff81f87 0xfbfffffc03ff03f0

def z493 : W := mkw 0x210018da80000000 0x0420031b50000000 0x400010fc00000000 0x0800021f80000000

def z494 : W := mkw 0x04e4c00000000000 0x009c980000000000 0x00f0e00000000000 0x801e1c0000000000

def z495 : W := mkw 0x27fffedbd4474000 0x04ffffdb7a88e800 0xe7ffffffe007e003 0xfcfffffffc00fc00

def z496 : W := mkw 0x080201243df7d666 0x4100402487befacc 0x180000001ffffe64 0x0300000003ffffcc

def z497 : W := mkw 0x17bb1e961e9e0bd1 0x82f763d2c3d3c17a 0xf73f1c1f1e1e1fff 0x7ee7e383e3c3c3ff

def z498 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x1831ef03e11be198 0xc3063de07c237c33

def z499 : W := mkw 0x0002000014474000 0x000040000288e800 0x000000000007e000 0x000000000000fc00

def z500 : W := mkw 0x2956bffff1659666 0x452ad7fffe2cb2cc 0xe8ce9ffff1e59e67 0xbd19d3fffe3cb3cc

def z501 : W := mkw 0x24f4e6c9c0000000 0x049e9cd938000000 0xa0f1efe3e0000003 0xd41e3dfc7c000000

def z502 : W := mkw 0x0a4f805eb4478270 0xc149f00bd688f04e 0x200f801fe0078079 0x0401f003fc00f00f

def z503 : W := mkw 0x2000205bc0000000 0x0400040b78000000 0x2000001fe0000000 0x04000003fc000000

def z504 : W := mkw 0x0846812431659666 0x4108d024862cb2cc 0x88ce800011e59e65 0xb119d000023cb3cc

def z505 : W := mkw 0x17ffdfa01fff5d87 0x02fffbf403ffebb0 0xdffe1fe01ff81f86 0xfbffc3fc03ff03f0

def z506 : W := mkw 0x26fde6c9c0000000 0x04dfbcd938000000 0x87ffe3e0e0000001 0xf0fffc7c1c000000

def z507 : W := mkw 0x004680001cd74000 0x0008d000039ae800 0x98ce80001fffe005 0xb319d00003fffc00

def z508 : W := mkw 0x31103ffbc3281d87 0x062207ff786503b0 0x60001fffe0001f82 0x0c0003fffc0003f0

def z509 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x47ff7cff00000000 0x68ffef9fe0000000

def z510 : W := mkw 0x0002000414060250 0x800040008280c04a 0x0000000000060078 0x000000000000c00f

def z511 : W := mkw 0x000020016000a028 0x200004002c001405 0xb001ec03e007f1ff 0x56003d807c00fe3f

def z512 : W := mkw 0x0010260140000000 0x000204c028000000 0xb831ef03e11fe007 0xd7063de07c23fc00

def z513 : W := mkw 0x0002010431049264 0x000040208620924c 0xe80e931cf1059e67 0xbd01d2639e20b3cc

def z514 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x280e801cf1e59e65 0x0501d0039e3cb3cc

def z515 : W := mkw 0x1de698ec9af50f43 0x43bcd31d935ea1e8 0x47ce10fc1ee00e00 0x28f9c21f83dc01c0

def z516 : W := mkw 0x0854a769e169b4ae 0x610a94ed3c2d3695 0x08f0e3e0e1f9e000 0x811e1c7c1c3f3c00

def z517 : W := mkw 0x27fddeda80000000 0x04ffbbdb50000000 0xc7fe1ffc00000002 0xf8ffc3ff80000000

def z518 : W := mkw 0x0846804cb0458260 0x4108d0099608b04c 0xe00e901cf0059e67 0x3c01d2039e00b3cc

def z519 : W := mkw 0x04a200001cd74000 0x00944000039ae800 0x9ff000001fffe004 0xf3fe000003fffc00

def z520 : W := mkw 0x07ffff177fdffbfc 0xa0ffffe2effbff7f 0xffffff1fffffffff 0xffffffe3ffffffff

def z521 : W := mkw 0x04f4e70169d9f0ac 0x209e9ce02d3b3e15 0x08f0e300e1f9e000 0x811e1c601c3f3c00

def z522 : W := mkw 0x04f4e70169d9f0ac 0x209e9ce02d3b3e15 0xb8f1ef03e1fff1ff 0xd71e3de07c3ffe3f

def z523 : W := mkw 0x0802016cb1659666 0x4100402d962cb2cc 0x680013fcf1e59e66 0x0d00027f9e3cb3cc

def z524 : W := mkw 0x17bb1fb61fbe1fd7 0x82f763f6c3f7c3fa 0xdffe1ffc1ff81f86 0xfbffc3ff83ff03f0

def z525 : W := mkw 0x17b91fb20fba1d97 0x82f723f641f743b2 0xdff11fe31ffa1f9e 0xfbfe23fc63ff43f3

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x0830e0000119e000 0x81061c0000233c00

def z527 : W := mkw 0x224fe05fd4060250 0x8449fc0bfa80c04a 0x200fe01fe0060079 0x0401fc03fc00c00f

def z528 : W := mkw 0x04e6800018d50000 0x009cd000031aa000 0x9ffe80001ffd8005 0xf3ffd00003ffb000

def z529 : W := mkw 0x27fffedbd4060000 0x04ffffdb7a80c000 0xf7fffffffe060007 0xfeffffffffc0c000

def z530 : W := mkw 0x25b03edbc0000000 0x04b607db78000000 0xe7f01fffe0000002 0xfcfe03fffc000000

def z531 : W := mkw 0x0844816ca1209666 0x4108902d942412cc 0xe0ce93fce0001e63 0xbc19d27f9c0003cc

def z532 : W := mkw 0x0000000008900000 0x0000000001120000 0x180000001ff80004 0x0300000003ff0000

def z533 : W := mkw 0x0010070001081084 0x000200e000210210 0x00000f0000001182 0x000001e000000230

def z534 : W := mkw 0x2ffdfffbe1619426 0x45ffbfff7c2c3284 0xefffffffe1e18003 0xfdfffffffc3c3000

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0x90000c0000001186 0x5200018000000230

def z536 : W := mkw 0x06edc00000000000 0x00ddb80000000000 0x9fffe000011fe005 0xf3fffc000023fc00

def z537 : W := mkw 0x0002000010040000 0x0000400002008000 0x800e000010040005 0x3001c00002008000

def z538 : W := mkw 0x231b3edfd6060b50 0x846367dbfac0c16a 0xf70f1ffffe061fff 0x7ee1e3ffffc0c3ff

def z539 : W := mkw 0x00122705710cb2ec 0x200244e0ae21965d 0xf83fff1ff11fffff 0xff07ffe3fe23ffff

def z540 : W := mkw 0x07efd8121cd74000 0x00fdfb02439ae800 0xfffffc1f1fffe007 0xffffff83e3fffc00

def z541 : W := mkw 0x110019200bb81d87 0x02200324017703b0 0xdf001c001ff81f86 0x7be0038003ff03f0

def z542 : W := mkw 0x0856a76df16db6ee 0x610ad4edbe2db6dd 0xe8fef3fcf1fdfe67 0xbd1fde7f9e3fbfcc

def z543 : W := mkw 0x0010260140000000 0x000204c028000000 0x20000f03e0000002 0x040001e07c000000

def z544 : W := mkw 0x27efd8de96060b50 0x84fdfb1bd2c0c16a 0xf7cf1cff1e061fff 0x7ef9e39fe3c0c3ff

def z545 : W := mkw 0x0000012001201406 0x0000002400240280 0x08c003e001e00000 0x8118007c003c0000

def z546 : W := mkw 0x07fdde8000000000 0x00ffbbd000000000 0xc7ffffe000000003 0xf8fffffc00000000

def z547 : W := mkw 0x0b4f987e96670f52 0xc169f30fd2cce1ea 0xf7cf1cff1ee61fff 0x7ef9e39fe3dcc3ff

def z548 : W := mkw 0x0010260140082088 0x200204c028010411 0x9831ec03011fe19d 0xd3063d806023fc33

def z549 : W := mkw 0x0eefc16cbdf7d666 0x41ddf82d97befacc 0xefce93fcffe59e67 0xbdf9d27f9ffcb3cc

def z550 : W := mkw 0x0846816c91651646 0x4108d02d922ca2c8 0xc8ce13fc11e01e06 0xb919c27f823c03c0

def z551 : W := mkw 0x030b1916370ebbfc 0xa0616322c6e1d77f 0xff0f1c1f1f1fffff 0x7fe1e383e3e3ffff

def z552 : W := mkw 0x16ffc7a01dff5487 0x02dff8f403bfea90 0x9fffe3e01fffe005 0xf3fffc7c03fffc00

def z553 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xf8cf9ffff1e79fff 0xff19f3fffe3cf3ff

def z554 : W := mkw 0x0844806880610402 0x4108900d100c2080 0x00c000e000e00000 0x0018001c001c0000

def z555 : W := mkw 0x01101f0003081984 0x002203e000610330 0xdf301f001f181f86 0xfbe603e003e303f0

def z556 : W := mkw 0x27fdffdbe108b0ac 0x24ffbffb7c211615 0xefffffffe119e003 0xfdfffffffc233c00

def z557 : W := mkw 0x06efc1003ddff0ac 0x20ddf82007bbfe15 0x9fffe0001ffff1fd 0xf3fffc0003fffe3f

def z558 : W := mkw 0x06a940000c924000 0x00d5280001924800 0x9f31e0000f1fe005 0xd3e63c0001e3fc00

def z559 : W := mkw 0x1db21fa43bfd9fe7 0x43b643f4877fb3fc 0xdff01fe01ffd9fe6 0xfbfe03fc03ffb3fc

def z560 : W := mkw 0x27ffffdbfddff0ac 0x24fffffb7fbbfe15 0xfffffffffffff1ff 0xfffffffffffffe3f

def z561 : W := mkw 0x0002000416060b50 0x8000400082c0c16a 0x000000001e000e00 0x0000000003c001c0

def z562 : W := mkw 0x0209400004024000 0x0041280000804800 0x0001600000026000 0x00002c0000004c00

def z563 : W := mkw 0x000200001cd74000 0x00004000039ae800 0x000000001ee00000 0x0000000003dc0000

def z564 : W := mkw 0x0100192003201d06 0x00200324006403a0 0xdfc01fe01fe01f86 0xfbf803fc03fc03f0

def z565 : W := mkw 0x234df85bc0000000 0x0469bf0b78000000 0xe70ffc1fe0000003 0x7ce1ff83fc000000

def z566 : W := mkw 0x024fc00014474000 0x0049f8000288e800 0x983fe000011fe005 0xd307fc000023fc00

def z567 : W := mkw 0x0309181206020910 0x8061230240c04122 0xb7010c030e0611ff 0x56e0218061c0c23f

def z568 : W := mkw 0x27fdffdbc1081084 0x04ffbffb78210210 0xffffffffe1181187 0xfffffffffc230230

def z569 : W := mkw 0x04e6c00018d54000 0x009cd800031aa800 0x88fee00011fde005 0xb11fdc00023fbc00

def z570 : W := mkw 0x0010270161009024 0x000204e02c201204 0xa831ef03e1059067 0xd5063de07c20b20c

def z571 : W := mkw 0x0000000000000000 0x0000000000000000 0x10316000001a6000 0x42062c0000034c00

def z572 : W := mkw 0x0856876cb16d96e6 0x410ad0ed962db2dc 0xf8fe9ffcf1fd9fe7 0xff1fd3ff9e3fb3fc

def z573 : W := mkw 0x27fdfedbe000a028 0x24ffbfdb7c001405 0xe7ffffffe007e07b 0xfcfffffffc00fc0f

def z574 : W := mkw 0x2fefd9feb1659666 0x45fdfb3fd62cb2cc 0xefce93fcf1e59e67 0xbdf9d27f9e3cb3cc

def z575 : W := mkw 0x020b000414060240 0x004160008280c048 0xf70f101c1e061e67 0x7ee1e20383c0c3cc

def z576 : W := mkw 0x17efd8a01ef74d03 0x02fdfb1403dee9a0 0x47ce10e01ee00e00 0x28f9c21c03dc01c0

def z577 : W := mkw 0x27efd8da9cd74000 0x04fdfb1b539ae800 0x47ce10fc1ee00000 0x28f9c21f83dc0000

def z578 : W := mkw 0x00100700210890a4 0x000200e004211214 0xb8308f00e11d91e7 0xd70611e01c23b23c

def z579 : W := mkw 0x020b000014060000 0x004160000280c000 0x000f000000060001 0x0001e0000000c000

def z580 : W := mkw 0x03193f13670ab9bc 0xa06327e26ce15737 0xbf31ef03ef1ff1ff 0xd7e63de07de3fe3f

def z581 : W := mkw 0x0000012021209426 0x0000002404241284 0xe8c093e0f1e59e67 0xbd18127c1e3cb3cc

def z582 : W := mkw 0x0000001600000250 0x80000002c000004a 0x2000001f00000078 0x04000003e000000f

def z583 : W := mkw 0x17b91fb20bb81d87 0x02f723f6417703b0 0xffff1fff1ff81f87 0xffffe3ffe3ff03f0

def z584 : W := mkw 0x08448168a1619426 0x4108902d142c3284 0xa8c083e0e1e59067 0x9518107c1c3cb20c

def z585 : W := mkw 0x07efd8121ed74910 0x80fdfb0243dae922 0x9fffec031fffe19d 0xf3fffd8063fffc33

def z586 : W := mkw 0x000001002108b0ac 0x2000002004211615 0x080000000119e000 0x0100000000233c00

def z587 : W := mkw 0x0846804cb0458260 0x4108d0099608b04c 0xa8ce801cf1e58065 0xb519d0039e3cb00c

def z588 : W := mkw 0x15f4dfa00bf95d87 0x02be9bf4017f2bb0 0xdff0ffe01ff9ff86 0xfbfe1ffc03ff3ff0

def z589 : W := mkw 0x0fefd97ebff7df76 0xc1fdfb2fd7fefbee 0xffffffffffffffff 0xffffffffffffffff

def z590 : W := mkw 0x17ab18b61eb60f53 0x82f56316c3d6c1ea 0x47ce10fc1ee00e00 0x28f9c21f83dc01c0

def z591 : W := mkw 0x020b000416060b50 0x8041600082c0c16a 0x970f00001e061ffd 0x72e1e00003c0c3ff

def z592 : W := mkw 0x0010260140000000 0x000204c028000000 0xb031ef03e00611ff 0xd6063de07c00c23f

def z593 : W := mkw 0x034f981616470b50 0x8069f302c2c8e16a 0xffcf9c1f1fe79fff 0xfff9f383e3fcf3ff

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0010c0300000003 0x5400218060000000

def z595 : W := mkw 0x0000010021009024 0x0000002004201204 0x08008300e1018000 0x810010601c203000

def z596 : W := mkw 0x0000000002000900 0x0000000000400120 0x100000001e001f84 0x0200000003c003f0

def z597 : W := mkw 0x21103edbc0000000 0x042207db78000000 0xe031ffffe0000003 0xdc063ffffc000000

def z598 : W := mkw 0x27a9589200000000 0x04f52b1240000000 0x0700000000000000 0x00e0000000000000

def z599 : W := mkw 0x0eefc16cb1659666 0x41ddf82d962cb2cc 0xeffff3fcf1e59e67 0xfdfffe7f9e3cb3cc

def z600 : W := mkw 0x0000200140002008 0x2000040028000401 0x0001600300026018 0x00002c0060004c03

def z601 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x08ffe00001ffe001 0x811ffc00003ffc00

def z602 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xa8008f03e10591ff 0x950011e07c20b23f

def z603 : W := mkw 0x29103fffe1209666 0x452207fffc2412cc 0x60001fffe0001e62 0x0c0003fffc0003cc

def z604 : W := mkw 0x1df49fe8abf99da7 0x43be93fd157f33b4 0xdff09fe0fff99f86 0xfbfe13fc1fff33f0

def z605 : W := mkw 0x0056a701714db0ac 0x200ad4e02e29b615 0xb8ffef03f1fff1ff 0xf71ffde07e3ffe3f

def z606 : W := mkw 0x0eefc1243df7d666 0x41ddf82487befacc 0x9fffe0001ffffe65 0xf3fffc0003ffffcc

def z607 : W := mkw 0x0000000000082088 0x2000000000010411 0x10000000001a6198 0x0200000000034c33

def z608 : W := mkw 0x06ab00001c960000 0x00d560000392c000 0x9fff00001ffe0005 0xf3ffe00003ffc000

def z609 : W := mkw 0x0810276de128b6ee 0x610204edbc2516dd 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z610 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x570e101c1e061ffc 0x2ae1c20383c0c3ff

def z611 : W := mkw 0x06ffe6015cd74000 0x00dffcc02b9ae800 0xbfffef03ffffe007 0xf7fffde07ffffc00

def z612 : W := mkw 0x0209000000000000 0x0041200000000000 0x870f000000000001 0x70e1e00000000000

def z613 : W := mkw 0x025fe701754ff0ac 0x204bfce02ea9fe15 0xb83fef03e11ff1ff 0xd707fde07c23fe3f

def z614 : W := mkw 0x000020016000a028 0x200004002c001405 0x0000e000e001e000 0x00001c001c003c00

def z615 : W := mkw 0x0100180002000900 0x0020030000400120 0x470010001e000e00 0x28e0020003c001c0

def z616 : W := mkw 0x05a018000a900900 0x00b4030001520120 0xdff01c001ff81f86 0xfbfe038003ff03f0

def z617 : W := mkw 0x04a0000000000000 0x0094000000000000 0x87f0000000000000 0xf0fe000000000000

def z618 : W := mkw 0x225de75be108b0ac 0x244bbceb7c211615 0xb83fef1fe11ff1ff 0xd707fde3fc23fe3f

def z619 : W := mkw 0x17b95e800e9a4981 0x02f72bd001d34930 0x17316c000e1a6180 0x42e62d8001c34c30

def z620 : W := mkw 0x100001200bb81d87 0x02000024017703b0 0xd8c013e01ff81f86 0xbb18027c03ff03f0

def z621 : W := mkw 0x0010270141081084 0x000204e028210210 0xb831ef03e1181187 0xd7063de07c230230

def z622 : W := mkw 0x020b000014060000 0x004160000280c000 0x9f3fe0001f1fe005 0xf3e7fc0003e3fc00

def z623 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xd70f101c1e060e05 0x7ae1e20383c0c1c0

def z624 : W := mkw 0x06efc0041ed74b50 0x80ddf80083dae96a 0x9fffe0001ffffffd 0xf3fffc0003ffffff

def z625 : W := mkw 0x03193e1340000000 0x006327c268000000 0xe73fff1fe0000003 0xfce7ffe3fc000000

def z626 : W := mkw 0x100000000a980981 0x0200000001530130 0x100000000e180180 0x0200000001c30030

def z627 : W := mkw 0x19569fecb36d9fe7 0x432ad3fd966db3fc 0xe8ce9ffcf1e59fe7 0xbd19d3ff9e3cb3fc

def z628 : W := mkw 0x24f4e6c9c8d14000 0x049e9cd9391a2800 0x08f0e3e0e1f9e000 0x811e1c7c1c3f3c00

def z629 : W := mkw 0x27fffe935cd74000 0x04ffffd26b9ae800 0x9fffec031fffe005 0xf3fffd8063fffc00

def z630 : W := mkw 0x0000000400000240 0x0000000080000048 0x6000101c00001e62 0x0c000203800003cc

def z631 : W := mkw 0x24f4e6c9c0000000 0x049e9cd938000000 0xe0fef3fce0000003 0xbc1fde7f9c000000

def z632 : W := mkw 0x27fdfffbc1201406 0x04ffbfff78240280 0xeffffffff1e01e07 0xfdfffffffe3c03c0

def z633 : W := mkw 0x0309181200000000 0x0061230240000000 0x470e101c00000000 0x28e1c20380000000

def z634 : W := mkw 0x0b0b197eb7269f76 0xc161632fd6e4d3ee 0xf70f1ffffe061fff 0x7ee1e3ffffc0c3ff

def z635 : W := mkw 0x35b03ffbcbb81d87 0x06b607ff797703b0 0xfff01ffffff81f86 0xfffe03ffffff03f0

def z636 : W := mkw 0x14b007a009b81487 0x029600f401370290 0x98f00fe001f81186 0xd31e01fc003f0230

def z637 : W := mkw 0x21103e9340000000 0x042207d268000000 0x00000c0300000000 0x0000018060000000

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800800001058005 0x910010000020b000

def z639 : W := mkw 0x0002000416060b50 0x8000400082c0c16a 0xf00e101c1e061fff 0x3e01c20383c0c3ff

def z640 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x600f1c1f00061ffb 0x0c01e383e000c3ff

def z641 : W := mkw 0x0010070001081084 0x000200e000210210 0x9831ef00011ff187 0xd3063de00023fe30

def z642 : W := mkw 0x08468168b1659426 0x4108d02d162cb284 0x88ce83e0f1e58005 0xb119d07c1e3cb000

def z643 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x2831e303e11fe079 0x85063c607c23fc0f

def z644 : W := mkw 0x0b4f997eb1659666 0x4169f32fd62cb2cc 0xefcf9ffff1e59e67 0xfdf9f3fffe3cb3cc

def z645 : W := mkw 0x000020016000a028 0x200004002c001405 0xb831e003e11fe07d 0xd7063c007c23fc0f

def z646 : W := mkw 0x024fc00014474000 0x0049f8000288e800 0x88cfe00011e7e005 0xb119fc00023cfc00

def z647 : W := mkw 0x07ab58161e964b50 0x80f56b02c3d2c96a 0xf73f7c1f1e1e7fff 0x7ee7ef83e3c3cfff

def z648 : W := mkw 0x0800006c80200642 0x4100000d900400c8 0x400010fc00000e00 0x0800021f800001c0

def z649 : W := mkw 0x031b3e1756060b50 0x806367c2eac0c16a 0xf73fff1ffe061fff 0xfee7ffe3ffc0c3ff

def z650 : W := mkw 0x0846a16df165b66e 0x6108d42dbe2cb6cd 0xe8cff3fff1e7fe7f 0xbd19fe7ffe3cffcf

def z651 : W := mkw 0x04b027016998b0ac 0x209604e02d331615 0xbff1ef03fffff1ff 0xf7fe3de07ffffe3f

def z652 : W := mkw 0x0df69fecb1659666 0x41bed3fd962cb2cc 0xeffe9ffcf1e59e67 0xfdffd3ff9e3cb3cc

def z653 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0xc8c013e011e59e66 0xb918027c023cb3cc

def z654 : W := mkw 0x0846a04df045a268 0x6108d409be08b44d 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z655 : W := mkw 0x0ce4c168a9f1d426 0x419c982d153e3a84 0x08f0e3e0e1f9e000 0x811e1c7c1c3f3c00

def z656 : W := mkw 0x07efd8161ed74b50 0x80fdfb02c3dae96a 0xf7cf1c1f1ee61fff 0x7ef9e383e3dcc3ff

def z657 : W := mkw 0x08448048a0418020 0x4108900914083004 0x00008000e0018000 0x000010001c003000

def z658 : W := mkw 0x0000000402000b50 0x800000008040016a 0x0000000000001ff8 0x00000000000003ff

def z659 : W := mkw 0x020b00001cd74000 0x00416000039ae800 0x9f0f00001fffe005 0x73e1e00003fffc00

def z660 : W := mkw 0x0810276de128b6ee 0x610204edbc2516dd 0xf831ffffe11fffff 0xdf063ffffc23ffff

def z661 : W := mkw 0x06efc00010450000 0x00ddf8000208a000 0x8fffe00011e58005 0xf1fffc00023cb000

def z662 : W := mkw 0x000001002108b0ac 0x2000002004211615 0x00000000000011f8 0x000000000000023f

def z663 : W := mkw 0x24f4e7c9e108b0ac 0x249e9cf93c211615 0xb8f1efe3e11ff1ff 0xd71e3dfc7c23fe3f

def z664 : W := mkw 0x0a4f816cb5679666 0x4149f02d96acf2cc 0xffcf93fcffe79e67 0xfff9f27f9ffcf3cc

def z665 : W := mkw 0x07b91e9200000000 0x00f723d240000000 0xe7ff1fff00000003 0xfcffe3ffe0000000

def z666 : W := mkw 0x05b01fa001201406 0x00b603f400240280 0xcff01fe011e01e06 0xf9fe03fc023c03c0

def z667 : W := mkw 0x020b001616060b50 0x80416002c2c0c16a 0x300f001f1e061ffd 0x0601e003e3c0c3ff

def z668 : W := mkw 0x0b4f987e96670f52 0xc169f30fd2cce1ea 0x47ce10fc1ee00e00 0x28f9c21f83dc01c0

def z669 : W := mkw 0x2ffffedff0458260 0x45ffffdbfe08b04c 0xe7ffffffe0058063 0xfcfffffffc00b00c

def z670 : W := mkw 0x34f4e7e9c9b81487 0x069e9cfd39370290 0x08f0e3e0e1f80000 0x811e1c7c1c3f0000

def z671 : W := mkw 0x000200001cd74000 0x00004000039ae800 0x9831e0001fffe005 0xd3063c0003fffc00

def z672 : W := mkw 0x27fdfedfc2000b50 0x84ffbfdbf840016a 0xe7ffffffe0001ffb 0xfcfffffffc0003ff

def z673 : W := mkw 0x0102180416060b50 0x8020430082c0c16a 0xd7001c001e061ffe 0x7ae0038003c0c3ff

def z674 : W := mkw 0x020b000014060000 0x004160000280c000 0x070e00001e000000 0x20e1c00003c00000

def z675 : W := mkw 0x000020016000a028 0x200004002c001405 0x20000003e0000078 0x040000007c00000f

def z676 : W := mkw 0x0309181602000b50 0x80612302c040016a 0xe70f1c1f00001ffb 0x7ce1e383e00003ff

def z677 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x30316f03e01a71fa 0x46062de07c034e3f

def z678 : W := mkw 0x0856a76df1659666 0x410ad4edbe2cb2cc 0xe8fffffff1e59e67 0xfd1ffffffe3cb3cc

def z679 : W := mkw 0x0ce6c16cb9f5d666 0x419cd82d973ebacc 0xe8fef3fcf1fdfe67 0xbd1fde7f9e3fbfcc

def z680 : W := mkw 0x15b01e800a980981 0x02b603d001530130 0xd7301c001e181f86 0x7ae6038003c303f0

def z681 : W := mkw 0x11101fb603281fd7 0x822203f6c06503fa 0x60001fff00001ffa 0x0c0003ffe00003ff

def z682 : W := mkw 0x030b181614060250 0x80616302c280c04a 0xe70f1c1f0006007b 0x7ce1e383e000c00f

def z683 : W := mkw 0x024fe0017447e028 0x2049fc002e88fc05 0x200fe003e007e079 0x0401fc007c00fc0f

def z684 : W := mkw 0x21103edfc2000b50 0x842207dbf840016a 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z685 : W := mkw 0x17b95fa00fba5d87 0x02f72bf401f74bb0 0xdff17fe01ffa7f86 0xfbfe2ffc03ff4ff0

def z686 : W := mkw 0x11101fa00bb81d87 0x022203f4017703b0 0x58001fe01ff81f86 0x0b0003fc03ff03f0

def z687 : W := mkw 0x0800016ca1209666 0x4100002d942412cc 0xe80093fce1059e67 0x9d00127f9c20b3cc

def z688 : W := mkw 0x2cf6e7edf1659666 0x459edcfdbe2cb2cc 0xe8fef3fcf1e59e67 0xbd1fde7f9e3cb3cc

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x88c0000011e00004 0xb1180000023c0000

def z690 : W := mkw 0x27edd8da80000000 0x04fdbb1b50000000 0xe7cf1cff00000003 0x7cf9e39fe0000000

def z691 : W := mkw 0x05b03f816108b0ac 0x20b607f02c211615 0xfff1ffe3e11ff1ff 0xfffe3ffc7c23fe3f

def z692 : W := mkw 0x0100181602000b50 0x80200302c040016a 0x4000101c00000e00 0x08000203800001c0

def z693 : W := mkw 0x100201201fff5d87 0x0200402403ffebb0 0x180000001fffff84 0x0300000003fffff0

def z694 : W := mkw 0x024dc00000000000 0x0049b80000000000 0x000fe00000000001 0x0001fc0000000000

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x9001000000060005 0x520020000000c000

def z696 : W := mkw 0x15b21fa41fbe1fd7 0x82b643f483f7c3fa 0xdff01fe01ffe1ffe 0xfbfe03fc03ffc3ff

def z697 : W := mkw 0x0010260140000000 0x000204c028000000 0x0030e300e0000000 0x80061c601c000000

def z698 : W := mkw 0x27b97e9340000000 0x04f72fd268000000 0xa731ef03e0000003 0xd4e63de07c000000

def z699 : W := mkw 0x000000002000a028 0x2000000004001405 0x000000000007e078 0x000000000000fc0f

def z700 : W := mkw 0x0010070001081084 0x000200e000210210 0xb8310f03011e11ff 0xd70621e06023c23f

def z701 : W := mkw 0x06b967016d9af0ac 0x20d72ce02db35e15 0xbf31ef03ef1ff1ff 0xd7e63de07de3fe3f

def z702 : W := mkw 0x03193e13460a2998 0xa06327c268c14533 0x17316c030e1a6198 0x42e62d8061c34c33

def z703 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x8fce80001fe58005 0xb1f9d00003fcb000

def z704 : W := mkw 0x14b027a169b8b4af 0x229604f42d371695 0xb8f1efe3e1fff1ff 0xd71e3dfc7c3ffe3f

def z705 : W := mkw 0x001227017ddff0ac 0x200244e02fbbfe15 0xb831ef03fffff1ff 0xd7063de07ffffe3f

def z706 : W := mkw 0x130b19361fbe1fd7 0x82616326c3f7c3fa 0xff0f1c1f1ffe1fff 0x7fe1e383e3ffc3ff

def z707 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0xc7c01ce01ee00e02 0x78f8039c03dc01c0

def z708 : W := mkw 0x15a018a00ab80d83 0x02b40314015701b0 0x57c010e01ef80f80 0x2af8021c03df01f0

def z709 : W := mkw 0x0846806c90650642 0x4108d00d920ca0c8 0xe0ce93fcf0e41e67 0xbc19d27f9e1c83cc

def z710 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0x0000000010e01e60 0x00000000021c03cc

def z711 : W := mkw 0x27b97e934e924910 0x84f72fd269d24922 0x17316c030e1a6198 0x42e62d8061c34c33

def z712 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0x1800000011fffe64 0x03000000023fffcc

def z713 : W := mkw 0x031b3f17770ebbfc 0xa06367e2eee1d77f 0x4f3ef31cff19ee00 0xa9e7de639fe33dc0

def z714 : W := mkw 0x030b181616470b50 0x80616302c2c8e16a 0xff0f1c1f1fe79fff 0x7fe1e383e3fcf3ff

def z715 : W := mkw 0x235dbedbc0000000 0x046bb7db78000000 0xe7cf9fffe0000003 0xfcf9f3fffc000000

def z716 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x770f1c1f0e061ffb 0x4ee1e383e1c0c3ff

def z717 : W := mkw 0x224de05bc0000000 0x0449bc0b78000000 0x20cfe3ffe0000001 0x8419fc7ffc000000

def z718 : W := mkw 0x26fde6dbc0000000 0x04dfbcdb78000000 0xa0ffefffe0000003 0xd41ffdfffc000000

def z719 : W := mkw 0x0044804880000000 0x0008900910000000 0xe0ce93fcf0001e07 0xbc19d27f9e0003c0

def z720 : W := mkw 0x235dfedbc0000000 0x046bbfdb78000000 0x600e1fffe0000002 0x0c01c3fffc000000

def z721 : W := mkw 0x27fdfedbc2000900 0x04ffbfdb78400120 0xe7fffffffe000e03 0xfcffffffffc001c0

def z722 : W := mkw 0x0eefc04c9cd74240 0x41ddf809939ae848 0x9fffe01c1fffe005 0xf3fffc0383fffc00

def z723 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xffce93fcffe59e67 0xfff9d27f9ffcb3cc

def z724 : W := mkw 0x06edc0000cd34000 0x00ddb800019a6800 0x0ff0e0000ff9e000 0x81fe1c0001ff3c00

def z725 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xe70e1c1f1e041fff 0x3ce1c383e3c083ff

def z726 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x570f1c1f1e061ffc 0x6ae1e383e3c0c3ff

def z727 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xdff013e01ff80e04 0xfbfe027c03ff01c0

def z728 : W := mkw 0x16bb07b61dbe16d7 0x82d760f6c3b7c2da 0x28ff03ff01fe0079 0x851fe07fe03fc00f

def z729 : W := mkw 0x001027216128b4ae 0x200204e42c251695 0xf831ffe3e11fffff 0xdf063ffc7c23ffff

def z730 : W := mkw 0x34f4e7e9e9b8b4af 0x269e9cfd3d371695 0x08f0e3e0e1f9e000 0x811e1c7c1c3f3c00

def z731 : W := mkw 0x2154bedbc0000000 0x042a97db78000000 0x600e9fffe0000003 0x0c01d3fffc000000

def z732 : W := mkw 0x27fdfedbc8d14000 0x04ffbfdb791a2800 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z733 : W := mkw 0x15b03fa14bb81d87 0x02b607f4297703b0 0xdff0ffe0fff81f86 0xfbfe1ffc1fff03f0

def z734 : W := mkw 0x1df69eccbadd8be1 0x43bed3d9975bb17c 0x373e8c1cee1d81e1 0x46e7d1839dc3b03c

def z735 : W := mkw 0x0054a649c0000000 0x000a94c938000000 0xe0ce9fffe0000003 0xbc19d3fffc000000

def z736 : W := mkw 0x15b01fb20bb81d87 0x02b603f6417703b0 0xfff01fff1ff81f86 0xfffe03ffe3ff03f0

def z737 : W := mkw 0x06efc0121cd74010 0x80ddf802439ae802 0x9fffe0031fffe01d 0xf3fffc0063fffc03

def z738 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0xbfffe0031fffe07d 0xf7fffc0063fffc0f

def z739 : W := mkw 0x0044804880000000 0x0008900910000000 0xe0ce93fce0041067 0xbc19d27f9c00820c

def z740 : W := mkw 0x15a019a00bb81d87 0x02b40334017703b0 0x47c010e01ee01f80 0x28f8021c03dc03f0

def z741 : W := mkw 0x225de65bc0000000 0x044bbccb78000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z742 : W := mkw 0x0846816cb16db6ee 0x6108d02d962db6dd 0xf8cf9ffff1ffffff 0xff19f3fffe3fffff

def z743 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xcff013e01ff81e06 0xb9fe027c03ff03c0

def z744 : W := mkw 0x06ab40001cd74000 0x00d56800039ae800 0x9ff160001fffe004 0xf3fe2c0003fffc00

def z745 : W := mkw 0x2a4fe05ff4478270 0xc549fc0bfe88f04e 0x200fe01fe0078079 0x0401fc03fc00f00f

def z746 : W := mkw 0x135fdfa0176f5d87 0x026bfbf402edebb0 0x400fffe00007ff83 0x0801fffc0000fff0

def z747 : W := mkw 0x01549ec880000000 0x002a93d910000000 0xe0ce9ffce0000003 0xbc19d3ff9c000000

def z748 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xdff01fe0fff81f86 0xfbfe03fc1fff03f0

def z749 : W := mkw 0x15b01ea00ab80d83 0x02b603d4015701b0 0xd7f01fe01ef80f82 0xfafe03fc03df01f0

def z750 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xe8cf9ffff1e59e67 0xfd19f3fffe3cb3cc

def z751 : W := mkw 0x2fbb7fb771659666 0x45f76ff6ee2cb2cc 0x0f316c0311e59e64 0x41e62d80623cb3cc

def z752 : W := mkw 0x0802012439f5d666 0x41004024873ebacc 0x0800000011fdfe64 0x01000000023fbfcc

def z753 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x5ff01fe01ff80f80 0xebfe03fc03ff01f0

def z754 : W := mkw 0x06efc0489cd74000 0x00ddf809139ae800 0xdffff0fc1fffe005 0xfbfffe1f83fffc00

def z755 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xdff0ffe01ff9ff86 0xfbfe1ffc03ff3ff0

def z756 : W := mkw 0x04e4804880000000 0x009c900910000000 0xe7fe93fce0000003 0xfcffd27f9c000000

def z757 : W := mkw 0x0802012433659f66 0x41004024866cb3ec 0x180000001fe59fe4 0x0300000003fcb3fc

def z758 : W := mkw 0x26fde6dbc0000000 0x04dfbcdb78000000 0xa7ffe3ffe0000001 0xf4fffc7ffc000000

def z759 : W := mkw 0x24f6e6cdd6060b50 0x849edcd9bac0c16a 0x10f0e3e0fe061ffc 0x821e1c7c1fc0c3ff

def z760 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0x9831e00011fffe65 0xd3063c00023fffcc

def z761 : W := mkw 0x0044804880410000 0x0008900910082000 0xe8ce93fce1e18003 0xbd19d27f9c3c3000

def z762 : W := mkw 0x0054a649c0000000 0x000a94c938000000 0xe0fef3fce0000003 0xbc1fde7f9c000000

def z763 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xff0f1c1f1f1fffff 0x7fe1e383e3e3ffff

def z764 : W := mkw 0x0102180412040b40 0x0020430082408168 0xf70f1c1f1e061fff 0x7ee1e383e3c0c3ff

def z765 : W := mkw 0x15b03fa14bb83d8f 0x22b607f4297707b1 0xfff1ffe3fffa7f9f 0xfffe3ffc7fff4ff3

def z766 : W := mkw 0x15b01fa02bb8bdaf 0x22b603f4057717b5 0xdff01fe01ff9ff86 0xfbfe03fc03ff3ff0

def z767 : W := mkw 0x15b03ea14ab00d03 0x02b607d4295601a0 0xe7f1ffe3fee00e03 0xfcfe3ffc7fdc01c0

def z768 : W := mkw 0x07fd9eda80000000 0x00ffb3db50000000 0xe7ff9fffe0000003 0xfcfff3fffc000000

def z769 : W := mkw 0x06efc0161cd74250 0x80ddf802c39ae84a 0x9fffe01c1fffe005 0xf3fffc0383fffc00

def z770 : W := mkw 0x101027a16128b4af 0x220204f42c251695 0xb831efe3e11ff1ff 0xd7063dfc7c23fe3f

def z771 : W := mkw 0x21103edbc0000000 0x042207db78000000 0xe00e1fffe0000003 0x3c01c3fffc000000

def z772 : W := mkw 0x00448168a1209426 0x0008902d14241284 0xe8ce93fcf1e59e67 0xbd19d27f9e3cb3cc

def z773 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xff3f1c1f1f1e1fff 0xffe7e383e3e3c3ff

def z774 : W := mkw 0x27fdfedbc6020910 0x84ffbfdb78c04122 0xf7ffffffee0611ff 0xfefffffffdc0c23f

def z775 : W := mkw 0x0ea9416cadb2d666 0x41d5282d95b65acc 0x773173fcee1a7e62 0x4ee62e7f9dc34fcc

def z776 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x68ce93fcf1e58e61 0xad19d27f9e3cb1cc

def z777 : W := mkw 0x0309181202000900 0x0061230240400120 0xf70f1c1f1e061fff 0x7ee1e383e3c0c3ff

def z778 : W := mkw 0x06efc0161cd74250 0x80ddf802c39ae84a 0xbfffec1f1ffff1ff 0xf7fffd83e3fffe3f

def z779 : W := mkw 0x11103fa16328bdaf 0x222207f42c6517b5 0x40001fe0e0001f82 0x080003fc1c0003f0

def z780 : W := mkw 0x21123edbdcd74000 0x042247db7b9ae800 0x78001fffffffe006 0x0f0003fffffffc00

def z781 : W := mkw 0x15b01fa02bb8bdaf 0x22b603f4057717b5 0xdff1ffe01fffffff 0xfbfe3ffc03ffffff

def z782 : W := mkw 0x0802012437679f76 0xc100402486ecf3ee 0x080000001fe59e64 0x0100000003fcb3cc

def z783 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xffffffffe11ff1ff 0xfffffffffc23fe3f

def z784 : W := mkw 0x0b4d997aa7639d36 0xc169b32f54ec73a6 0x1fc18fe3efe38198 0xc3f831fc7dfc7033

def z785 : W := mkw 0x37b97e934e9a0991 0x86f72fd269d34132 0x17316c030e1a0198 0x42e62d8061c34033

def z786 : W := mkw 0x04e4c00008d14000 0x009c9800011a2800 0x0ff0e0001ff9e000 0xa1fe1c0003ff3c00

def z787 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xffcf1c1f1fe61fff 0xfff9e383e3fcc3ff

def z788 : W := mkw 0x0cf4e769e9f9f4ae 0x619e9ced3d3f3e95 0x08f0e3e0e1f9e000 0x811e1c7c1c3f3c00

def z789 : W := mkw 0x020b000414060240 0x004160008280c048 0xf70f1c1f1e061fff 0x7ee1e383e3c0c3ff

def z790 : W := mkw 0x27edd9daa108b0ac 0x24fdbb3b54211615 0x5fce10fc011ff1fc 0x2bf9c21f8023fe3f

def z791 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x1f3fe0001fffe005 0x43e7fc0003fffc00

def z792 : W := mkw 0x27b97edbc0000000 0x04f72fdb78000000 0xe73f7fffe0000003 0x7ce7effffc000000

def z793 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x1ffee0001fffe004 0xa3ffdc0003fffc00

def z794 : W := mkw 0x15b01fb20bb81d97 0x82b603f6417703b2 0xdff01fe31ff81f9e 0xfbfe03fc63ff03f3

def z795 : W := mkw 0x0000004880000000 0x0000000910000000 0xe00e13fce0000003 0x3c01c27f9c000000

def z796 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x48ce93fcf1e59e64 0xa919d27f9e3cb3cc

def z797 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xf73f7c1f1e1e7fff 0x7ee7ef83e3c3cfff

def z798 : W := mkw 0x05b01e800a900900 0x00b603d001520120 0xdff01fe01ff81f86 0xfbfe03fc03ff03f0

def z799 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x67fff3ffe0000001 0xacfffe7ffc000000

def z800 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x670f1c1f1e061ffb 0x2ce1e383e3c0c3ff

def z801 : W := mkw 0x15a019a02bb09d27 0x02b40334057613a4 0xefc093e0ffe59e67 0xbdf8127c1ffcb3cc

def z802 : W := mkw 0x37b97e934a900901 0x06f72fd269520120 0x07316c030e000000 0x40e62d8061c00000

def z803 : W := mkw 0x0846816cb567d666 0x4108d02d96acfacc 0xe8ce93fcf1e7fe67 0xbd19d27f9e3cffcc

def z804 : W := mkw 0x0a4f805e94470250 0xc149f00bd288e04a 0x200f001f00060079 0x0401e003e000c00f

def z805 : W := mkw 0x0802012435679666 0x4100402486acf2cc 0x180000001fe79e64 0x0300000003fcf3cc

def z806 : W := mkw 0x06efc0489cd74000 0x00ddf809139ae800 0x9fffe3e0ffffe005 0xf3fffc7c1ffffc00

def z807 : W := mkw 0x324de17bcbb81d87 0x0649bc2f797703b0 0x380fe01ffff81f85 0x0701fc03ffff03f0

def z808 : W := mkw 0x15b01ea00ab00d03 0x02b603d4015601a0 0xd7f01fe01ee01f86 0xfafe03fc03dc03f0

def z809 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x370f0c1f1e061ffd 0x46e1e183e3c0c3ff

def z810 : W := mkw 0x15a019a02bb8bdaf 0x22b40334057717b5 0x5fc010e01ffffffc 0x2bf8021c03ffffff

def z811 : W := mkw 0x15b03fa14bb81d87 0x02b607f4297703b0 0xfff1ffe3ffffff87 0xfffe3ffc7ffffff0

def z812 : W := mkw 0x0846816cb16db6ee 0x6108d02d962db6dd 0xe8ce93fcf1e59fff 0xbd19d27f9e3cb3ff

def z813 : W := mkw 0x0902192433659f66 0x41204324866cb3ec 0xdf001c001fe59fe6 0x7be0038003fcb3fc

def z814 : W := mkw 0x0a4f805eb4478270 0xc149f00bd688f04e 0x200e801ce0058061 0x0401d0039c00b00c

def z815 : W := mkw 0x0ce6c12439f5d666 0x419cd824873ebacc 0x08f0e00011fdfe64 0x811e1c00023fbfcc

def z816 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xf7ffffffe002019b 0xfefffffffc004033

def z817 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x8fffe0001ff9e001 0xf1fffc0003ff3c00

def z818 : W := mkw 0x08020124316d96e6 0x41004024862db2dc 0x1800000011fd9fe4 0x03000000023fb3fc

def z819 : W := mkw 0x024f800014470000 0x0049f0000288e000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z820 : W := mkw 0x27fdfedbc8900000 0x04ffbfdb79120000 0xf7ffffffee180003 0xfefffffffdc30000

def z821 : W := mkw 0x27fdfedbc8d14000 0x04ffbfdb791a2800 0xffffffffe1ffe007 0xfffffffffc3ffc00

def z822 : W := mkw 0x15b03fa14bb81d87 0x02b607f4297703b0 0xdff17fe31ff81f86 0xfbfe2ffc63ff03f0

def z823 : W := mkw 0x15a019a00bb81d87 0x02b40334017703b0 0x4fc010e01ff80e00 0x29f8021c03ff01c0

def z824 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x3031ef03e01ff1fb 0x46063de07c03fe3f

def z825 : W := mkw 0x0046816891651406 0x0008d02d122ca280 0xe8ce93fcf1e59e07 0xbd19d27f9e3cb3c0

def z826 : W := mkw 0x06ffe7017ddff0ac 0x20dffce02fbbfe15 0x27ce0f03fee011fa 0x24f9c1e07fdc023f

def z827 : W := mkw 0x27fdfedbc2000900 0x04ffbfdb78400120 0xf7fffffffe061fff 0xfeffffffffc0c3ff

def z828 : W := mkw 0x27fdfedbc8d14000 0x04ffbfdb791a2800 0xfffffffffff9e007 0xffffffffffff3c00

def z829 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xdff0ffe0fffffffe 0xfbfe1ffc1fffffff

def z830 : W := mkw 0x37fdfedbce9a0991 0x86ffbfdb79d34132 0xf7ffffffee1a019b 0xfefffffffdc34033

def z831 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xe8cf93fff1e79e7f 0xbd19f27ffe3cf3cf

def z832 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xf8ce9ffcf1e59fe7 0xff19d3ff9e3cb3fc

def z833 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x47ce13fce0000000 0x28f9c27f9c000000

def z834 : W := mkw 0x07edd85a80000000 0x00fdbb0b50000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z835 : W := mkw 0x0a4fc04c94474240 0x4149f8099288e848 0x000e001c00000000 0x0001c00380000000

def z836 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0x4ff010e01ff80e00 0xa9fe021c03ff01c0

def z837 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x3831ef03e11fe1f9 0xc7063de07c23fc3f

def z838 : W := mkw 0x2044e049c0000000 0x04089c0938000000 0xe0cef3fce0000003 0xbc19de7f9c000000

def z839 : W := mkw 0x05f4bec9c0000000 0x00be97d938000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z840 : W := mkw 0x0856a66dd06d26ca 0x610ad4cdba0da4d9 0x50ff7cff10fa6f98 0x6a1fef9fe21f4df3

def z841 : W := mkw 0x26fde6c9c0000000 0x04dfbcd938000000 0xe7fff3fce0000003 0xfcfffe7f9c000000

def z842 : W := mkw 0x15b01ea00ab80d83 0x02b603d4015701b0 0x47f010e01ef80e00 0x28fe021c03df01c0

def z843 : W := mkw 0x18020124336d9fe7 0x43004024866db3fc 0x0800000011e59fe4 0x01000000023cb3fc

def z844 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0xc7c013e01ee00e02 0xb8f8027c03dc01c0

def z845 : W := mkw 0x01101f2003281d86 0x002203e4006503b0 0xdff01fe01ff81f86 0xfbfe03fc03ff03f0

def z846 : W := mkw 0x08122725716db6ee 0x610244e4ae2db6dd 0x18316c0311fffffc 0x43062d80623fffff

def z847 : W := mkw 0x05b01fa003201d06 0x00b603f4006403a0 0xdff01fe01fe01f86 0xfbfe03fc03fc03f0

def z848 : W := mkw 0x27edd8da80000000 0x04fdbb1b50000000 0xe7cf9fffe0000003 0xfcf9f3fffc000000

def z849 : W := mkw 0x27fdfedbc6020910 0x84ffbfdb78c04122 0xe7ffffffee000003 0xfcfffffffdc00000

def z850 : W := mkw 0x27fdfedbc60a2998 0xa4ffbfdb78c14533 0xf7ffffffee1a619b 0xfefffffffdc34c33

def z851 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xfff1ffe3fff81fff 0xfffe3ffc7fff03ff

def z852 : W := mkw 0x0044804880000000 0x0008900910000000 0x20ce83fce0000001 0x8419d07f9c000000

def z853 : W := mkw 0x001026016008a0a8 0x200204c02c011415 0xb031ef03e01fe1fb 0xd6063de07c03fc3f

def z854 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x67cfffffe0000003 0x2cf9fffffc000000

def z855 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xefffffffe119e003 0xfdfffffffc233c00

def z856 : W := mkw 0x0309185a80000000 0x0061230b50000000 0xe70f1fffe0000003 0x7ce1e3fffc000000

def z857 : W := mkw 0x04a0000008900000 0x0094000001120000 0x9ff0e0001ff9e004 0xf3fe1c0003ff3c00

def z858 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x60ffffffe0000003 0x8c1ffffffc000000

def z859 : W := mkw 0x0044804880000000 0x0008900910000000 0xe0cf9fffe0000003 0xfc19f3fffc000000

def z860 : W := mkw 0x04a0002008b00402 0x0094000401160080 0xdff010e01ff80e04 0xfbfe021c03ff01c0

def z861 : W := mkw 0x27fdfedbcc924000 0x04ffbfdb79924800 0xfffffffffffa6007 0xffffffffffff4c00

def z862 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0x0800000011e18e00 0x01000000023c31c0

def z863 : W := mkw 0x35b07fa14bb81d87 0x06b60ff4297703b0 0xdff07fe01ff81f86 0xfbfe0ffc03ff03f0

def z864 : W := mkw 0x05e498c880000000 0x00bc931910000000 0xe7ce93fce0000003 0xbcf9d27f9c000000

def z865 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0x8800800011e59e65 0x91001000023cb3cc

def z866 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0xbfffe300ffffe007 0xf7fffc601ffffc00

def z867 : W := mkw 0x06efc0489cd74000 0x00ddf809139ae800 0xbfffe01cffffe005 0xf7fffc039ffffc00

def z868 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xf70e1c1f1e001ffe 0x7ee1c383e3c003ff

def z869 : W := mkw 0x27fdfedbc0082088 0x24ffbfdb78010411 0xe7ffffffe000019b 0xfcfffffffc000033

def z870 : W := mkw 0x080201243165b66e 0x61004024862cb6cd 0x0800000011e7fe7c 0x01000000023cffcf

def z871 : W := mkw 0x26efc0c89cd74000 0x04ddf819139ae800 0x9fffe0e01fffe005 0xf3fffc1c03fffc00

def z872 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0xdffff0001ffffe07 0xfbfffe0003ffffc0

def z873 : W := mkw 0x06efc0041cd74240 0x00ddf800839ae848 0x9fffe0001ffffe65 0xf3fffc0003ffffcc

def z874 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xf8f1ffe3e11ff1ff 0xff1e3ffc7c23fe3f

def z875 : W := mkw 0x15a019a00bb01d07 0x02b40334017603a0 0xdfc01fe01fe01f86 0xfbf803fc03fc03f0

def z876 : W := mkw 0x15a038a16ab0ad2b 0x22b407142d5615a5 0x67c1f0e3fee7ee79 0x2cf83e1c7fdcfdcf

def z877 : W := mkw 0x0309181606020b50 0x80612302c0c0416a 0xf70f1c1f0e021ffb 0x7ee1e383e1c043ff

def z878 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xd7c01fe01ee01f86 0x7af803fc03dc03f0

def z879 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xe7ffffffe006007b 0xfcfffffffc00c00f

def z880 : W := mkw 0x15b03fa14bb83d8f 0x22b607f4297707b1 0xdff07fe01ff87f86 0xfbfe0ffc03ff0ff0

def z881 : W := mkw 0x0fefd87e9ef74f52 0xc1fdfb0fd3dee9ea 0x47ce10fc1ee00e00 0x28f9c21f83dc01c0

def z882 : W := mkw 0x224de05bc0000000 0x0449bc0b78000000 0x600ff3ffe0000003 0x0c01fe7ffc000000

def z883 : W := mkw 0x001027216128b4ae 0x200204e42c251695 0xb8f1efe3e1fff1ff 0xd71e3dfc7c3ffe3f

def z884 : W := mkw 0x25f4fedbc0000000 0x04be9fdb78000000 0xe0feffffe0000003 0xbc1fdffffc000000

def z885 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xe8cff3fcf1e7fe67 0xbd19fe7f9e3cffcc

def z886 : W := mkw 0x27fdfedbc8900000 0x04ffbfdb79120000 0xe7fffffffee00003 0xfcffffffffdc0000

def z887 : W := mkw 0x31103ffbe328bdaf 0x262207ff7c6517b5 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z888 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0x47c01ce01ee01f82 0x28f8039c03dc03f0

def z889 : W := mkw 0x001026016008a0a8 0x200204c02c011415 0xb031ec03e01ff1ff 0x56063d807c03fe3f

def z890 : W := mkw 0x15f49ec88a980981 0x02be93d911530130 0xf7fe9ffcee180183 0xfeffd3ff9dc30030

def z891 : W := mkw 0x27fdfedbc0002008 0x24ffbfdb78000401 0xe7ffffffe002601b 0xfcfffffffc004c03

def z892 : W := mkw 0x214498da80000000 0x0428931b50000000 0xe0ce93fce0000003 0xbc19d27f9c000000

def z893 : W := mkw 0x06ab40001cd74000 0x00d56800039ae800 0x9f3f60001fffe005 0x73e7ec0003fffc00

def z894 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0xf7c11ce31ee61fff 0x7ef8239c63dcc3ff

def z895 : W := mkw 0x27fdfedbc0410000 0x04ffbfdb78082000 0xefffffffe1e18003 0xfdfffffffc3c3000

def z896 : W := mkw 0x06a940000cd34000 0x00d52800019a6800 0x1f3160000ffbe000 0x43e62c0001ff7c00

def z897 : W := mkw 0x224dc05a80000000 0x0449b80b50000000 0xe0ce93fce0000003 0xbc19d27f9c000000

def z898 : W := mkw 0x06ab40001cd74000 0x00d56800039ae800 0x9f31e0001fffe005 0xd3e63c0003fffc00

def z899 : W := mkw 0x080201243dfff6ee 0x6100402487bffedd 0x180000001ffffffc 0x0300000003ffffff

def z900 : W := mkw 0x2154bedbc0000000 0x042a97db78000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z901 : W := mkw 0x05e4d8160ad14b50 0x80bc9b02c15a296a 0x68f0fc1f01f9fffa 0x8d1e1f83e03f3fff

def z902 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xe7fe1fffe0000002 0xfcffc3fffc000000

def z903 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xdff17fe31ffffffe 0xfbfe2ffc63ffffff

def z904 : W := mkw 0x080201243df7d666 0x4100402487befacc 0x080000001fe59e64 0x0100000003fcb3cc

def z905 : W := mkw 0x14b007a009b81487 0x029600f401370290 0xdff013e01ff81e06 0xfbfe027c03ff03c0

def z906 : W := mkw 0x15b01fa02bb89da7 0x02b603f4057713b4 0xfff19fe3ffff9fff 0xfffe33fc7ffff3ff

def z907 : W := mkw 0x06efc0041cd74240 0x00ddf800839ae848 0xbfffe01c1fffe065 0xf7fffc0383fffc0c

def z908 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0xfffff01c1fffe007 0xfffffe0383fffc00

def z909 : W := mkw 0x0a5fe74df54ff2ec 0x614bfce9bea9fe5d 0xb83fef1fe11ff1ff 0xd707fde3fc23fe3f

def z910 : W := mkw 0x37fdfedbca980981 0x06ffbfdb79530130 0xfffffffffff80187 0xffffffffffff0030

def z911 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xf8ce93fcf1e79fff 0xbf19d27f9e3cf3ff

def z912 : W := mkw 0x06edc00008900000 0x00ddb80001120000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z913 : W := mkw 0x27fdfedbc4024000 0x04ffbfdb78804800 0xe7ffffffe0026003 0xfcfffffffc004c00

def z914 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xfff0ffe3fff9fffe 0xfffe1ffc7fff3fff

def z915 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xf70f9f1ffe061fff 0xfee1f3e3ffc0c3ff

def z916 : W := mkw 0x23193edbc0000000 0x046327db78000000 0x670e1fffe0000002 0x2ce1c3fffc000000

def z917 : W := mkw 0x27fdfedbc8900000 0x04ffbfdb79120000 0xffffffffffffe007 0xfffffffffffffc00

def z918 : W := mkw 0x180201243bf59f67 0x43004024877eb3ec 0x080000001fe59e64 0x0100000003fcb3cc

def z919 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0x1800000011e79ffc 0x03000000023cf3ff

def z920 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xbf31ef03ff1ff1ff 0xf7e63de07fe3fe3f

def z921 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xf7fffffffe000007 0xfeffffffffc00000

def z922 : W := mkw 0x04b0072009b81486 0x009600e401370290 0xdff01fe01ff81f86 0xfbfe03fc03ff03f0

def z923 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xc7fefffce0000002 0xf8ffdfff9c000000

def z924 : W := mkw 0x15b03fa14bb83d8f 0x22b607f4297707b1 0xdff01fe31ff81f9e 0xfbfe03fc63ff03f3

def z925 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xfffe1ffc1ff81f87 0xffffc3ff83ff03f0

def z926 : W := mkw 0x27b93edbc0000000 0x04f727db78000000 0xe7ff1fffe0000003 0xfcffe3fffc000000

def z927 : W := mkw 0x0846816cb5679676 0xc108d02d96acf2ce 0xe8ce93fcf1e79e7f 0xbd19d27f9e3cf3cf

def z928 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x770f1c1f1e021ffa 0x6ee1e383e3c043ff

def z929 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x5ff01ce01ff81f84 0x6bfe039c03ff03f0

def z930 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xf8fe93fcf1fd9e67 0xff1fd27f9e3fb3cc

def z931 : W := mkw 0x04e4c04888d14000 0x009c9809111a2800 0xe8fef3fce1f9e003 0xbd1fde7f9c3f3c00

def z932 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xefffffffe1058007 0xfdfffffffc20b000

def z933 : W := mkw 0x26efc05a9cd74000 0x04ddf80b539ae800 0x9fffe01c1fffe005 0xf3fffc0383fffc00

def z934 : W := mkw 0x27fdfedbc0082088 0x24ffbfdb78010411 0xffffffffe11fe19f 0xfffffffffc23fc33

def z935 : W := mkw 0x07b93e9340000000 0x00f727d268000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z936 : W := mkw 0x100201243fbebfff 0xa200402487f7d7ff 0x180000001ffffffc 0x0300000003ffffff

def z937 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xf83fff1fe11ff1ff 0xff07ffe3fc23fe3f

def z938 : W := mkw 0x15b01fa02bb89da7 0x02b603f4057713b4 0xfff1ffe0ffffffe7 0xfffe3ffc1ffffffc

def z939 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0xc7c010e01ee01e06 0x38f8021c03dc03c0

def z940 : W := mkw 0x0044806880200402 0x0008900d10040080 0xe0ce93fcf0e00e03 0xbc19d27f9e1c01c0

def z941 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xdff11fe01ffe1f87 0xfbfe23fc03ffc3f0

def z942 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0xdff1f0e01fffee05 0xfbfe3e1c03fffdc0

def z943 : W := mkw 0x2044a05bc0000000 0x0408940b78000000 0xe0ce93ffe0000003 0xbc19d27ffc000000

def z944 : W := mkw 0x0044804880000000 0x0008900910000000 0xe8ce93fce1058007 0xbd19d27f9c20b000

def z945 : W := mkw 0x04e4c00008d14000 0x009c9800011a2800 0x9ff1e0001fffe005 0xf3fe3c0003fffc00

def z946 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x47c013e01ee00e00 0x28f8027c03dc01c0

def z947 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0x57c01ce01ee00f80 0x6af8039c03dc01f0

def z948 : W := mkw 0x1802012439fd96e7 0x43004024873fb2dc 0x0800000011fd9e64 0x01000000023fb3cc

def z949 : W := mkw 0x37fdfedbc2080981 0x06ffbfdb78410130 0xe7ffffffe0000183 0xfcfffffffc000030

def z950 : W := mkw 0x15b01ea00ab00d03 0x02b603d4015601a0 0xdff01fe01ff80e06 0xfbfe03fc03ff01c0

def z951 : W := mkw 0x024d804880000000 0x0049b00910000000 0xe7cf93fce0000003 0xfcf9f27f9c000000

def z952 : W := mkw 0x27fdfedbc4020010 0x84ffbfdb78804002 0xe7ffffffe002001b 0xfcfffffffc004003

def z953 : W := mkw 0x225de6dbc0000000 0x044bbcdb78000000 0x200fe3ffe0000001 0x0401fc7ffc000000

def z954 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xfff09fe0fff81f87 0xfffe13fc1fff03f0

def z955 : W := mkw 0x030b581616064b50 0x80616b02c2c0c96a 0xf70f7c1f1e067fff 0x7ee1ef83e3c0cfff

def z956 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xf7ffffffe0001187 0xfefffffffc000230

def z957 : W := mkw 0x0100192003201d06 0x00200324006403a0 0xcfc013e01fe01e06 0xb9f8027c03fc03c0

def z958 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xf7cf1fff1e061fff 0xfef9e3ffe3c0c3ff

def z959 : W := mkw 0x15b01fa02bb8bdaf 0x22b603f4057717b5 0xdff01fe01ff81ffe 0xfbfe03fc03ff03ff

def z960 : W := mkw 0x15b01ea00ab00d03 0x02b603d4015601a0 0x47f013e01ee00e00 0xa8fe027c03dc01c0

def z961 : W := mkw 0x0a4fa05ff447a278 0xe149f40bfe88f44f 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z962 : W := mkw 0x080201243ff7df76 0xc100402487fefbee 0x180000001ffffffc 0x0300000003ffffff

def z963 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x27ffefffe0000001 0xc4fffdfffc000000

def z964 : W := mkw 0x35b03fb34bb81d87 0x06b607f6697703b0 0xdff01fe31ff81f86 0xfbfe03fc63ff03f0

def z965 : W := mkw 0x0044804880000000 0x0008900910000000 0x40ce93fce0000000 0xa819d27f9c000000

def z966 : W := mkw 0x0044804880000000 0x0008900910000000 0xf0cf9fffe00611ff 0xfe19f3fffc00c23f

def z967 : W := mkw 0x235dfedbc0000000 0x046bbfdb78000000 0xe0cfffffe0000003 0xbc19fffffc000000

def z968 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0xdffff3e01fffe007 0xfbfffe7c03fffc00

def z969 : W := mkw 0x034d985a80000000 0x0069b30b50000000 0xe7ce93fce0000003 0xbcf9d27f9c000000

def z970 : W := mkw 0x27fdfedbccd34000 0x04ffbfdb799a6800 0xffffffffeffbe003 0xfffffffffdff7c00

def z971 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x5ff013e01ff81f84 0xabfe027c03ff03f0

def z972 : W := mkw 0x15b01fa00bb01d07 0x02b603f4017603a0 0xcff01fe01fe01e06 0xf9fe03fc03fc03c0

def z973 : W := mkw 0x001026016008a0a8 0x200204c02c011415 0xb831ec03e11fe1fd 0xd7063d807c23fc3f

def z974 : W := mkw 0x1db21fa43bfd9fe7 0x43b643f4877fb3fc 0x1f300c001ffd9fe4 0x43e6018003ffb3fc

def z975 : W := mkw 0x04e6c0001cd74000 0x009cd800039ae800 0x9ff0e0001fffe004 0xf3fe1c0003fffc00

def z976 : W := mkw 0x0100182002200d02 0x00200304004401a0 0xd7c01ce01ee01f86 0x7af8039c03dc03f0

def z977 : W := mkw 0x0846816cb16db6ee 0x6108d02d962db6dd 0xe8ce93fcf1fdfe67 0xbd19d27f9e3fbfcc

def z978 : W := mkw 0x0044804880000000 0x0008900910000000 0xe0fff3fce0000003 0xfc1ffe7f9c000000

def z979 : W := mkw 0x15b03fa14bb81d87 0x02b607f4297703b0 0xfff01fe3fff81f86 0xfffe03fc7fff03f0

def z980 : W := mkw 0x0010260140000000 0x000204c028000000 0xb831ef03e11ff1ff 0xd7063de07c23fe3f

def z981 : W := mkw 0x024d805a80000000 0x0049b00b50000000 0xe0cf93ffe0000003 0xbc19f27ffc000000

def z982 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0x770e1c1f1e061ffe 0x2ee1c383e3c0c3ff

def z983 : W := mkw 0x030b181616474b50 0x80616302c2c8e96a 0xf70f1c1f1e07ffff 0x7ee1e383e3c0ffff

def z984 : W := mkw 0x0309181602000b50 0x80612302c040016a 0xf70f1c1f1e001fff 0x7ee1e383e3c003ff

def z985 : W := mkw 0x06a940000c924000 0x00d5280001924800 0x9ff1e0001fffe005 0xf3fe3c0003fffc00

def z986 : W := mkw 0x06edc04880000000 0x00ddb80910000000 0xe7ce93fce0000003 0xbcf9d27f9c000000

def z987 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z988 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xe7ffffffe007e003 0xfcfffffffc00fc00

def z989 : W := mkw 0x27fdfedbca900900 0x04ffbfdb79520120 0xfffffffffff81f87 0xffffffffffff03f0

def z990 : W := mkw 0x080201243567d666 0x4100402486acfacc 0x0800000011e7fe64 0x01000000023cffcc

def z991 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xfff11fe3fffe1fff 0xfffe23fc7fffc3ff

def z992 : W := mkw 0x0846806c90650642 0x4108d00d920ca0c8 0x60ce13fcf0e00e02 0x2c19c27f9e1c01c0

def z993 : W := mkw 0x0044804880000000 0x0008900910000000 0xf8fff3fce11fe007 0xff1ffe7f9c23fc00

def z994 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x1ff00fe01ff81f84 0xc3fe01fc03ff03f0

def z995 : W := mkw 0x09103f7fe328bffe 0xe12207effc6517ff 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z996 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xe7cf1fffe0000003 0x7cf9e3fffc000000

def z997 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xdff01fe01fffff86 0xfbfe03fc03fffff0

def z998 : W := mkw 0x04e6800018d50000 0x009cd000031aa000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z999 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xc7f01fe01ee01f82 0xf8fe03fc03dc03f0

def z1000 : W := mkw 0x27fdfedbc4020000 0x04ffbfdb78804000 0xf7ffffffee020003 0xfefffffffdc04000

def z1001 : W := mkw 0x234df85bc0000000 0x0469bf0b78000000 0xe7cfffffe0000003 0xfcf9fffffc000000

def z1002 : W := mkw 0x08020124316db6ee 0x61004024862db6dd 0x0800000011e59ffc 0x01000000023cb3ff

def z1003 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0xd7c010e01ee00e04 0x7af8021c03dc01c0

def z1004 : W := mkw 0x27fdfedbc8900000 0x04ffbfdb79120000 0xefffffffe1f80003 0xfdfffffffc3f0000

def z1005 : W := mkw 0x224fe05fd4474250 0x8449fc0bfa88e84a 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z1006 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xe8ce93fcf1e18e03 0xbd19d27f9e3c31c0

def z1007 : W := mkw 0x0000012001201406 0x0000002400240280 0xdfc013e01fe01e06 0xfbf8027c03fc03c0

def z1008 : W := mkw 0x27edd8da80000000 0x04fdbb1b50000000 0x67ce13fce0000002 0x2cf9c27f9c000000

def z1009 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xe7ffffffe0041067 0xfcfffffffc00820c

def z1010 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xf831ff03f11fffff 0xff063fe07e23ffff

def z1011 : W := mkw 0x27fdfedbc0082088 0x24ffbfdb78010411 0xf7ffffffe01e71ff 0xfefffffffc03ce3f

def z1012 : W := mkw 0x37fdfedbca900901 0x06ffbfdb79520120 0xe7ffffffee000003 0xfcfffffffdc00000

def z1013 : W := mkw 0x15b01fa02bb8bdaf 0x22b603f4057717b5 0xfff11fe31fffffff 0xfffe23fc63ffffff

def z1014 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xfff11fe31ff81f87 0xfffe23fc63ff03f0

def z1015 : W := mkw 0x06edc0000cd34000 0x00ddb800019a6800 0x9ff1e0000fffe005 0xd3fe3c0001fffc00

def z1016 : W := mkw 0x0102181612040b50 0x80204302c240816a 0xf70e1c1f1e041fff 0x7ee1c383e3c083ff

def z1017 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x9fffec001ffff187 0xf3fffd8003fffe30

def z1018 : W := mkw 0x15a019a00bb01d07 0x02b40334017603a0 0x4fc013e01fe00e00 0xa9f8027c03fc01c0

def z1019 : W := mkw 0x27fdfedbc6020910 0x84ffbfdb78c04122 0xf7fffffffe021f9f 0xfeffffffffc043f3

def z1020 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x67ff7fffe0000002 0x6cffeffffc000000

def z1021 : W := mkw 0x15b01ea00ab80d83 0x02b603d4015701b0 0xdff01ce01ff80f84 0xfbfe039c03ff01f0

def z1022 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xc8ce93fcf1e19e06 0xb919d27f9e3c33c0

def z1023 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x57f01fe01ef81f82 0x6afe03fc03df03f0

def z1024 : W := mkw 0x035dbe5bc0000000 0x006bb7cb78000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1025 : W := mkw 0x001027216128b4ae 0x200204e42c251695 0xb831ef03f1ffffff 0xd7063de07e3fffff

def z1026 : W := mkw 0x0802012431249666 0x41004024862492cc 0x0000000010041e64 0x00000000020083cc

def z1027 : W := mkw 0x24f4e6c9c0000000 0x049e9cd938000000 0x40fef3fce0000000 0xa81fde7f9c000000

def z1028 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0x0000000000059e60 0x000000000000b3cc

def z1029 : W := mkw 0x15b01fa02bb8bdaf 0x22b603f4057717b5 0xfff09fe0ffffffff 0xfffe13fc1fffffff

def z1030 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xe7fef3fce0000003 0xbcffde7f9c000000

def z1031 : W := mkw 0x0002012431249666 0x00004024862492cc 0xe8ce93fcf1e59e67 0xbd19d27f9e3cb3cc

def z1032 : W := mkw 0x235dfedbc0000000 0x046bbfdb78000000 0xe03fffffe0000003 0xdc07fffffc000000

def z1033 : W := mkw 0x0b0b193637679f76 0xc1616326c6ecf3ee 0x1f010c031fe79ffc 0x43e0218063fcf3ff

def z1034 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xffffffffe1180007 0xfffffffffc230000

def z1035 : W := mkw 0x06edc0000cd34000 0x00ddb800019a6800 0x9ff1e0001ffbe004 0xf3fe3c0003ff7c00

def z1036 : W := mkw 0x1cf4a7e9e9f9b4af 0x639e94fd3d3f3695 0x08f0e3e0e1f9e000 0x811e1c7c1c3f3c00

def z1037 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xfff01fe01ffc1fe7 0xfffe03fc03ff83fc

def z1038 : W := mkw 0x024dc04880000000 0x0049b80910000000 0xe0cff3fce0000003 0xbc19fe7f9c000000

def z1039 : W := mkw 0x27fdfedbc2000900 0x04ffbfdb78400120 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z1040 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xc7fff3fce0000001 0xf8fffe7f9c000000

def z1041 : W := mkw 0x04e6c00018d54000 0x009cd800031aa800 0x9ffee0001ffde005 0xf3ffdc0003ffbc00

def z1042 : W := mkw 0x15b01ea00ab00d03 0x02b603d4015601a0 0x47f01ce01ee00e00 0x68fe039c03dc01c0

def z1043 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0xb8010c0311e79fff 0x57002180623cf3ff

def z1044 : W := mkw 0x25f4fec9c0000000 0x04be9fd938000000 0xe7fefffce0000003 0xfcffdfff9c000000

def z1045 : W := mkw 0x37fdfedbc8980081 0x06ffbfdb79130010 0xe7ffffffe0180003 0xfcfffffffc030000

def z1046 : W := mkw 0x0044a049c0000000 0x0008940938000000 0xe0cff3ffe0000003 0xbc19fe7ffc000000

def z1047 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xfff01fe3fffffffe 0xfffe03fc7fffffff

def z1048 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x68ce93fce1e59e63 0x8d19d27f9c3cb3cc

def z1049 : W := mkw 0x01103f216328bdae 0x202207e42c6517b5 0xfff1ffe3ffffffff 0xfffe3ffc7fffffff

def z1050 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xcff01fe01ff80e02 0xf9fe03fc03ff01c0

def z1051 : W := mkw 0x06efc0121cd74000 0x00ddf802439ae800 0xbfffe01f1fffe005 0xf7fffc03e3fffc00

def z1052 : W := mkw 0x15b03fa14bb81d87 0x02b607f4297703b0 0xfff1ffe3fffe1fff 0xfffe3ffc7fffc3ff

def z1053 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xf8ce93fcf1fffe67 0xbf19d27f9e3fffcc

def z1054 : W := mkw 0x15a019a00bb01d07 0x02b40334017603a0 0xdff013e01ff81e06 0xfbfe027c03ff03c0

def z1055 : W := mkw 0x0802012433659f76 0xc1004024866cb3ee 0x0800000011e59ffc 0x01000000023cb3ff

def z1056 : W := mkw 0x27fdfedbce924910 0x84ffbfdb79d24922 0xf7ffffffee1a619b 0xfefffffffdc34c33

def z1057 : W := mkw 0x0100192023209d26 0x00200324046413a4 0xffc19fe3ffe79fff 0xfff833fc7ffcf3ff

def z1058 : W := mkw 0x0a4f805e94470250 0xc149f00bd288e04a 0x000e001c00000000 0x0001c00380000000

def z1059 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xe8ce9ffff1e59fff 0xbd19d3fffe3cb3ff

def z1060 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x5fc01fe01ff81f86 0x2bf803fc03ff03f0

def z1061 : W := mkw 0x27fdfedbc0080080 0x04ffbfdb78010010 0xf7ffffffe0180183 0xfefffffffc030030

def z1062 : W := mkw 0x0ca2012439f59666 0x41944024873eb2cc 0x9ff000001ffd9e64 0xf3fe000003ffb3cc

def z1063 : W := mkw 0x2054a6c9c0000000 0x040a94d938000000 0xe0ce93fce0000003 0xbc19d27f9c000000

def z1064 : W := mkw 0x0144984882000900 0x0028930910400120 0xf7ce9ffcfe001f87 0xfef9d3ff9fc003f0

def z1065 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x8ffee0001ffde005 0xb1ffdc0003ffbc00

def z1066 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xfff1ffe31fffffff 0xfffe3ffc63ffffff

def z1067 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x1ff1e0001fffe004 0xc3fe3c0003fffc00

def z1068 : W := mkw 0x23193edbc0000000 0x046327db78000000 0x600f1fffe0000003 0x0c01e3fffc000000

def z1069 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x1831ef03e11ff1fc 0xc3063de07c23fe3f

def z1070 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xeffffffff1e00007 0xfdfffffffe3c0000

def z1071 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x673fffffe0000003 0x4ce7fffffc000000

def z1072 : W := mkw 0x08448168a1619426 0x4108902d142c3284 0xe8ce93fcf1e19e07 0xbd19d27f9e3c33c0

def z1073 : W := mkw 0x04e4804888900000 0x009c900911120000 0xfffe93fcfff80007 0xffffd27f9fff0000

def z1074 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xdff1ffe0ffffff87 0xfbfe3ffc1ffffff0

def z1075 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x1fffe0000fffe001 0xc3fffc0001fffc00

def z1076 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x0fffe0001fffe001 0xa1fffc0003fffc00

def z1077 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xdff09fe01ffd9f87 0xfbfe13fc03ffb3f0

def z1078 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x9ffee0001ff9e004 0xf3ffdc0003ff3c00

def z1079 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xf7ffffffe01a6003 0xfefffffffc034c00

def z1080 : W := mkw 0x15b01fa02bb89da7 0x02b603f4057713b4 0xfff01fe0fff81fe6 0xfffe03fc1fff03fc

def z1081 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x68ce93fcf1e19e62 0xad19d27f9e3c33cc

def z1082 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0xbfffec031fffe007 0xf7fffd8063fffc00

def z1083 : W := mkw 0x0802012435679676 0xc100402486acf2ce 0x0800000011e79e7c 0x01000000023cf3cf

def z1084 : W := mkw 0x0eab41243df7d666 0x41d5682487befacc 0x1f3160001ffffe64 0x43e62c0003ffffcc

def z1085 : W := mkw 0x06efc04c9cd74240 0x00ddf809939ae848 0xfffff3fcfffffe67 0xfffffe7f9fffffcc

def z1086 : W := mkw 0x06edc00008d14000 0x00ddb800011a2800 0x9fffe0001ff9e005 0xf3fffc0003ff3c00

def z1087 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x1fffe0001ffbe000 0xe3fffc0003ff7c00

def z1088 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0x0800000001e58060 0x01000000003cb00c

def z1089 : W := mkw 0x14a001200bb81d87 0x02940024017703b0 0xdff013e01ff81f86 0xfbfe027c03ff03f0

def z1090 : W := mkw 0x06ab00001c960000 0x00d560000392c000 0x9fffe0001fffe005 0xf3fffc0003fffc00

def z1091 : W := mkw 0x0846806c90650642 0x4108d00d920ca0c8 0xe8ce93fcf1e58e07 0xbd19d27f9e3cb1c0

def z1092 : W := mkw 0x26fde6dbc0000000 0x04dfbcdb78000000 0x00fee3fce0000000 0x801fdc7f9c000000

def z1093 : W := mkw 0x11101fa003281d87 0x022203f4006503b0 0xdfc01fe01fe01f86 0xfbf803fc03fc03f0

def z1094 : W := mkw 0x23193edbc0000000 0x046327db78000000 0xe73fffffe0000003 0xfce7fffffc000000

def z1095 : W := mkw 0x180201243bfdbfef 0x63004024877fb7fd 0x180000001ffffffc 0x0300000003ffffff

def z1096 : W := mkw 0x06edc0000cd34000 0x00ddb800019a6800 0x9fffe0000ffbe001 0xf3fffc0001ff7c00

def z1097 : W := mkw 0x15b01fa02bb89da7 0x02b603f4057713b4 0xdff01fe01ffd9fe6 0xfbfe03fc03ffb3fc

def z1098 : W := mkw 0x37fdfedbca980981 0x06ffbfdb79530130 0xf7fffffffe181f87 0xfeffffffffc303f0

def z1099 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0xbfffe0001ffff067 0xf7fffc0003fffe0c

def z1100 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x1fff60001fffe004 0x63ffec0003fffc00

def z1101 : W := mkw 0x0846816c91651646 0x4108d02d922ca2c8 0xe8ce93fcf1e01e07 0xbd19d27f9e3c03c0

def z1102 : W := mkw 0x0a4f815eb5479274 0xc149f02bd6a8f24e 0xb80f8f1fe10791ff 0xd701f1e3fc20f23f

def z1103 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0xc7f010e01ee00e00 0xf8fe021c03dc01c0

def z1104 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xcfc01fe01fe01f86 0xb9f803fc03fc03f0

def z1105 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x3831ec03e11ff1fd 0x47063d807c23fe3f

def z1106 : W := mkw 0x0a4fc14cb547d264 0x4149f82996a8fa4c 0xb83fe31ce11ff067 0xd707fc639c23fe0c

def z1107 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0xb8f1ef03f1fff1ff 0xf71e3de07e3ffe3f

def z1108 : W := mkw 0x0046804c90450240 0x0008d0099208a048 0xe8ce93fcf1e59e67 0xbd19d27f9e3cb3cc

def z1109 : W := mkw 0x15b03fa16bb89da7 0x02b607f42d7713b4 0xfff1ffe3fffd9fe7 0xfffe3ffc7fffb3fc

def z1110 : W := mkw 0x15a019a00bb81d87 0x02b40334017703b0 0xdff010e01ff81f84 0xfbfe021c03ff03f0

def z1111 : W := mkw 0x15b01ea00ab00d03 0x02b603d4015601a0 0x47c01fe01ee00e02 0x28f803fc03dc01c0

def z1112 : W := mkw 0x27fdfedbc0082088 0x24ffbfdb78010411 0xe7ffffffe0186003 0xfcfffffffc030c00

def z1113 : W := mkw 0x05a019200bb01d06 0x00b40324017603a0 0xdff01fe01ff81f86 0xfbfe03fc03ff03f0

def z1114 : W := mkw 0x0144984880000000 0x0028930910000000 0xe7ce9ffce0000003 0xfcf9d3ff9c000000

def z1115 : W := mkw 0x110019200bb81d87 0x02200324017703b0 0xdfc01fe01ff81f86 0xfbf803fc03ff03f0

def z1116 : W := mkw 0x0a4fc04cb447c260 0x4149f8099688f84c 0x200e801ce0058061 0x0401d0039c00b00c

def z1117 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0x57f010e01ef80e00 0x6afe021c03df01c0

def z1118 : W := mkw 0x15a019a00bb01d07 0x02b40334017603a0 0x4fc010e01fe01e04 0x29f8021c03fc03c0

def z1119 : W := mkw 0x37fdfedbca982989 0x26ffbfdb79530531 0xf7ffffffee1a619b 0xfefffffffdc34c33

def z1120 : W := mkw 0x14b007a00bb81d87 0x029600f4017703b0 0x9ff003e01ff81f84 0xf3fe007c03ff03f0

def z1121 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xdff11fe31ffa1f9e 0xfbfe23fc63ff43f3

def z1122 : W := mkw 0x25f4bedbc0000000 0x04be97db78000000 0xe7fe9fffe0000003 0xfcffd3fffc000000

def z1123 : W := mkw 0x15a019a00bb81d87 0x02b40334017703b0 0xdfc013e01ff81f86 0xbbf8027c03ff03f0

def z1124 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x40ce13fcf0e00e00 0x2819c27f9e1c01c0

def z1125 : W := mkw 0x0044804880000000 0x0008900910000000 0x60ce13fce0000002 0x2c19c27f9c000000

def z1126 : W := mkw 0x04a200001cd74000 0x00944000039ae800 0x9ff1e0001fffe005 0xf3fe3c0003fffc00

def z1127 : W := mkw 0x05b01fa009b01406 0x00b603f401360280 0xdff01fe01ff81e06 0xfbfe03fc03ff03c0

def z1128 : W := mkw 0x15b01fa02bb89da7 0x02b603f4057713b4 0xdff09fe0fff99f86 0xfbfe13fc1fff33f0

def z1129 : W := mkw 0x0846c16cb165d666 0x4108d82d962cbacc 0xe8cef3fcf1e5fe67 0xbd19de7f9e3cbfcc

def z1130 : W := mkw 0x0846806c90650642 0x4108d00d920ca0c8 0x40ce93fcf0e00e00 0xa819d27f9e1c01c0

def z1131 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xf8cf93fcf1e79e67 0xff19f27f9e3cf3cc

def z1132 : W := mkw 0x08020124316db6ee 0x61004024862db6dd 0x0800000011fdfe64 0x01000000023fbfcc

def z1133 : W := mkw 0x0a4fc04c94474240 0x4149f8099288e848 0x000fe01c0007e001 0x0001fc038000fc00

def z1134 : W := mkw 0x06efc0041cd74250 0x80ddf800839ae84a 0x9fffe0001fffe07d 0xf3fffc0003fffc0f

def z1135 : W := mkw 0x11103fb76328bfff 0xa22207f6ec6517ff 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z1136 : W := mkw 0x04a0002008b00402 0x0094000401160080 0x47c010e01ee00e00 0x28f8021c03dc01c0

def z1137 : W := mkw 0x0a4f804cb4478260 0x4149f0099688f04c 0x200f801ce0078061 0x0401f0039c00f00c

def z1138 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xfff1ffe3fff9ff87 0xfffe3ffc7fff3ff0

def z1139 : W := mkw 0x07fddec880000000 0x00ffbbd910000000 0xe7fffffce0000003 0xfcffffff9c000000

def z1140 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xf7ffffffe0060007 0xfefffffffc00c000

def z1141 : W := mkw 0x15b05fa00bb85d87 0x02b60bf401770bb0 0xdff07fe01ff87f86 0xfbfe0ffc03ff0ff0

def z1142 : W := mkw 0x04b0272169b8b4ae 0x209604e42d371695 0xfff1ffe3ffffffff 0xfffe3ffc7fffffff

def z1143 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xdff01fe01ffe1ffe 0xfbfe03fc03ffc3ff

def z1144 : W := mkw 0x0144985a80000000 0x0028930b50000000 0xe0ce9fffe0000003 0xbc19d3fffc000000

def z1145 : W := mkw 0x034d985a86020910 0x8069b30b50c04122 0xf7cf9fffee02019b 0xfef9f3fffdc04033

def z1146 : W := mkw 0x0044804880000000 0x0008900910000000 0x600e93fce0000003 0x0c01d27f9c000000

def z1147 : W := mkw 0x24e4c0c880000000 0x049c981910000000 0xe0ce93fce0000003 0xbc19d27f9c000000

def z1148 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xe8ce13fcf1e01e66 0xbd19c27f9e3c03cc

def z1149 : W := mkw 0x27fdfedbc0414000 0x04ffbfdb78082800 0xe7ffffffe001e003 0xfcfffffffc003c00

def z1150 : W := mkw 0x15b03fa14bb83d8f 0x22b607f4297707b1 0xfff17fe31ffe7fff 0xfffe2ffc63ffcfff

def z1151 : W := mkw 0x17b93e934e9a2999 0xa2f727d269d34533 0x17316c030e1a6198 0x42e62d8061c34c33

def z1152 : W := mkw 0x06efc0041cd74240 0x00ddf800839ae848 0xfffffc1f1fffffff 0xffffff83e3ffffff

def z1153 : W := mkw 0x24f4e6c9c0000000 0x049e9cd938000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1154 : W := mkw 0x19103fede328bfef 0x632207fdbc6517fd 0x60001fffe0001ffa 0x0c0003fffc0003ff

def z1155 : W := mkw 0x0846806cb0658662 0x4108d00d960cb0cc 0xe0ce93fcf0e58e63 0xbc19d27f9e1cb1cc

def z1156 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xdff17fe01ffa7f86 0xfbfe2ffc03ff4ff0

def z1157 : W := mkw 0x0846816cb5679666 0x4108d02d96acf2cc 0xf8ce93fcffe79e67 0xbf19d27f9ffcf3cc

def z1158 : W := mkw 0x27fdfedbcc924000 0x04ffbfdb79924800 0xe7ffffffee000003 0xfcfffffffdc00000

def z1159 : W := mkw 0x27fdfedbcc9a6088 0x24ffbfdb79934c11 0xf7ffffffee1a619b 0xfefffffffdc34c33

def z1160 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xff0f9c1f1f079fff 0xffe1f383e3e0f3ff

def z1161 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xe0ce93fcf0e01e63 0xbc19d27f9e1c03cc

def z1162 : W := mkw 0x0846816cb16d96e6 0x4108d02d962db2dc 0xf8ce93fcf1fd9fe7 0xbf19d27f9e3fb3fc

def z1163 : W := mkw 0x235dfedbc0000000 0x046bbfdb78000000 0xe70fffffe0000003 0x7ce1fffffc000000

def z1164 : W := mkw 0x15b03ea14ab82d8b 0x22b607d4295705b1 0x57f17ce31efa6f98 0x6afe2f9c63df4df3

def z1165 : W := mkw 0x0054a649c0082088 0x200a94c938010411 0xf0ffffffe01a619b 0xfe1ffffffc034c33

def z1166 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xe8fef3fcf1fdfe67 0xbd1fde7f9e3fbfcc

def z1167 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x68ce13fcf1e59e66 0x2d19c27f9e3cb3cc

def z1168 : W := mkw 0x15b01ea00ab80d83 0x02b603d4015701b0 0x47c01ce01ee00f80 0x28f8039c03dc01f0

def z1169 : W := mkw 0x0a5fa75ff54fb2fc 0xe14bf4ebfea9f65f 0xb83fef1fe11ff1ff 0xd707fde3fc23fe3f

def z1170 : W := mkw 0x06efc0041cd74240 0x00ddf800839ae848 0xdffff01c1fffee05 0xfbfffe0383fffdc0

def z1171 : W := mkw 0x2a4fe05ff447c260 0x4549fc0bfe88f84c 0x200fe01fe007e061 0x0401fc03fc00fc0c

def z1172 : W := mkw 0x27fddeda80000000 0x04ffbbdb50000000 0xe7fe9ffce0000003 0xfcffd3ff9c000000

def z1173 : W := mkw 0x0802012437269f76 0xc100402486e4d3ee 0x100000001e061ffc 0x0200000003c0c3ff

def z1174 : W := mkw 0x0802016cb1249666 0x4100402d962492cc 0xe8ce13fcf1e41e67 0xbd19c27f9e3c83cc

def z1175 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xf70ffc1f1e07ffff 0x7ee1ff83e3c0ffff

def z1176 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0x57c010e01ee01f84 0x2af8021c03dc03f0

def z1177 : W := mkw 0x27edd8da80000000 0x04fdbb1b50000000 0xe7fff3fce0000003 0xfcfffe7f9c000000

def z1178 : W := mkw 0x0100182002200d02 0x00200304004401a0 0x47c010e01ee00e00 0x28f8021c03dc01c0

def z1179 : W := mkw 0x0846812431659666 0x4108d024862cb2cc 0x08c0800011e59e64 0x81181000023cb3cc

def z1180 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xfff09fe3fffd9fff 0xfffe13fc7fffb3ff

def z1181 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xe7ffffffe00011fb 0xfcfffffffc00023f

def z1182 : W := mkw 0x020b00001cd74000 0x00416000039ae800 0x9f3fe0001fffe005 0xf3e7fc0003fffc00

def z1183 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xe7ce9fffe0000003 0xbcf9d3fffc000000

def z1184 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0x67c01fe3fee01ffa 0x2cf803fc7fdc03ff

def z1185 : W := mkw 0x37b97e934a982989 0x26f72fd269530531 0x17316c030e1a6198 0x42e62d8061c34c33

def z1186 : W := mkw 0x0846816cb16db6ee 0x6108d02d962db6dd 0xf8fff3fcf1ffffff 0xff1ffe7f9e3fffff

def z1187 : W := mkw 0x0802012439f59666 0x41004024873eb2cc 0x180000001ffd9e64 0x0300000003ffb3cc

def z1188 : W := mkw 0x27edf8dbc0000000 0x04fdbf1b78000000 0xe7cff3ffe0000003 0xbcf9fe7ffc000000

def z1189 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0x60ce93fcf0e59e63 0x2c19d27f9e1cb3cc

def z1190 : W := mkw 0x27fdfedbc2000910 0x84ffbfdb78400122 0xe7ffffffe000019b 0xfcfffffffc000033

def z1191 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0xe7fffffff0001e07 0xfcfffffffe0003c0

def z1192 : W := mkw 0x26fde6dbc0000000 0x04dfbcdb78000000 0xe0fff3ffe0000003 0xbc1ffe7ffc000000

def z1193 : W := mkw 0x15b03fa14bb83d8f 0x22b607f4297707b1 0xdff1ffe31fffff9f 0xfbfe3ffc63fffff3

def z1194 : W := mkw 0x001027016108b0ac 0x200204e02c211615 0x2831ef03e11ff1fb 0x85063de07c23fe3f

def z1195 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x67feffffe0000002 0xacffdffffc000000

def z1196 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x9fffe0001ffff1fd 0xf3fffc0003fffe3f

def z1197 : W := mkw 0x15a019a00bb81d87 0x02b40334017703b0 0xdfc01ce01ff81f86 0x7bf8039c03ff03f0

def z1198 : W := mkw 0x37b97e934e9a4981 0x06f72fd269d34930 0x17316c030e1a6180 0x42e62d8061c34c30

def z1199 : W := mkw 0x04f486c880000000 0x009e90d910000000 0xe0fe93fce0000003 0xbc1fd27f9c000000

def z1200 : W := mkw 0x0846816cb165b66e 0x6108d02d962cb6cd 0xe8ce93fcf1e7fe7f 0xbd19d27f9e3cffcf

def z1201 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xfff17fe3fffa7ffe 0xfffe2ffc7fff4fff

def z1202 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xfff01fe31ff81ffe 0xfffe03fc63ff03ff

def z1203 : W := mkw 0x180201243fffdfe7 0x4300402487fffbfc 0x180000001fffffe4 0x0300000003fffffc

def z1204 : W := mkw 0x04a0012009b01406 0x0094002401360280 0xcfc013e01fe01e06 0xb9f8027c03fc03c0

def z1205 : W := mkw 0x27edd8da80000000 0x04fdbb1b50000000 0x47ce93fce0000000 0xa8f9d27f9c000000

def z1206 : W := mkw 0x2154bedbc0000000 0x042a97db78000000 0x60ce1fffe0000002 0x2c19c3fffc000000

def z1207 : W := mkw 0x06edc0488c924000 0x00ddb80911924800 0xf7fff3fcee1a6003 0xfefffe7f9dc34c00

def z1208 : W := mkw 0x0054864880000000 0x000a90c910000000 0xe0fe9ffce0000003 0xfc1fd3ff9c000000

def z1209 : W := mkw 0x0046816c91241646 0x0008d02d922482c8 0xe8ce93fcf1e41e67 0xbd19d27f9e3c83cc

def z1210 : W := mkw 0x04a0012029b09426 0x0094002405361284 0xfff1f3e0fffffe67 0xfffe3e7c1fffffcc

def z1211 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0xdff01ce01ff81f86 0xfbfe039c03ff03f0

def z1212 : W := mkw 0x04e4c04880000000 0x009c980910000000 0xe0fef3fce0000003 0xbc1fde7f9c000000

def z1213 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xe70f1c1f1e001ffb 0x7ce1e383e3c003ff

def z1214 : W := mkw 0x0000010021009024 0x0000002004201204 0xb831ef03e11ff1ff 0xd7063de07c23fe3f

def z1215 : W := mkw 0x0a4fc05eb447c270 0xc149f80bd688f84e 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z1216 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0xcfc010e01fe00e04 0xb9f8021c03fc01c0

def z1217 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xfff0ffe0fffdffe7 0xfffe1ffc1fffbffc

def z1218 : W := mkw 0x27fdfedbc0000000 0x04ffbfdb78000000 0x47ffffffe0000000 0xe8fffffffc000000

def z1219 : W := mkw 0x27fdfedbcc924000 0x04ffbfdb79924800 0xffffffffef1fe007 0xfffffffffde3fc00

def z1220 : W := mkw 0x15a019a00bb01d07 0x02b40334017603a0 0x47c013e01ee01e02 0x28f8027c03dc03c0

def z1221 : W := mkw 0x15b01ea00ab80d83 0x02b603d4015701b0 0xd7f01ce01ef81f86 0x7afe039c03df03f0

def z1222 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0xa800000011e59e67 0x15000000023cb3cc

def z1223 : W := mkw 0x26ede05bc0000000 0x04ddbc0b78000000 0xe7fff3ffe0000003 0xfcfffe7ffc000000

def z1224 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0x4ff01fe01ff81f82 0xa9fe03fc03ff03f0

def z1225 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xc8ce93fcf1e58e05 0xb919d27f9e3cb1c0

def z1226 : W := mkw 0x15a018a00ab00d03 0x02b40314015601a0 0x5fc010e01ff80e04 0x2bf8021c03ff01c0

def z1227 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0x4ff0f3e0fff9ee00 0xa9fe1e7c1fff3dc0

def z1228 : W := mkw 0x15b01fa00bb83d8f 0x22b603f4017707b1 0xdff01fe01ffa7f9e 0xfbfe03fc03ff4ff3

def z1229 : W := mkw 0x37fdfedbce9a4981 0x06ffbfdb79d34930 0xf7ffffffee1a6183 0xfefffffffdc34c30

def z1230 : W := mkw 0x08020124376fbffe 0xe100402486edf7ff 0x180000001ffffffc 0x0300000003ffffff

def z1231 : W := mkw 0x27fdfedbc2000900 0x04ffbfdb78400120 0xf7ffffffee000183 0xfefffffffdc00030

def z1232 : W := mkw 0x06efc0161cd74250 0x80ddf802c39ae84a 0xfffff01f1ffffe7f 0xfffffe03e3ffffcf

def z1233 : W := mkw 0x15b01fa00bb81d87 0x02b603f4017703b0 0xdff1ffe01ff81f87 0xfbfe3ffc03ff03f0

def z1234 : W := mkw 0x04e4c00008d14000 0x009c9800011a2800 0x1ff0e0000ff9e000 0xc3fe1c0001ff3c00

def z1235 : W := mkw 0x27fdfedbc8904000 0x04ffbfdb79120800 0xe7ffffffe0186003 0xfcfffffffc030c00

def z1236 : W := mkw 0x24f4e6c9c0000000 0x049e9cd938000000 0x20fee3fce0000001 0x841fdc7f9c000000

def z1237 : W := mkw 0x0a4fe04df447e268 0x6149fc09be88fc4d 0x200fe01fe007e079 0x0401fc03fc00fc0f

def z1238 : W := mkw 0x030b181616060b50 0x80616302c2c0c16a 0xf73ffc1f1e061fff 0xfee7ff83e3c0c3ff

def z1239 : W := mkw 0x180201243fff9ff7 0xc300402487fff3fe 0x180000001fff9ffc 0x0300000003fff3ff

def z1240 : W := mkw 0x27efd8de9ed74b50 0x84fdfb1bd3dae96a 0x47ce10fc1ee00e00 0x28f9c21f83dc01c0

def z1241 : W := mkw 0x0844816ca1209666 0x4108902d942412cc 0xe8ce93fcf1e01e67 0xbd19d27f9e3c03cc

def z1242 : W := mkw 0x0844816ca1619666 0x4108902d942c32cc 0xe8ce93fce1e19e63 0xbd19d27f9c3c33cc

def z1243 : W := mkw 0x06efc0001cd74000 0x00ddf800039ae800 0x9fffec031fffe19d 0xf3fffd8063fffc33

def z1244 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0xc800100011e59e66 0x39000200023cb3cc

def z1245 : W := mkw 0x0044804880000000 0x0008900910000000 0xe8ce93fcf1e00007 0xbd19d27f9e3c0000

def z1246 : W := mkw 0x06fde649c0000000 0x00dfbcc938000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1247 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xe0ce13fcf0e41e67 0x3c19c27f9e1c83cc

def z1248 : W := mkw 0x0846816cb1659666 0x4108d02d962cb2cc 0xe8fff3fcf1e59e67 0xfd1ffe7f9e3cb3cc

def z1249 : W := mkw 0x0802012431659666 0x41004024862cb2cc 0x88c0000011e59e64 0xb1180000023cb3cc

def z1250 : W := mkw 0x000020016000a028 0x200004002c001405 0xb831ec03e11ff1ff 0xd7063d807c23fe3f

def z1251 : W := mkw 0x15b03fa16bb8bdaf 0x22b607f42d7717b5 0xdff1ffe3fffbff9e 0xfbfe3ffc7fff7ff3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z7,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z8,z8,z6]),(0,[z0,z2,z3,z9,z4,z5,z6]),(0,[z10,z0,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z5,z12]),(1,[z0,z13,z2,z14,z5,z6]),(0,[z0,z2,z3,z4,z5,z15,z6]),(0,[z0,z2,z3,z16,z17,z5,z6])],[(0,[z2,z3,z18,z4,z19,z5,z6]),(0,[z0,z2,z3,z18,z4,z8,z6]),(0,[z0,z13,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z21,z22,z4,z5]),(0,[z0,z23,z2,z3,z4,z5,z24]),(0,[z0,z11,z2,z3,z4,z5,z25]),(0,[z0,z2,z3,z26,z4,z5,z6])],[(0,[z0,z2,z27,z3,z4,z5,z6]),(1,[z0,z28,z21,z4,z5,z6]),(0,[z0,z2,z29,z3,z22,z4,z5])],[(0,[z0,z30,z31,z3,z4,z5,z6]),(0,[z0,z2,z3,z32,z22,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z33]),(0,[z34,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z14,z8,z6]),(0,[z0,z2,z3,z4,z5,z35,z6])],[(0,[z0,z2,z36,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z37]),(0,[z0,z11,z23,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z38,z5,z6])],[(0,[z39,z0,z2,z3,z4,z5,z6]),(1,[z40,z2,z3,z18,z5,z6]),(0,[z41,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z42,z43,z4,z5,z6]),(1,[z0,z2,z3,z44,z4,z5])],[(0,[z45,z0,z2,z3,z4,z5,z6]),(0,[z46,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z47,z0,z2,z3,z18,z5,z6]),(0,[z0,z2,z3,z4,z48,z20,z6]),(0,[z0,z2,z3,z4,z5,z49,z6]),(0,[z50,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z51,z6])],[(0,[z0,z52,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z6,z53]),(0,[z0,z54,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z20,z55,z6]),(0,[z41,z0,z2,z3,z4,z17,z6]),(0,[z0,z11,z56,z2,z3,z4,z5])],[(0,[z57,z0,z58,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z20,z6,z59]),(0,[z0,z2,z60,z42,z4,z5,z6]),(0,[z61,z0,z2,z3,z4,z5,z6]),(0,[z0,z62,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z63])],[(0,[z57,z0,z2,z3,z4,z5,z64]),(0,[z65,z0,z2,z3,z4,z8,z6]),(0,[z0,z66,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z16,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z67,z6])],[(0,[z0,z2,z3,z4,z5,z6,z68]),(0,[z0,z69,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z70,z5,z6]),(0,[z0,z2,z3,z4,z19,z20,z6]),(0,[z0,z2,z3,z22,z4,z20,z5]),(0,[z41,z0,z2,z3,z5,z71,z6]),(0,[z72,z0,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z5,z73,z6])],[(0,[z0,z2,z3,z74,z4,z5,z6]),(0,[z0,z58,z2,z3,z4,z5,z6]),(0,[z75,z2,z76,z3,z4,z5,z6]),(1,[z0,z77,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z78]),(0,[z0,z2,z3,z4,z5,z6,z79]),(0,[z65,z0,z2,z4,z5,z67,z6]),(0,[z0,z2,z3,z4,z5,z80,z81])]],
   [[(0,[z0,z2,z3,z4,z82,z8,z6]),(0,[z0,z23,z3,z83,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z84]),(0,[z0,z2,z29,z3,z4,z5,z85]),(0,[z0,z86,z2,z3,z4,z5,z6])],[(0,[z0,z2,z87,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z88,z6]),(0,[z89,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z90,z3,z4,z5,z6]),(0,[z0,z91,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z92,z6]),(0,[z0,z2,z3,z16,z4,z17,z6])],[(0,[z0,z2,z4,z5,z67,z6,z85])],[(0,[z0,z2,z3,z4,z93,z20,z6]),(0,[z0,z2,z3,z4,z5,z94,z6]),(0,[z0,z2,z3,z5,z71,z6,z95])],[(0,[z0,z96,z2,z3,z4,z5,z6]),(0,[z97,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z20,z6]),(0,[z0,z2,z98,z4,z5,z8,z6]),(0,[z0,z99,z2,z3,z4,z5,z6]),(1,[z0,z52,z3,z4,z100,z6]),(0,[z0,z2,z3,z4,z5,z101,z6]),(0,[z0,z2,z3,z4,z102,z5,z6]),(0,[z0,z2,z3,z22,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z103,z6]),(0,[z0,z104,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z105,z6]),(0,[z0,z106,z2,z3,z4,z5,z6])],[(0,[z107,z0,z31,z3,z4,z5,z6]),(0,[z0,z2,z3,z18,z14,z5,z6]),(0,[z0,z2,z3,z4,z8,z108,z6]),(0,[z0,z109,z2,z3,z4,z5,z6]),(0,[z0,z52,z2,z3,z22,z4,z5])],[(0,[z0,z69,z3,z21,z4,z5,z6]),(0,[z0,z2,z3,z110,z4,z5,z6]),(0,[z0,z111,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z112]),(0,[z0,z2,z3,z4,z5,z113,z6]),(0,[z0,z11,z2,z3,z4,z5,z108]),(1,[z0,z2,z3,z4,z114,z108])]],
   [[(0,[z40,z2,z3,z18,z4,z5,z6]),(0,[z0,z2,z3,z4,z115,z8,z6]),(0,[z0,z116,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z22,z4,z5,z67])],[(1,[z0,z2,z3,z22,z4,z8]),(0,[z0,z2,z3,z4,z5,z117,z6]),(0,[z0,z2,z21,z4,z118,z5,z6]),(0,[z0,z2,z3,z4,z119,z5,z6]),(0,[z0,z2,z120,z3,z4,z5,z6]),(0,[z65,z0,z2,z3,z22,z4,z5])],[(0,[z0,z2,z3,z4,z5,z121,z6]),(0,[z0,z122,z2,z3,z4,z5,z6]),(0,[z0,z0,z2,z3,z4,z20,z6]),(0,[z0,z123,z2,z3,z4,z5,z12]),(0,[z0,z11,z2,z3,z4,z5,z85]),(0,[z0,z2,z3,z4,z5,z124,z6]),(0,[z0,z2,z3,z4,z5,z6,z125])],[(0,[z0,z69,z2,z3,z22,z4,z5]),(1,[z0,z2,z3,z4,z126,z6]),(0,[z47,z2,z3,z4,z19,z5,z6]),(0,[z0,z2,z3,z4,z127,z5,z6]),(0,[z0,z128,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z129,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z130,z6]),(0,[z0,z131,z2,z3,z4,z5,z6])],[(0,[z0,z2,z132,z3,z4,z5,z6]),(0,[z0,z2,z133,z3,z4,z14,z6]),(1,[z134,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z135,z5,z6]),(0,[z136,z0,z2,z3,z4,z5,z6])],[(1,[z0,z137,z3,z4,z5,z6]),(0,[z0,z2,z3,z138,z4,z5,z6]),(0,[z139,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z140,z4,z5,z6]),(0,[z0,z2,z3,z141,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z121]),(0,[z0,z2,z3,z142,z4,z5,z6]),(0,[z0,z2,z3,z83,z4,z20,z6]),(0,[z0,z2,z43,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z143,z5,z6]),(0,[z0,z52,z2,z144,z4,z5,z6]),(0,[z145,z0,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z5,z146])],[(0,[z147,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z148,z5,z6]),(1,[z0,z2,z149,z3,z4,z5])]],
   [[(0,[z107,z0,z2,z3,z150,z5,z6]),(0,[z0,z2,z3,z4,z5,z151,z6]),(0,[z0,z2,z152,z3,z4,z8,z6]),(0,[z0,z153,z2,z3,z4,z5,z6]),(0,[z0,z2,z154,z3,z4,z5,z6]),(0,[z0,z13,z2,z3,z138,z5,z6]),(0,[z0,z2,z3,z155,z4,z5,z6]),(0,[z156,z0,z2,z3,z4,z5,z6])],[(0,[z0,z157,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z22,z4,z100,z5]),(0,[z0,z158,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z159]),(0,[z0,z160,z2,z3,z4,z5,z6]),(0,[z161,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z20,z162,z6]),(0,[z163,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z164])],[(1,[z107,z31,z3,z4,z5,z6]),(0,[z0,z2,z165,z3,z4,z5,z6]),(0,[z166,z0,z2,z3,z4,z5,z6]),(0,[z0,z167,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z168,z4,z5,z6])],[(0,[z0,z2,z3,z169,z4,z5,z6]),(0,[z34,z0,z11,z2,z3,z4,z5]),(0,[z170,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z171,z5,z6]),(0,[z172,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z173,z6])],[(1,[z0,z2,z3,z4,z174,z6]),(0,[z0,z175,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z20,z6,z12]),(0,[z0,z2,z3,z176,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z177,z6]),(0,[z0,z2,z178,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z179,z5,z6]),(0,[z180,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z44,z4,z5,z6]),(0,[z0,z2,z3,z22,z4,z14,z5]),(0,[z0,z11,z181,z2,z3,z4,z5])],[(0,[z47,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z20,z81,z6]),(0,[z0,z2,z3,z182,z4,z5,z6]),(0,[z0,z2,z3,z4,z183,z5,z6]),(0,[z0,z2,z3,z22,z4,z5,z71]),(1,[z0,z2,z3,z5,z6,z184])]],
   [[(0,[z75,z0,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z5,z185,z12]),(0,[z0,z2,z3,z186,z4,z5,z6]),(0,[z41,z0,z2,z3,z4,z5,z6]),(0,[z187,z0,z2,z3,z4,z5,z6])],[(0,[z188,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z189,z4,z5,z6]),(1,[z0,z2,z60,z4,z190,z6]),(0,[z191,z0,z2,z3,z4,z5,z6])],[(0,[z0,z11,z2,z3,z18,z4,z5]),(0,[z180,z34,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z192,z4,z5,z6]),(0,[z0,z2,z3,z4,z193,z8,z6]),(0,[z0,z2,z3,z194,z4,z5,z6]),(0,[z0,z2,z3,z4,z20,z71,z6]),(0,[z0,z2,z3,z4,z195,z5,z6]),(0,[z0,z2,z3,z22,z4,z5,z12]),(0,[z196,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z197,z3,z4,z5,z81]),(0,[z0,z2,z198,z3,z4,z5,z6])],[(0,[z107,z0,z2,z3,z4,z199,z6]),(0,[z0,z2,z3,z4,z200,z5,z6]),(0,[z0,z23,z2,z3,z4,z20,z6]),(0,[z0,z2,z43,z3,z4,z5,z159]),(0,[z41,z201,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z202,z6])],[(0,[z203,z0,z2,z3,z4,z5,z6]),(0,[z203,z0,z69,z3,z4,z5,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z204,z5,z6]),(0,[z57,z2,z3,z32,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z190,z6]),(0,[z0,z205,z2,z3,z4,z5,z6]),(1,[z65,z0,z2,z4,z5,z67])],[(0,[z57,z0,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z8,z67,z6]),(0,[z0,z2,z206,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z207]),(0,[z40,z0,z2,z3,z4,z208,z6]),(1,[z34,z2,z3,z4,z8,z6]),(0,[z34,z2,z3,z4,z5,z8,z6]),(0,[z0,z2,z3,z4,z5,z12,z209])],[(0,[z210,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z76,z21,z4,z5,z6]),(0,[z211,z0,z2,z3,z4,z5,z185]),(0,[z0,z2,z3,z4,z212,z5,z6]),(0,[z0,z2,z3,z16,z4,z5,z6]),(0,[z0,z11,z2,z3,z26,z4,z5]),(1,[z0,z11,z2,z3,z22,z5])]],
   [[(0,[z213,z0,z2,z3,z4,z5,z6]),(0,[z214,z0,z2,z3,z4,z5,z6])],[(0,[z215,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z216,z3,z4,z5,z6]),(0,[z41,z0,z2,z60,z3,z4,z6]),(0,[z217,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z218,z3,z4,z5,z6]),(0,[z0,z2,z3,z83,z19,z5,z6]),(0,[z0,z219,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z21,z4,z5]),(0,[z0,z157,z2,z3,z4,z25,z6]),(0,[z0,z2,z3,z220,z4,z5,z6]),(0,[z0,z175,z2,z3,z22,z4,z5])],[(0,[z0,z28,z2,z3,z4,z8,z6]),(0,[z180,z0,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z20,z20,z6]),(0,[z0,z2,z3,z4,z5,z6,z221]),(0,[z0,z222,z2,z3,z4,z5,z6]),(0,[z0,z123,z2,z3,z4,z5,z85])],[(0,[z223,z0,z2,z3,z4,z5,z6]),(0,[z57,z0,z2,z3,z4,z126,z6]),(0,[z0,z224,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z208,z6]),(0,[z0,z2,z3,z22,z4,z20,z6]),(0,[z41,z0,z175,z2,z3,z4,z6])],[(1,[z0,z2,z3,z225,z5,z6]),(0,[z0,z11,z2,z3,z4,z5,z185]),(0,[z0,z226,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z227,z6]),(0,[z0,z228,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z199,z6]),(0,[z57,z0,z137,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z229]),(0,[z0,z2,z3,z4,z5,z6,z230])],[(0,[z0,z2,z231,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z232]),(0,[z0,z123,z2,z3,z4,z5,z146]),(0,[z0,z11,z13,z2,z3,z4,z5]),(0,[z233,z0,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z17,z5,z6])]],
   [[(0,[z0,z2,z234,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z235,z6]),(0,[z0,z52,z2,z3,z16,z4,z6]),(0,[z0,z2,z236,z3,z4,z5,z6])],[(0,[z237,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z238,z5,z6]),(0,[z75,z0,z2,z3,z4,z174,z6]),(0,[z0,z2,z29,z3,z4,z8,z6]),(0,[z211,z214,z2,z3,z4,z5,z6]),(0,[z0,z239,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z24]),(0,[z240,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z152,z3,z4,z114,z6])],[(0,[z0,z2,z3,z4,z115,z5,z6]),(0,[z0,z2,z3,z4,z5,z241,z6]),(0,[z0,z2,z3,z4,z5,z242,z6]),(0,[z0,z243,z2,z3,z4,z5,z6])],[(0,[z0,z244,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z245,z6]),(0,[z0,z30,z2,z42,z4,z5,z6]),(0,[z246,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z247]),(0,[z0,z2,z3,z4,z248,z5,z6]),(0,[z0,z2,z3,z4,z249,z5,z6])],[(0,[z0,z2,z3,z18,z193,z5,z6]),(0,[z0,z28,z3,z21,z4,z5,z6]),(0,[z0,z30,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z250]),(0,[z0,z251,z2,z3,z4,z5,z6]),(0,[z0,z2,z43,z3,z138,z5,z6]),(0,[z0,z2,z3,z4,z252,z5,z6]),(0,[z253,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z254,z5,z6])],[(0,[z0,z2,z3,z4,z5,z255,z6]),(0,[z0,z2,z3,z4,z5,z6,z256]),(0,[z211,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z98,z3,z4,z8,z6]),(0,[z0,z2,z3,z138,z4,z20,z6]),(0,[z0,z2,z3,z4,z118,z5,z6]),(0,[z0,z257,z2,z3,z4,z5,z6])],[(0,[z0,z2,z258,z3,z4,z5,z6]),(0,[z0,z2,z42,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z20,z6,z85]),(1,[z0,z23,z3,z83,z5,z6]),(0,[z0,z259,z2,z3,z4,z5,z6]),(0,[z215,z0,z2,z3,z22,z4,z5])],[(0,[z0,z2,z3,z260,z4,z5,z6]),(0,[z47,z0,z2,z3,z4,z261,z6]),(0,[z0,z2,z262,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z83,z4,z5]),(0,[z0,z2,z3,z4,z5,z263,z6])]],
   [[(1,[z2,z3,z4,z19,z8,z6]),(0,[z0,z2,z3,z4,z8,z151,z6]),(0,[z0,z2,z3,z4,z20,z6,z209]),(0,[z0,z28,z2,z3,z22,z4,z5]),(0,[z0,z264,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z29,z3,z4,z5])],[(0,[z107,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z265,z5,z6]),(1,[z0,z123,z3,z4,z5,z12]),(0,[z0,z2,z60,z3,z4,z5,z266]),(0,[z0,z181,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z267]),(0,[z0,z268,z2,z3,z4,z5,z6])],[(0,[z269,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z60,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z270,z6]),(0,[z0,z2,z3,z4,z5,z271,z6]),(0,[z163,z0,z11,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z272,z6]),(0,[z0,z2,z3,z4,z5,z6,z273]),(0,[z0,z11,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z274,z4,z5,z6]),(0,[z0,z2,z43,z4,z5,z6,z85]),(0,[z0,z275,z2,z3,z4,z5,z6]),(0,[z0,z276,z2,z3,z4,z5,z6])],[(0,[z0,z2,z76,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z20,z277,z6]),(0,[z0,z2,z3,z4,z20,z25,z6]),(0,[z41,z0,z52,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z278]),(0,[z0,z2,z138,z4,z14,z5,z6]),(0,[z0,z2,z60,z4,z5,z190,z6]),(0,[z279,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z280,z6]),(0,[z0,z2,z21,z4,z14,z5,z6]),(0,[z0,z2,z144,z3,z4,z5,z6]),(0,[z0,z13,z2,z43,z4,z5,z6]),(0,[z0,z2,z3,z4,z281,z5,z6]),(0,[z0,z2,z3,z22,z4,z5,z209]),(0,[z0,z2,z3,z282,z4,z5,z6])],[(0,[z107,z0,z2,z74,z4,z5,z6]),(0,[z0,z2,z31,z3,z4,z20,z6]),(0,[z40,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z3,z4,z283,z8,z6]),(0,[z0,z2,z3,z4,z20,z146,z6]),(1,[z0,z2,z284,z4,z5,z6]),(0,[z285,z0,z2,z284,z4,z5,z6]),(0,[z0,z2,z60,z3,z4,z118,z6]),(0,[z0,z2,z3,z4,z286,z5,z6])],[(0,[z57,z0,z2,z3,z4,z5,z207]),(0,[z0,z2,z42,z76,z4,z5,z6]),(0,[z47,z0,z2,z3,z4,z20,z6]),(0,[z47,z0,z11,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z287,z5,z6]),(0,[z0,z2,z3,z288,z4,z5,z6]),(0,[z0,z2,z3,z289,z22,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z5,z290,z6]),(0,[z285,z0,z23,z3,z4,z5,z6]),(1,[z0,z175,z2,z4,z118,z6]),(0,[z41,z0,z11,z2,z3,z4,z5])],[(0,[z40,z0,z2,z3,z18,z5,z6]),(0,[z0,z2,z3,z4,z5,z146,z185]),(0,[z0,z291,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z17,z5,z6]),(0,[z0,z2,z3,z4,z5,z292,z6]),(1,[z0,z2,z3,z4,z5,z293])],[(0,[z294,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z295,z4,z8,z6]),(0,[z211,z0,z2,z3,z22,z4,z5]),(0,[z196,z0,z11,z2,z3,z4,z5]),(0,[z0,z11,z2,z152,z3,z4,z5])],[(0,[z296,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z42,z3,z22,z4,z5]),(0,[z215,z0,z2,z3,z4,z5,z85]),(0,[z0,z2,z3,z4,z5,z297,z6]),(1,[z0,z2,z3,z4,z5,z266]),(0,[z0,z11,z2,z3,z4,z5,z81]),(0,[z0,z2,z298,z3,z4,z5,z6]),(0,[z0,z2,z3,z299,z4,z5,z6])],[(0,[z203,z0,z2,z3,z4,z20,z6]),(0,[z203,z0,z11,z2,z3,z4,z5]),(1,[z0,z2,z3,z4,z8,z6]),(0,[z285,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z67,z59]),(0,[z0,z2,z3,z4,z193,z5,z6]),(0,[z0,z300,z2,z3,z4,z5,z6]),(0,[z0,z2,z301,z3,z4,z5,z6]),(1,[z41,z0,z2,z3,z81,z6])],[(0,[z0,z2,z3,z18,z5,z71,z6]),(1,[z0,z2,z3,z4,z302,z6]),(0,[z303,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z304,z3,z4,z5,z6]),(0,[z0,z305,z2,z3,z4,z5,z6])],[(0,[z107,z0,z2,z3,z22,z4,z5]),(0,[z0,z11,z2,z3,z32,z4,z5]),(0,[z306,z0,z2,z3,z4,z5,z6]),(0,[z41,z0,z2,z3,z5,z81,z6])],[(1,[z0,z2,z307,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z108,z12]),(0,[z215,z0,z2,z3,z4,z5,z146]),(0,[z0,z2,z60,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z5,z308,z6]),(1,[z41,z0,z11,z2,z3,z5])]],
   [[(0,[z214,z0,z2,z3,z4,z20,z6]),(0,[z214,z0,z11,z2,z3,z4,z5]),(0,[z0,z175,z2,z3,z4,z190,z6]),(0,[z0,z11,z2,z3,z22,z4,z5])],[(1,[z0,z2,z74,z4,z5,z6]),(0,[z0,z2,z3,z138,z19,z5,z6]),(0,[z0,z2,z3,z4,z100,z8,z6])],[(0,[z0,z309,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z310,z6])],[(0,[z0,z311,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z19,z5,z71,z6]),(0,[z40,z0,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z22,z4,z5,z59]),(0,[z0,z3,z83,z4,z193,z5,z6]),(0,[z0,z222,z11,z2,z3,z4,z5])],[(1,[z0,z2,z3,z142,z4,z5]),(0,[z0,z2,z312,z3,z4,z5,z6]),(0,[z313,z0,z2,z3,z4,z5,z6])],[(0,[z314,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z162,z6]),(0,[z0,z315,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z14,z5,z6,z85])],[(0,[z316,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z6,z229]),(0,[z0,z2,z3,z4,z114,z20,z6]),(0,[z0,z2,z3,z4,z317,z5,z6]),(0,[z0,z2,z3,z5,z6,z184,z209])],[(0,[z0,z2,z3,z4,z20,z318,z6]),(0,[z0,z319,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z320,z5,z6]),(0,[z0,z2,z321,z3,z4,z5,z6]),(0,[z233,z0,z11,z2,z3,z4,z5])]],
   [[(0,[z0,z31,z3,z21,z4,z5,z6]),(0,[z47,z40,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z12])],[(0,[z203,z0,z31,z3,z4,z5,z6]),(0,[z214,z0,z2,z3,z4,z143,z6]),(0,[z0,z2,z3,z4,z5,z322,z6]),(0,[z0,z2,z3,z4,z323,z5,z6]),(0,[z0,z2,z3,z324,z4,z5,z6]),(0,[z0,z2,z3,z4,z325,z5,z6]),(0,[z285,z0,z2,z3,z22,z4,z5]),(0,[z0,z326,z2,z3,z4,z5,z6]),(0,[z240,z0,z11,z2,z3,z4,z5]),(1,[z0,z2,z3,z22,z4,z5])],[(0,[z0,z2,z3,z4,z5,z327,z6]),(0,[z0,z2,z3,z21,z4,z5,z6]),(0,[z0,z2,z3,z328,z4,z5,z6]),(0,[z0,z2,z329,z3,z4,z5,z6])],[(0,[z330,z0,z2,z3,z4,z5,z6]),(0,[z47,z0,z2,z3,z19,z5,z6]),(0,[z0,z2,z331,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z332]),(0,[z0,z2,z29,z3,z4,z5,z6])],[(0,[z0,z2,z3,z32,z4,z5,z6]),(0,[z0,z123,z2,z3,z4,z8,z6]),(0,[z0,z333,z2,z3,z4,z5,z6]),(0,[z0,z42,z3,z21,z4,z5,z6]),(0,[z0,z2,z3,z334,z4,z5,z6]),(0,[z0,z2,z3,z335,z22,z4,z5])],[(1,[z0,z2,z3,z4,z336,z6]),(0,[z0,z2,z3,z4,z336,z5,z6]),(0,[z0,z2,z3,z4,z8,z255,z6]),(0,[z0,z2,z3,z4,z337,z5,z6]),(0,[z0,z2,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z5,z338,z6])],[(0,[z0,z2,z3,z4,z5,z261,z6]),(0,[z0,z2,z3,z22,z4,z19,z5]),(0,[z0,z2,z3,z339,z4,z5,z6]),(0,[z340,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z341,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z342]),(0,[z0,z2,z3,z4,z343,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z344])],[(0,[z0,z2,z3,z19,z14,z5,z6]),(0,[z0,z2,z3,z4,z345,z5,z6]),(0,[z0,z2,z3,z4,z5,z346,z6]),(0,[z0,z347,z2,z3,z4,z5,z6]),(0,[z348,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z29,z3,z4,z5,z67])]],
   [[(0,[z75,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z349,z5,z6]),(0,[z0,z2,z3,z4,z350,z5,z6])],[(0,[z0,z77,z2,z3,z4,z5,z6]),(0,[z180,z2,z3,z4,z20,z5,z6]),(0,[z0,z2,z3,z4,z265,z20,z6]),(0,[z0,z351,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z352]),(0,[z0,z2,z3,z353,z4,z5,z6]),(1,[z0,z2,z144,z4,z5,z6]),(0,[z0,z2,z3,z17,z5,z81,z6])],[(0,[z0,z2,z354,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z355]),(0,[z0,z2,z356,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z266,z6]),(0,[z0,z2,z3,z4,z114,z5,z108])],[(0,[z107,z203,z2,z3,z4,z5,z6]),(0,[z0,z23,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z272,z6]),(0,[z0,z2,z3,z4,z357,z5,z6]),(0,[z0,z2,z43,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z358]),(0,[z0,z359,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z360,z5,z6])],[(0,[z0,z2,z76,z3,z4,z20,z6]),(0,[z0,z2,z3,z361,z4,z5,z6]),(0,[z0,z2,z3,z362,z4,z5,z6]),(0,[z0,z363,z2,z3,z4,z5,z6]),(0,[z0,z2,z307,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z118,z5]),(0,[z0,z11,z2,z3,z4,z17,z5]),(0,[z0,z2,z3,z17,z5,z71,z6])],[(0,[z57,z0,z2,z3,z4,z8,z6]),(1,[z2,z3,z4,z20,z8,z6]),(0,[z0,z2,z3,z4,z5,z85,z209])],[(1,[z0,z2,z3,z204,z5,z6]),(0,[z72,z0,z2,z3,z4,z5,z6]),(1,[z211,z2,z3,z4,z5,z185]),(0,[z0,z157,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z364,z5,z6])],[(0,[z0,z2,z3,z18,z4,z5,z6]),(0,[z0,z2,z365,z3,z4,z5,z6]),(0,[z34,z0,z2,z3,z4,z20,z6]),(0,[z366,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z22,z4,z20]),(0,[z0,z2,z3,z4,z5,z367,z6]),(0,[z0,z2,z3,z4,z114,z5,z209])]],
   [[(0,[z0,z2,z3,z4,z368,z5,z6]),(1,[z0,z2,z3,z4,z369,z6]),(0,[z0,z2,z3,z142,z4,z19,z5]),(0,[z0,z2,z3,z4,z283,z5,z6]),(0,[z0,z2,z3,z4,z5,z82,z6]),(0,[z0,z2,z3,z4,z5,z108,z85])],[(0,[z370,z0,z2,z3,z4,z5,z6]),(0,[z0,z371,z2,z3,z4,z5,z6]),(0,[z0,z123,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z14,z5,z6]),(0,[z0,z372,z2,z3,z4,z5,z6]),(0,[z134,z0,z2,z3,z4,z5,z6])],[(0,[z0,z373,z2,z3,z4,z5,z6]),(0,[z0,z2,z42,z3,z4,z5,z53]),(0,[z0,z2,z3,z4,z374,z5,z6]),(1,[z0,z11,z2,z26,z4,z5])],[(0,[z0,z2,z3,z4,z5,z375,z6]),(0,[z0,z2,z3,z4,z20,z8,z6]),(0,[z65,z0,z2,z4,z14,z5,z6]),(1,[z0,z2,z133,z3,z4,z6])],[(0,[z0,z2,z3,z295,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z108,z146]),(0,[z0,z175,z2,z3,z4,z118,z6]),(0,[z0,z2,z3,z4,z5,z80,z6]),(0,[z0,z11,z2,z3,z22,z5,z6])],[(0,[z0,z2,z376,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z126,z6]),(0,[z75,z0,z2,z3,z22,z4,z5]),(0,[z47,z0,z2,z3,z4,z377,z6]),(0,[z0,z2,z3,z4,z5,z378,z6]),(0,[z0,z2,z379,z3,z4,z5,z6]),(0,[z0,z2,z60,z3,z4,z190,z6])],[(1,[z0,z2,z3,z150,z5,z6]),(1,[z203,z69,z3,z4,z5,z6]),(0,[z0,z11,z69,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z380,z6]),(0,[z0,z52,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z22,z4,z5,z25]),(0,[z0,z52,z3,z4,z100,z5,z6]),(0,[z41,z0,z2,z3,z16,z5,z6])],[(1,[z75,z2,z76,z4,z5,z6]),(0,[z381,z0,z2,z3,z4,z5,z6]),(0,[z214,z0,z2,z3,z4,z5,z59]),(0,[z0,z2,z3,z4,z382,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z159])]],
   [[(0,[z0,z23,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z383,z4,z5,z6]),(0,[z0,z2,z384,z3,z4,z5,z6])],[(0,[z385,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z386,z6]),(0,[z0,z2,z3,z387,z4,z5,z6]),(0,[z0,z388,z2,z3,z4,z8,z6]),(0,[z0,z2,z42,z4,z118,z5,z6]),(0,[z0,z2,z60,z3,z16,z4,z6]),(0,[z0,z2,z3,z389,z4,z5,z6]),(0,[z65,z0,z2,z3,z4,z5,z6]),(1,[z0,z11,z2,z298,z4,z5])],[(0,[z107,z0,z2,z3,z4,z5,z390]),(0,[z391,z0,z2,z3,z4,z5,z6]),(0,[z57,z0,z2,z3,z22,z4,z5]),(0,[z0,z2,z392,z3,z4,z5,z6]),(0,[z0,z30,z2,z3,z4,z8,z6]),(1,[z0,z2,z98,z4,z8,z6]),(0,[z0,z2,z3,z4,z393,z5,z6]),(0,[z0,z309,z11,z2,z3,z4,z5])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z0,z69,z2,z3,z4,z5,z6]),(1,[z47,z2,z3,z19,z5,z6]),(0,[z394,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z395,z5,z6]),(0,[z396,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z100,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z209])],[(0,[z0,z397,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z398,z5,z6]),(0,[z0,z2,z3,z4,z5,z399,z6]),(0,[z0,z11,z2,z3,z4,z5,z95])],[(0,[z107,z0,z2,z3,z4,z103,z6]),(0,[z0,z400,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z401,z6]),(0,[z0,z2,z3,z4,z5,z402,z6]),(0,[z0,z2,z42,z3,z4,z5,z403]),(0,[z65,z0,z2,z3,z4,z5,z67]),(0,[z0,z11,z2,z206,z3,z4,z5])],[(0,[z57,z0,z2,z3,z4,z336,z6]),(0,[z0,z2,z404,z3,z4,z5,z6]),(0,[z0,z2,z307,z3,z4,z193,z5]),(0,[z316,z0,z11,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z405,z6])],[(0,[z0,z2,z3,z406,z4,z5,z6]),(0,[z0,z2,z407,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z174,z6]),(0,[z0,z2,z408,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z277,z6]),(0,[z211,z2,z3,z4,z5,z185,z6]),(0,[z409,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z8,z6,z12]),(0,[z0,z2,z410,z3,z4,z5,z6])],[(0,[z0,z2,z3,z411,z4,z5,z6]),(0,[z0,z2,z3,z4,z412,z5,z6]),(0,[z0,z11,z2,z3,z4,z114,z5])],[(1,[z0,z11,z2,z3,z19,z5]),(0,[z0,z2,z3,z4,z8,z327,z6]),(0,[z0,z2,z3,z21,z4,z20,z6]),(0,[z0,z2,z3,z225,z4,z5,z6]),(0,[z0,z2,z413,z3,z4,z5,z6]),(0,[z0,z2,z414,z3,z4,z5,z6])],[(0,[z0,z415,z2,z3,z4,z5,z6]),(0,[z416,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z22,z4,z417,z5])],[(0,[z0,z2,z3,z4,z5,z6,z207]),(0,[z0,z2,z3,z32,z4,z20,z6]),(0,[z0,z2,z3,z418,z4,z5,z6]),(0,[z75,z0,z2,z3,z4,z369,z6]),(0,[z0,z2,z3,z419,z4,z5,z6]),(0,[z0,z2,z420,z3,z4,z5,z6]),(0,[z0,z2,z149,z3,z4,z5,z6]),(0,[z0,z2,z60,z3,z4,z5,z112]),(0,[z0,z2,z3,z4,z5,z67,z108])],[(1,[z0,z2,z3,z4,z5,z390]),(1,[z0,z2,z3,z4,z421,z6]),(0,[z0,z11,z2,z76,z3,z4,z5]),(0,[z0,z422,z2,z3,z4,z5,z6]),(0,[z0,z13,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z71,z6])],[(0,[z423,z0,z2,z3,z4,z5,z6]),(0,[z424,z0,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z26,z4,z5,z6]),(0,[z425,z0,z2,z3,z22,z4,z5])],[(0,[z57,z0,z2,z3,z204,z5,z6]),(0,[z180,z2,z3,z4,z19,z5,z6]),(0,[z41,z0,z157,z2,z3,z4,z6]),(0,[z0,z175,z2,z60,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z55,z6]),(0,[z0,z2,z3,z4,z20,z108,z6]),(0,[z0,z2,z3,z4,z5,z426,z6]),(0,[z0,z427,z2,z3,z4,z5,z6]),(0,[z396,z0,z2,z3,z22,z4,z5])],[(0,[z0,z2,z3,z4,z20,z6,z428]),(0,[z0,z2,z3,z4,z5,z6,z59]),(0,[z0,z2,z3,z4,z5,z429,z6]),(0,[z0,z2,z3,z4,z430,z5,z6]),(0,[z0,z2,z3,z4,z5,z67,z209])],[(0,[z0,z2,z3,z138,z22,z4,z5]),(0,[z0,z2,z3,z4,z431,z5,z6])],[(0,[z0,z2,z3,z4,z5,z64,z6]),(0,[z0,z2,z432,z3,z4,z5,z6]),(0,[z433,z0,z2,z3,z4,z5,z6]),(0,[z0,z28,z2,z21,z4,z5,z6]),(0,[z434,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z403]),(0,[z0,z435,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z436,z4,z5,z6]),(0,[z0,z2,z3,z22,z4,z5,z108])],[(0,[z437,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z185,z85]),(0,[z438,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z439,z5,z6]),(0,[z440,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z19,z193,z5,z6]),(0,[z40,z0,z2,z3,z4,z441,z6]),(0,[z0,z2,z3,z4,z5,z442,z6]),(0,[z0,z11,z2,z3,z4,z5,z8]),(1,[z0,z2,z3,z4,z5,z443]),(0,[z0,z2,z3,z4,z5,z444,z6]),(0,[z0,z2,z3,z4,z445,z5,z6]),(0,[z0,z2,z446,z3,z4,z5,z6]),(0,[z0,z2,z152,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z447,z6])],[(1,[z57,z2,z32,z4,z5,z6]),(0,[z285,z0,z2,z3,z193,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z448]),(0,[z0,z2,z3,z22,z4,z5,z85])],[(0,[z0,z2,z449,z3,z4,z5,z6]),(0,[z0,z2,z197,z3,z4,z5,z6]),(1,[z0,z2,z26,z4,z5,z6]),(0,[z0,z2,z450,z3,z22,z4,z5])]],
   [[(1,[z0,z2,z3,z451,z5,z6]),(1,[z0,z2,z4,z283,z8,z6]),(0,[z452,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z453,z4,z5,z6]),(0,[z454,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z455,z4,z5,z6])],[(0,[z0,z2,z3,z4,z19,z8,z6]),(0,[z0,z456,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z18,z5,z6]),(0,[z0,z2,z3,z4,z14,z20,z6]),(0,[z214,z0,z2,z3,z4,z302,z6]),(0,[z0,z457,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z17,z5,z458])],[(0,[z0,z459,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z318,z6]),(1,[z0,z2,z87,z4,z5,z6]),(0,[z285,z0,z2,z87,z4,z5,z6]),(0,[z285,z0,z3,z4,z193,z5,z6]),(0,[z0,z2,z3,z4,z5,z460,z6]),(0,[z0,z2,z3,z4,z461,z5,z6]),(0,[z0,z2,z3,z22,z4,z5,z146]),(0,[z0,z462,z2,z3,z4,z5,z6]),(0,[z0,z13,z2,z3,z22,z4,z5]),(0,[z0,z175,z2,z3,z4,z5,z6]),(0,[z463,z0,z2,z3,z22,z4,z5])],[(0,[z0,z2,z31,z3,z22,z4,z5]),(1,[z0,z2,z3,z4,z441,z6]),(0,[z180,z0,z2,z3,z4,z5,z6]),(0,[z41,z0,z2,z3,z4,z20,z6]),(0,[z464,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z241]),(0,[z465,z0,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z60,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z6,z466]),(0,[z0,z2,z3,z4,z5,z467,z6]),(0,[z0,z11,z2,z3,z4,z4,z5])],[(0,[z0,z2,z468,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z469]),(0,[z0,z2,z3,z22,z4,z470,z5])],[(0,[z471,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z472,z6]),(0,[z0,z473,z2,z3,z4,z5,z6]),(0,[z0,z2,z474,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z114,z8,z6]),(0,[z0,z52,z2,z3,z4,z20,z6]),(0,[z0,z11,z175,z2,z3,z4,z5])],[(0,[z107,z2,z31,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z475,z6]),(0,[z0,z2,z3,z4,z5,z6,z476]),(0,[z0,z2,z3,z4,z477,z5,z6]),(0,[z0,z11,z2,z3,z16,z4,z5])]],
   [[(0,[z0,z2,z42,z32,z4,z5,z6]),(1,[z0,z157,z3,z4,z25,z6]),(0,[z0,z2,z3,z4,z417,z5,z6])],[(1,[z0,z11,z2,z3,z4,z8]),(0,[z65,z0,z2,z3,z4,z20,z6]),(0,[z0,z13,z2,z3,z14,z5,z6]),(0,[z65,z0,z11,z2,z3,z4,z5])],[(0,[z40,z2,z3,z4,z5,z8,z6]),(0,[z0,z2,z3,z16,z4,z20,z6]),(0,[z0,z11,z28,z2,z3,z4,z5]),(0,[z0,z2,z60,z21,z4,z5,z6])],[(0,[z0,z69,z2,z3,z4,z20,z6]),(0,[z0,z388,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z283,z5,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z209]),(0,[z0,z2,z3,z478,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z479,z6]),(0,[z41,z134,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z22,z140,z4,z5])],[(0,[z0,z30,z69,z3,z4,z5,z6]),(0,[z0,z30,z2,z3,z4,z5,z6]),(0,[z480,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z481,z6])],[(0,[z0,z0,z2,z3,z4,z8,z6]),(0,[z214,z0,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z482,z5,z6]),(1,[z0,z2,z43,z138,z5,z6])],[(0,[z483,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z22,z18,z4,z5]),(0,[z0,z2,z3,z4,z20,z190,z6]),(0,[z484,z0,z2,z3,z4,z5,z6]),(0,[z0,z11,z157,z2,z3,z4,z5]),(0,[z215,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z16,z17,z6])],[(0,[z485,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z486,z6]),(0,[z0,z175,z2,z3,z16,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z293])]],
   [[(0,[z0,z2,z3,z4,z20,z6,z95]),(0,[z0,z28,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z108,z6,z209])],[(0,[z0,z2,z3,z83,z4,z8,z6]),(0,[z0,z2,z43,z3,z4,z8,z6]),(0,[z211,z0,z2,z3,z4,z487,z6]),(0,[z488,z0,z2,z3,z4,z5,z6]),(1,[z0,z489,z2,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z67,z185]),(0,[z0,z2,z3,z4,z490,z5,z6]),(0,[z215,z0,z2,z3,z4,z5,z67]),(0,[z0,z2,z3,z4,z5,z6,z491])],[(0,[z0,z175,z2,z4,z118,z5,z6]),(0,[z0,z2,z3,z4,z5,z492,z6])],[(0,[z0,z2,z3,z4,z5,z493,z6]),(0,[z0,z2,z3,z83,z18,z5,z6]),(0,[z0,z157,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z20,z185,z6]),(0,[z0,z2,z494,z3,z4,z5,z6]),(0,[z215,z0,z3,z4,z5,z146,z6]),(0,[z0,z2,z3,z4,z5,z6,z495])],[(0,[z211,z0,z2,z3,z393,z5,z6]),(0,[z0,z2,z42,z4,z14,z5,z6]),(0,[z0,z23,z2,z3,z193,z5,z6]),(0,[z0,z2,z3,z496,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z81,z6]),(0,[z0,z2,z3,z4,z5,z497,z6]),(0,[z0,z2,z3,z22,z4,z5,z95])],[(0,[z498,z0,z2,z3,z4,z5,z6]),(0,[z0,z11,z52,z2,z3,z4,z5]),(0,[z499,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z17,z5,z293]),(0,[z0,z11,z2,z3,z4,z5,z202])],[(0,[z0,z2,z3,z451,z4,z5,z6]),(0,[z0,z2,z32,z21,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z302,z6]),(0,[z0,z2,z3,z4,z5,z6,z500]),(0,[z0,z2,z3,z289,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z118,z20,z6])],[(0,[z0,z2,z3,z4,z5,z501,z6]),(0,[z57,z0,z2,z3,z451,z5,z6]),(0,[z0,z2,z3,z4,z8,z6,z59]),(0,[z0,z2,z3,z22,z4,z5,z185]),(0,[z0,z2,z3,z4,z502,z193,z6]),(0,[z0,z52,z2,z3,z4,z100,z6]),(0,[z0,z2,z133,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z503,z6]),(0,[z0,z2,z3,z504,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z505,z6]),(0,[z40,z0,z2,z3,z4,z5,z380]),(0,[z0,z2,z98,z3,z4,z5,z6]),(0,[z211,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z506,z6]),(0,[z0,z11,z30,z2,z3,z4,z5]),(0,[z0,z2,z3,z22,z4,z114,z5]),(0,[z0,z507,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z508])],[(0,[z0,z2,z3,z4,z5,z509,z6]),(0,[z0,z2,z3,z4,z5,z59,z12]),(0,[z0,z2,z42,z3,z4,z5,z6]),(0,[z0,z52,z2,z353,z4,z5,z6]),(0,[z510,z0,z2,z3,z4,z5,z6]),(0,[z511,z0,z2,z3,z4,z5,z6]),(1,[z215,z0,z3,z4,z5,z146]),(0,[z512,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z114,z108,z6])],[(0,[z513,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z146,z6,z12]),(0,[z0,z2,z3,z4,z51,z5,z6]),(0,[z0,z2,z3,z514,z4,z5,z6])],[(0,[z203,z69,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z48,z5,z6]),(0,[z0,z2,z152,z3,z4,z20,z6]),(0,[z0,z11,z123,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z515,z6])],[(0,[z107,z0,z2,z3,z4,z5,z6]),(0,[z107,z0,z69,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z516,z5,z6]),(0,[z0,z2,z3,z4,z5,z517,z6]),(0,[z0,z2,z3,z518,z4,z5,z6]),(0,[z0,z123,z3,z4,z5,z6,z12]),(0,[z0,z2,z519,z3,z4,z5,z6])],[(0,[z0,z2,z3,z520,z4,z5,z6]),(0,[z0,z2,z521,z3,z4,z5,z6]),(0,[z0,z2,z522,z3,z4,z5,z6]),(0,[z285,z0,z2,z3,z83,z5,z6]),(0,[z0,z2,z60,z3,z4,z5,z6]),(0,[z0,z2,z3,z523,z4,z5,z6]),(0,[z41,z0,z11,z2,z3,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z524,z6]),(1,[z0,z2,z3,z4,z5,z380]),(1,[z0,z2,z3,z4,z487,z6]),(0,[z0,z2,z3,z4,z5,z525,z6]),(0,[z0,z11,z2,z3,z4,z5,z6])],[(0,[z526,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z527,z6]),(0,[z0,z2,z528,z3,z4,z5,z6]),(0,[z0,z456,z11,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z6,z529]),(0,[z0,z2,z3,z4,z5,z530,z6]),(0,[z0,z2,z3,z531,z4,z5,z6]),(0,[z0,z462,z11,z2,z3,z4,z5]),(1,[z0,z2,z152,z3,z4,z209])],[(0,[z40,z0,z2,z3,z4,z5,z6]),(0,[z180,z0,z2,z3,z4,z20,z6]),(0,[z180,z0,z11,z2,z3,z4,z5]),(0,[z0,z2,z3,z22,z83,z4,z5]),(0,[z532,z0,z2,z3,z4,z5,z6])],[(0,[z533,z0,z2,z3,z4,z5,z6]),(0,[z75,z0,z2,z76,z4,z5,z6]),(0,[z40,z0,z2,z3,z4,z5,z273]),(0,[z34,z0,z2,z3,z22,z4,z5]),(0,[z2,z3,z4,z20,z5,z8,z6]),(1,[z0,z2,z3,z393,z5,z6]),(0,[z0,z2,z3,z4,z502,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z534]),(0,[z0,z2,z43,z138,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z5,z67])],[(0,[z535,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z43,z3,z14,z5,z6])],[(0,[z0,z2,z3,z22,z4,z5,z8]),(0,[z0,z2,z536,z3,z4,z5,z6]),(0,[z537,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z538,z6])],[(0,[z0,z2,z3,z22,z4,z8,z6]),(0,[z0,z2,z3,z4,z193,z20,z6]),(0,[z0,z539,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z540,z4,z5,z6]),(0,[z0,z2,z3,z4,z541,z5,z6])]],
   [[(0,[z0,z2,z3,z150,z4,z5,z6]),(0,[z0,z2,z3,z4,z542,z5,z6]),(0,[z2,z3,z4,z19,z5,z8,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z57,z0,z2,z76,z4,z5,z6]),(0,[z543,z0,z2,z3,z4,z5,z6]),(0,[z285,z0,z2,z3,z4,z5,z6])],[(0,[z75,z0,z2,z32,z4,z5,z6]),(0,[z0,z2,z3,z4,z20,z17,z6]),(0,[z0,z2,z3,z4,z5,z544,z6]),(0,[z545,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z546,z4,z5,z6]),(0,[z0,z2,z152,z3,z4,z6,z209])],[(0,[z0,z2,z3,z4,z547,z5,z6]),(0,[z0,z116,z2,z3,z4,z8,z6]),(0,[z548,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z458,z6])],[(0,[z0,z2,z3,z4,z549,z5,z6]),(0,[z0,z2,z3,z550,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z428]),(0,[z0,z2,z551,z3,z4,z5,z6]),(0,[z0,z2,z3,z335,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z552,z6]),(0,[z0,z2,z3,z4,z5,z6,z85]),(1,[z201,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z553,z5,z6]),(0,[z0,z2,z3,z554,z4,z5,z6]),(0,[z0,z555,z2,z3,z4,z5,z6]),(0,[z203,z0,z2,z3,z4,z421,z6]),(0,[z0,z2,z3,z4,z5,z6,z556]),(0,[z0,z11,z2,z3,z4,z100,z5]),(0,[z0,z11,z2,z3,z4,z5,z190]),(0,[z0,z2,z3,z22,z4,z4,z5])],[(0,[z0,z2,z3,z557,z4,z5,z6]),(0,[z215,z0,z11,z2,z3,z4,z5]),(0,[z0,z2,z152,z3,z4,z5,z209])],[(0,[z57,z0,z2,z32,z4,z5,z6]),(0,[z214,z2,z3,z4,z5,z6,z59]),(0,[z0,z2,z3,z22,z4,z5,z81]),(0,[z0,z2,z3,z22,z5,z71,z6])]],
   [[(0,[z0,z2,z558,z3,z4,z5,z6]),(0,[z0,z2,z3,z138,z4,z8,z6]),(0,[z0,z28,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z22,z16,z4,z5]),(0,[z0,z2,z3,z4,z5,z559,z6])],[(0,[z0,z2,z3,z4,z5,z6,z560]),(0,[z0,z2,z3,z4,z369,z5,z6]),(1,[z0,z11,z2,z3,z5,z95])],[(0,[z107,z0,z2,z376,z4,z5,z6]),(0,[z561,z0,z2,z3,z4,z5,z6]),(0,[z75,z0,z2,z60,z4,z5,z6]),(0,[z0,z319,z2,z3,z4,z20,z6]),(0,[z0,z11,z2,z3,z4,z193,z5]),(0,[z0,z2,z3,z4,z5,z25,z6]),(0,[z0,z562,z2,z3,z4,z5,z6]),(0,[z0,z201,z2,z3,z4,z5,z6])],[(0,[z563,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z138,z18,z5,z6]),(1,[z0,z2,z3,z4,z5,z53]),(0,[z0,z564,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z565,z6]),(0,[z0,z2,z43,z3,z4,z5,z6])],[(0,[z0,z566,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z146,z6]),(0,[z0,z2,z3,z22,z22,z4,z5])],[(0,[z0,z2,z3,z4,z8,z81,z6]),(0,[z214,z0,z2,z3,z4,z5,z185])],[(0,[z0,z567,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z568]),(0,[z0,z2,z29,z3,z4,z20,z6]),(0,[z0,z2,z569,z3,z4,z5,z6]),(0,[z0,z23,z2,z3,z83,z5,z6]),(0,[z0,z157,z2,z3,z4,z5,z6]),(0,[z570,z0,z2,z3,z4,z5,z6])],[(0,[z57,z0,z2,z60,z4,z5,z6]),(0,[z2,z3,z4,z5,z185,z6,z59]),(0,[z0,z2,z3,z110,z22,z4,z5])]],
   [[(0,[z2,z76,z3,z32,z4,z5,z6]),(1,[z40,z2,z3,z4,z8,z6]),(0,[z0,z2,z4,z118,z5,z190,z6])],[(0,[z69,z2,z31,z3,z4,z5,z6]),(0,[z0,z2,z31,z3,z4,z8,z6]),(0,[z0,z2,z3,z284,z4,z5,z6]),(0,[z0,z123,z2,z3,z4,z5,z6])],[(0,[z571,z0,z2,z3,z4,z5,z6]),(0,[z47,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z572,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z573]),(0,[z211,z0,z2,z3,z4,z20,z6]),(0,[z211,z0,z11,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z574]),(0,[z0,z30,z2,z21,z4,z5,z6]),(0,[z0,z157,z3,z4,z5,z25,z6]),(0,[z0,z575,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z576,z6]),(0,[z0,z2,z3,z4,z5,z577,z6]),(0,[z41,z0,z2,z3,z4,z81,z6]),(0,[z578,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z103,z6]),(0,[z0,z2,z42,z3,z4,z20,z6]),(0,[z0,z579,z2,z3,z4,z5,z6]),(0,[z0,z2,z580,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z443,z6])],[(0,[z581,z0,z2,z3,z4,z8,z6]),(0,[z582,z0,z2,z3,z4,z5,z6]),(0,[z0,z30,z42,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z583,z6])],[(1,[z0,z2,z376,z4,z5,z6]),(0,[z0,z2,z3,z584,z4,z5,z6]),(0,[z75,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z585,z4,z5,z6]),(0,[z0,z123,z2,z3,z4,z5,z67]),(0,[z0,z11,z2,z3,z4,z360,z5])],[(0,[z107,z0,z2,z3,z4,z20,z6]),(0,[z107,z0,z11,z2,z3,z4,z5]),(0,[z586,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z587,z4,z5,z6]),(0,[z0,z11,z2,z298,z3,z4,z5])],[(0,[z203,z0,z2,z3,z4,z475,z6]),(0,[z203,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z60,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z5,z588,z6])]],
   [[(0,[z0,z11,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z589,z5,z6]),(0,[z0,z23,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z590,z6]),(0,[z0,z591,z2,z3,z4,z5,z6]),(0,[z0,z11,z11,z2,z3,z4,z5])],[(1,[z0,z2,z3,z4,z261,z6]),(0,[z0,z2,z3,z4,z5,z208,z6]),(0,[z592,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z593,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z112]),(0,[z0,z2,z3,z4,z5,z190,z6]),(0,[z0,z2,z3,z16,z4,z81,z6])],[(0,[z594,z0,z2,z3,z4,z5,z6]),(0,[z57,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z18,z4,z20,z6]),(1,[z214,z2,z3,z4,z5,z59]),(1,[z0,z564,z2,z3,z4,z6]),(0,[z0,z11,z2,z3,z138,z4,z5]),(0,[z0,z56,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z390]),(0,[z595,z0,z2,z3,z4,z5,z6]),(0,[z40,z0,z2,z3,z4,z20,z6]),(0,[z40,z0,z11,z2,z3,z4,z5]),(0,[z214,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z368,z20,z6]),(0,[z596,z0,z2,z3,z4,z5,z6]),(0,[z0,z157,z2,z3,z16,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z95]),(1,[z0,z2,z3,z22,z5,z71])],[(0,[z0,z2,z3,z4,z5,z597,z6]),(0,[z0,z2,z3,z4,z5,z598,z6]),(0,[z0,z2,z3,z4,z599,z5,z6]),(0,[z170,z0,z2,z3,z22,z4,z5])],[(0,[z600,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z601,z3,z4,z5,z6]),(0,[z215,z0,z123,z3,z4,z5,z6]),(0,[z602,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z29,z4,z5,z85]),(0,[z0,z2,z3,z4,z5,z6,z603])],[(0,[z0,z2,z3,z4,z5,z604,z6])],[(0,[z0,z2,z3,z4,z5,z421,z6]),(0,[z47,z0,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z5,z185,z6]),(0,[z0,z605,z2,z3,z4,z5,z6])]],
   [[(0,[z107,z0,z2,z3,z4,z5,z121]),(0,[z0,z2,z3,z4,z20,z5,z6]),(0,[z0,z2,z3,z22,z4,z118,z5]),(0,[z41,z0,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z22,z4,z17,z5]),(0,[z0,z2,z3,z4,z606,z5,z6])],[(0,[z607,z0,z2,z3,z4,z5,z6]),(0,[z285,z0,z2,z3,z4,z20,z6]),(0,[z285,z0,z11,z2,z3,z4,z5]),(0,[z0,z2,z608,z3,z4,z5,z6]),(0,[z0,z2,z149,z3,z4,z14,z5]),(1,[z0,z11,z2,z3,z4,z5]),(0,[z191,z0,z2,z3,z22,z4,z5])],[(0,[z0,z2,z3,z609,z4,z5,z6]),(0,[z0,z610,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z611,z4,z5,z6]),(0,[z0,z2,z43,z3,z4,z5,z443])],[(0,[z0,z612,z2,z3,z4,z5,z6])],[(0,[z203,z0,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z8,z6,z85]),(0,[z65,z0,z2,z43,z4,z5,z6]),(0,[z0,z613,z2,z3,z4,z5,z6])],[(0,[z614,z0,z2,z3,z4,z5,z6]),(0,[z0,z615,z2,z3,z4,z5,z6]),(0,[z0,z2,z616,z3,z4,z5,z6]),(0,[z0,z2,z617,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z618,z6])],[(0,[z75,z0,z2,z4,z118,z5,z6]),(0,[z0,z2,z3,z4,z100,z20,z6]),(0,[z0,z2,z3,z4,z5,z619,z6]),(0,[z425,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z620,z5,z6]),(0,[z621,z0,z2,z3,z4,z5,z6])],[(0,[z0,z622,z2,z3,z4,z5,z6]),(0,[z0,z623,z2,z3,z4,z5,z6]),(1,[z0,z2,z98,z4,z5,z6]),(0,[z0,z2,z3,z624,z4,z5,z6])]],
   [[(0,[z396,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z377,z5,z6]),(0,[z0,z2,z3,z4,z118,z8,z6]),(0,[z65,z0,z2,z29,z4,z5,z6]),(0,[z0,z11,z2,z298,z4,z5,z6])],[(0,[z0,z2,z625,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z626,z5,z6]),(0,[z0,z11,z2,z3,z4,z5,z209])],[(0,[z0,z2,z3,z4,z8,z25,z6]),(0,[z0,z2,z408,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z20,z67,z6]),(1,[z0,z2,z3,z4,z143,z6]),(0,[z0,z2,z3,z4,z5,z627,z6]),(0,[z0,z2,z3,z4,z5,z628,z6]),(0,[z0,z2,z3,z4,z5,z6,z629])],[(0,[z0,z2,z3,z4,z199,z5,z6]),(0,[z57,z0,z2,z4,z118,z5,z6]),(0,[z630,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z631]),(0,[z0,z157,z2,z3,z4,z5,z241]),(0,[z0,z2,z3,z4,z5,z6,z632])],[(0,[z0,z11,z2,z3,z19,z5,z6]),(0,[z0,z2,z3,z4,z8,z146,z6]),(0,[z0,z566,z2,z3,z4,z20,z6]),(0,[z0,z13,z2,z4,z14,z5,z6]),(0,[z0,z2,z3,z4,z51,z14,z6])],[(0,[z0,z633,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z634,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z635])],[(0,[z0,z2,z3,z4,z636,z5,z6]),(0,[z0,z2,z3,z4,z5,z637,z6]),(0,[z0,z2,z3,z22,z4,z5,z190]),(0,[z0,z2,z3,z22,z4,z5,z559])],[(0,[z0,z2,z137,z3,z4,z5,z6]),(0,[z0,z2,z76,z3,z4,z8,z6]),(0,[z40,z0,z2,z3,z19,z5,z6]),(0,[z0,z2,z3,z419,z4,z20,z6]),(1,[z0,z11,z2,z3,z4,z20]),(0,[z0,z2,z450,z3,z4,z5,z6])]],
   [[(0,[z638,z0,z2,z3,z4,z5,z6]),(0,[z639,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z8,z6]),(0,[z0,z123,z2,z3,z4,z20,z6]),(0,[z211,z0,z2,z3,z4,z5,z59]),(0,[z0,z640,z2,z3,z4,z5,z6]),(0,[z641,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z298,z4,z5,z6])],[(0,[z34,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z642,z4,z5,z6]),(0,[z643,z0,z2,z3,z4,z5,z6]),(0,[z0,z52,z2,z3,z4,z25,z6]),(0,[z0,z2,z3,z4,z644,z5,z6]),(0,[z0,z13,z2,z3,z4,z5,z6]),(0,[z463,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z31,z3,z4,z5,z6]),(0,[z211,z0,z2,z3,z225,z5,z6]),(0,[z0,z2,z3,z22,z4,z193,z5]),(0,[z645,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z29,z4,z5,z6,z85]),(0,[z65,z0,z2,z3,z4,z5,z85]),(1,[z0,z2,z197,z3,z4,z5]),(0,[z0,z646,z2,z3,z4,z5,z6])],[(0,[z107,z0,z2,z3,z553,z5,z6]),(0,[z57,z75,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z17,z8,z6]),(0,[z211,z0,z2,z3,z4,z280,z6]),(0,[z0,z2,z3,z647,z4,z5,z6])],[(0,[z0,z2,z3,z648,z4,z5,z6]),(0,[z75,z0,z11,z2,z3,z4,z5]),(0,[z0,z11,z2,z3,z4,z20,z5]),(0,[z0,z2,z649,z3,z4,z5,z6]),(0,[z0,z257,z2,z3,z22,z4,z5])],[(0,[z581,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z650,z5,z6]),(1,[z0,z2,z353,z4,z5,z6]),(0,[z0,z489,z2,z3,z5,z6,z209])],[(0,[z0,z11,z2,z3,z4,z5,z59]),(0,[z0,z2,z651,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z652,z5,z6]),(0,[z0,z2,z3,z653,z4,z5,z6])]],
   [[(0,[z0,z11,z2,z31,z3,z4,z5])],[(0,[z0,z2,z3,z4,z654,z5,z6]),(0,[z0,z2,z43,z21,z4,z5,z6]),(0,[z0,z2,z3,z4,z655,z5,z6]),(0,[z0,z2,z3,z4,z470,z5,z6])],[(0,[z57,z0,z11,z2,z3,z4,z5]),(0,[z0,z2,z3,z656,z4,z5,z6]),(0,[z0,z2,z449,z3,z4,z20,z6]),(0,[z0,z2,z3,z657,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z80]),(0,[z0,z2,z152,z3,z22,z4,z5]),(0,[z0,z489,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z8,z6,z95]),(0,[z658,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z24]),(0,[z0,z659,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z660,z4,z5,z6]),(0,[z0,z2,z661,z3,z4,z5,z6])],[(0,[z662,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z76,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z5,z663,z6]),(1,[z0,z11,z2,z3,z17,z5])],[(1,[z0,z2,z4,z283,z5,z6]),(0,[z0,z175,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z664,z5,z6]),(0,[z0,z2,z3,z4,z5,z146,z209]),(0,[z0,z2,z3,z4,z5,z6,z184])],[(0,[z0,z2,z3,z4,z19,z5,z6]),(0,[z0,z77,z2,z3,z4,z19,z5]),(0,[z0,z157,z52,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z250]),(0,[z0,z2,z3,z665,z4,z5,z6]),(0,[z0,z2,z666,z3,z4,z5,z6]),(0,[z0,z667,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z553,z5,z6]),(0,[z0,z2,z3,z4,z8,z185,z6]),(0,[z0,z2,z3,z4,z668,z5,z6]),(0,[z215,z0,z2,z3,z4,z5,z12]),(0,[z0,z2,z3,z4,z5,z6,z669]),(0,[z0,z2,z3,z288,z22,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z670])]],
   [[(0,[z671,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z672]),(0,[z0,z673,z2,z3,z4,z5,z6])],[(0,[z0,z674,z2,z3,z4,z5,z6]),(0,[z675,z0,z2,z3,z4,z5,z6]),(1,[z180,z2,z3,z4,z20,z6]),(0,[z0,z157,z2,z3,z4,z100,z6]),(0,[z0,z3,z4,z100,z5,z25,z6]),(0,[z0,z676,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z458])],[(1,[z0,z58,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z19,z5]),(0,[z0,z96,z2,z3,z4,z8,z6]),(0,[z0,z23,z2,z3,z4,z5,z631]),(0,[z677,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z496,z4,z14,z5])],[(1,[z0,z2,z3,z4,z5,z64]),(0,[z0,z2,z3,z4,z93,z5,z6]),(0,[z0,z2,z474,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z678,z5,z6]),(1,[z0,z2,z3,z4,z280,z6]),(0,[z0,z2,z3,z4,z679,z5,z6]),(0,[z0,z2,z3,z4,z5,z403,z6]),(0,[z0,z564,z2,z3,z4,z193,z6]),(0,[z0,z2,z3,z4,z680,z5,z6]),(0,[z0,z2,z3,z4,z681,z5,z6]),(0,[z0,z2,z3,z4,z114,z5,z6]),(0,[z0,z682,z2,z3,z4,z5,z6])],[(0,[z0,z683,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z684,z6]),(0,[z0,z2,z3,z4,z5,z685,z6]),(0,[z0,z2,z3,z4,z686,z5,z6]),(0,[z0,z2,z152,z3,z4,z5,z108])],[(0,[z0,z2,z3,z687,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z273]),(0,[z0,z2,z3,z21,z4,z8,z6]),(0,[z0,z615,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z44,z4,z193,z5]),(0,[z0,z2,z3,z4,z5,z6,z688]),(0,[z689,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z631,z6]),(1,[z0,z2,z3,z496,z4,z5]),(0,[z0,z2,z3,z4,z5,z108,z6])],[(0,[z0,z2,z3,z4,z5,z690,z6]),(0,[z0,z2,z3,z32,z4,z8,z6]),(1,[z0,z2,z3,z4,z377,z6]),(0,[z0,z30,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z22,z4,z606,z5]),(0,[z0,z2,z691,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z475,z5,z6]),(0,[z0,z692,z2,z3,z4,z5,z6]),(0,[z396,z0,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z487,z5,z6]),(0,[z0,z2,z3,z4,z693,z5,z6]),(0,[z0,z694,z2,z3,z4,z5,z6]),(0,[z396,z0,z11,z2,z3,z4,z5])],[(0,[z695,z0,z2,z3,z4,z5,z6]),(0,[z215,z0,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z5,z696,z6]),(0,[z0,z11,z2,z43,z3,z4,z5])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z345,z8,z6]),(0,[z485,z0,z2,z3,z4,z20,z6]),(0,[z0,z11,z2,z42,z3,z4,z5])],[(0,[z697,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z441,z5,z6]),(0,[z0,z2,z3,z4,z5,z146,z59]),(0,[z0,z30,z28,z3,z4,z5,z6]),(1,[z285,z0,z3,z193,z5,z6]),(0,[z0,z157,z2,z3,z4,z5,z250])],[(0,[z0,z2,z3,z4,z5,z698,z6]),(0,[z699,z0,z2,z3,z4,z5,z6]),(0,[z0,z28,z2,z42,z4,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z95])],[(0,[z700,z0,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z14,z5]),(0,[z0,z2,z701,z3,z4,z5,z6])],[(0,[z0,z2,z702,z3,z4,z5,z6]),(0,[z0,z2,z703,z3,z4,z5,z6]),(0,[z0,z2,z3,z83,z4,z5,z6]),(0,[z0,z2,z3,z4,z704,z5,z6]),(0,[z0,z705,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z5,z71]),(0,[z0,z2,z3,z4,z706,z5,z6])],[(0,[z180,z40,z2,z3,z4,z5,z6]),(1,[z0,z11,z2,z3,z18,z5]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z2,z3,z4,z5,z59,z85]),(1,[z0,z2,z3,z4,z502,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z313,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z707,z6]),(0,[z0,z2,z3,z4,z708,z6])],[(0,[z0,z2,z3,z4,z143,z6])],[(0,[z0,z2,z3,z4,z5,z121]),(0,[z0,z2,z3,z709,z5,z6]),(0,[z0,z2,z3,z710,z451,z5]),(0,[z0,z2,z3,z5,z711,z6]),(0,[z0,z2,z3,z4,z5,z631]),(0,[z0,z11,z2,z3,z5,z184])],[(0,[z0,z2,z3,z712,z204,z5]),(0,[z0,z2,z3,z19,z5,z380])],[(0,[z0,z23,z3,z22,z83,z5])],[(0,[z0,z713,z3,z4,z5,z6]),(0,[z203,z713,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z159]),(0,[z0,z714,z3,z4,z5,z6])],[(0,[z409,z2,z32,z4,z5,z6]),(0,[z2,z3,z142,z4,z19,z8]),(0,[z0,z11,z2,z3,z4,z20]),(0,[z0,z2,z149,z3,z4,z8]),(0,[z0,z2,z3,z4,z5,z715])],[(0,[z41,z0,z2,z144,z4,z6]),(0,[z0,z2,z379,z4,z5,z67]),(0,[z0,z716,z3,z4,z5,z6])],[(0,[z0,z2,z284,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z717]),(0,[z0,z2,z298,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z718]),(0,[z0,z2,z3,z22,z4,z441]),(0,[z0,z719,z2,z3,z4,z5]),(0,[z0,z2,z29,z26,z4,z5])],[(0,[z0,z2,z98,z4,z5,z720]),(0,[z0,z2,z3,z4,z20,z721]),(0,[z41,z0,z2,z3,z277,z6]),(0,[z0,z2,z3,z22,z4,z143]),(0,[z0,z2,z3,z22,z225,z5]),(0,[z0,z2,z197,z3,z4,z5])],[(0,[z0,z2,z4,z722,z8,z6]),(0,[z0,z2,z3,z4,z8,z293]),(0,[z0,z2,z3,z723,z5,z6]),(0,[z0,z2,z3,z5,z6,z184])],[(0,[z0,z11,z58,z3,z4,z5]),(0,[z0,z2,z724,z4,z5,z6]),(0,[z0,z2,z133,z42,z4,z6]),(0,[z0,z2,z298,z4,z5,z67])],[(0,[z0,z725,z3,z4,z5,z6]),(0,[z0,z2,z353,z4,z5,z6]),(0,[z0,z11,z726,z3,z4,z5])],[(0,[z0,z2,z3,z4,z727,z6])],[(1,[z713,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z728,z6]),(0,[z729,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z4,z118,z126,z6]),(0,[z0,z3,z4,z8,z6,z730]),(0,[z0,z2,z3,z4,z20,z112]),(0,[z217,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z225,z487,z6]),(0,[z0,z2,z3,z4,z5,z731])],[(0,[z0,z2,z3,z4,z5,z732]),(0,[z0,z2,z3,z4,z733,z6]),(0,[z315,z2,z3,z4,z8,z6]),(0,[z0,z2,z149,z3,z4,z20]),(0,[z0,z2,z3,z4,z734,z6]),(0,[z0,z2,z3,z4,z5,z80]),(0,[z0,z222,z181,z3,z4,z5])],[(0,[z57,z2,z32,z22,z4,z5]),(0,[z0,z2,z3,z22,z20,z71]),(0,[z41,z0,z2,z3,z734,z6]),(0,[z0,z2,z3,z16,z17,z293])],[(0,[z0,z2,z74,z4,z8,z6]),(0,[z0,z735,z2,z3,z4,z5]),(0,[z0,z2,z3,z22,z4,z208]),(0,[z0,z566,z2,z4,z93,z6]),(0,[z0,z2,z3,z4,z736,z6]),(0,[z0,z2,z737,z4,z5,z6]),(0,[z0,z2,z26,z22,z4,z5])],[(0,[z0,z2,z738,z4,z5,z6]),(0,[z0,z739,z2,z3,z4,z5]),(0,[z0,z11,z2,z3,z4,z336]),(0,[z109,z2,z3,z4,z20,z6]),(0,[z214,z56,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z740,z6])],[(0,[z0,z11,z2,z298,z4,z8]),(0,[z0,z2,z3,z4,z20,z741]),(0,[z0,z2,z3,z742,z5,z6])],[(0,[z0,z2,z3,z553,z5,z6]),(0,[z0,z2,z3,z4,z743,z6]),(0,[z57,z2,z32,z4,z336,z6]),(0,[z11,z56,z2,z3,z18,z5]),(0,[z0,z11,z2,z3,z22,z8]),(0,[z0,z11,z2,z744,z4,z5])],[(0,[z0,z2,z3,z4,z6,z745]),(0,[z0,z2,z4,z746,z190,z6]),(0,[z0,z747,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z748,z6]),(0,[z180,z2,z3,z4,z20,z6]),(0,[z316,z56,z2,z3,z4,z5]),(0,[z0,z2,z3,z22,z4,z749])],[(0,[z0,z58,z3,z4,z5,z6]),(0,[z107,z31,z3,z4,z103,z6]),(0,[z0,z2,z3,z225,z5,z6])],[(0,[z0,z2,z3,z750,z5,z6]),(0,[z0,z2,z3,z4,z5,z64]),(0,[z0,z2,z3,z5,z751,z95])],[(0,[z107,z31,z376,z4,z5,z6]),(0,[z0,z2,z3,z752,z4,z5])],[(0,[z0,z319,z3,z4,z100,z6])],[(0,[z285,z0,z11,z3,z193,z5])],[(0,[z0,z2,z3,z150,z5,z390]),(0,[z0,z11,z2,z3,z572,z5])],[(0,[z0,z2,z3,z4,z753,z6]),(0,[z0,z2,z3,z22,z5,z308])]],
   [[(0,[z41,z134,z2,z3,z81,z6]),(0,[z425,z0,z11,z2,z3,z5]),(0,[z0,z11,z2,z754,z4,z5]),(0,[z0,z11,z2,z666,z3,z5])],[(0,[z0,z2,z3,z4,z755,z6]),(0,[z0,z11,z2,z3,z22,z20]),(0,[z0,z2,z756,z3,z4,z5])],[(0,[z0,z2,z3,z757,z4,z5])],[(0,[z0,z2,z3,z4,z5,z758]),(0,[z215,z0,z3,z4,z5,z759])],[(0,[z0,z2,z3,z760,z4,z5]),(0,[z41,z0,z2,z197,z3,z5])],[(0,[z0,z761,z2,z3,z4,z5]),(0,[z0,z2,z60,z4,z190,z112])],[(0,[z0,z762,z2,z3,z4,z5]),(0,[z0,z11,z2,z3,z18,z5])],[(0,[z0,z763,z3,z4,z5,z6]),(0,[z2,z3,z19,z82,z8,z6]),(0,[z0,z764,z3,z4,z8,z6]),(0,[z0,z2,z149,z3,z4,z51]),(0,[z0,z309,z2,z3,z4,z360]),(0,[z0,z2,z3,z22,z4,z765])],[(0,[z0,z2,z3,z4,z766,z6]),(0,[z0,z2,z3,z4,z767,z6]),(0,[z0,z2,z3,z768,z4,z5]),(0,[z0,z157,z3,z22,z4,z25]),(0,[z0,z11,z2,z3,z5,z460]),(0,[z0,z2,z3,z734,z81,z6])],[(0,[z203,z11,z69,z3,z4,z5]),(0,[z0,z2,z769,z4,z8,z6]),(0,[z2,z3,z4,z770,z5,z6]),(0,[z0,z2,z87,z4,z5,z771]),(0,[z0,z11,z2,z3,z220,z5])],[(0,[z0,z772,z2,z3,z5,z6])],[(0,[z0,z773,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z142,z5]),(0,[z0,z2,z3,z8,z6,z184])],[(0,[z0,z2,z3,z4,z5,z774]),(1,[z0,z2,z775,z5,z6])],[(0,[z581,z0,z11,z2,z3,z8]),(0,[z0,z52,z353,z4,z100,z6]),(0,[z0,z2,z133,z3,z496,z4]),(0,[z0,z2,z3,z4,z5,z293])],[(0,[z0,z2,z3,z776,z5,z6]),(0,[z40,z2,z3,z18,z5,z273]),(0,[z0,z777,z3,z4,z8,z6]),(0,[z0,z2,z778,z4,z5,z6]),(0,[z0,z2,z3,z4,z114,z318])],[(0,[z0,z2,z4,z779,z5,z6]),(0,[z0,z244,z42,z4,z5,z6]),(0,[z0,z13,z2,z496,z14,z5]),(0,[z0,z2,z3,z4,z51,z6]),(0,[z0,z2,z4,z5,z67,z780]),(0,[z0,z2,z3,z4,z781,z6]),(0,[z0,z11,z2,z3,z5,z125])]],
   [[(0,[z203,z69,z3,z4,z8,z6]),(0,[z0,z2,z144,z22,z4,z5])],[(0,[z0,z2,z3,z782,z4,z5]),(0,[z0,z137,z32,z4,z5,z6]),(0,[z75,z2,z76,z4,z8,z6]),(0,[z0,z2,z3,z4,z302,z6])],[(0,[z0,z2,z3,z4,z5,z783]),(1,[z0,z3,z784,z5,z6]),(0,[z0,z2,z3,z5,z6,z785])],[(0,[z0,z2,z786,z4,z5,z6]),(0,[z0,z66,z2,z14,z5,z6]),(0,[z0,z787,z3,z4,z5,z6])],[(0,[z0,z3,z4,z788,z5,z6]),(0,[z75,z11,z2,z76,z4,z5]),(0,[z0,z158,z2,z3,z22,z5])],[(0,[z0,z2,z74,z150,z5,z6]),(0,[z0,z2,z3,z4,z20,z250]),(0,[z0,z175,z2,z4,z746,z6])],[(0,[z0,z789,z3,z4,z5,z6]),(0,[z0,z77,z2,z3,z4,z5]),(0,[z0,z2,z307,z3,z4,z8]),(0,[z41,z0,z11,z2,z3,z8]),(1,[z0,z3,z4,z5,z759])],[(0,[z2,z3,z4,z5,z790,z59]),(0,[z0,z11,z2,z791,z4,z5])],[(0,[z34,z2,z98,z4,z8,z6]),(0,[z2,z691,z3,z4,z20,z6])],[(0,[z2,z3,z4,z249,z20,z6]),(0,[z0,z2,z3,z4,z5,z792])],[(0,[z0,z2,z793,z4,z5,z6]),(0,[z0,z11,z2,z26,z19,z5]),(0,[z0,z2,z3,z4,z794,z6]),(0,[z795,z0,z2,z3,z4,z5])],[(0,[z0,z2,z3,z796,z5,z6]),(0,[z0,z797,z3,z4,z5,z6]),(0,[z0,z2,z3,z142,z4,z8]),(0,[z2,z3,z4,z572,z8,z6]),(0,[z0,z2,z798,z3,z4,z6]),(0,[z0,z2,z133,z3,z22,z4]),(0,[z0,z11,z2,z3,z514,z5])],[(0,[z303,z69,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z20,z273])],[(0,[z188,z2,z76,z4,z5,z6]),(0,[z0,z11,z66,z2,z3,z5]),(0,[z0,z2,z3,z4,z746,z6]),(0,[z0,z11,z2,z298,z5,z95])],[(0,[z0,z2,z3,z4,z5,z799]),(0,[z0,z800,z3,z4,z5,z6]),(0,[z40,z2,z3,z4,z801,z6]),(0,[z2,z4,z283,z20,z8,z6]),(0,[z0,z2,z3,z20,z6,z802]),(0,[z0,z2,z3,z803,z5,z6])],[(0,[z0,z2,z3,z4,z8,z390]),(0,[z0,z2,z3,z4,z804,z6]),(0,[z0,z2,z3,z805,z4,z5]),(0,[z41,z0,z11,z2,z3,z81]),(0,[z170,z0,z3,z4,z417,z5])]],
   [[(0,[z0,z2,z3,z22,z4,z8]),(0,[z0,z11,z2,z806,z4,z5]),(0,[z0,z2,z152,z3,z4,z807])],[(0,[z0,z2,z307,z3,z4,z20]),(0,[z41,z0,z11,z2,z3,z20])],[(0,[z0,z11,z2,z74,z4,z5]),(0,[z0,z2,z3,z4,z808,z6]),(0,[z0,z809,z3,z4,z5,z6])],[(0,[z0,z137,z3,z4,z5,z64]),(0,[z134,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z810,z6]),(0,[z0,z2,z3,z4,z811,z6])],[(0,[z0,z2,z74,z4,z5,z390]),(0,[z0,z2,z3,z812,z5,z6]),(0,[z0,z2,z3,z4,z813,z5]),(0,[z0,z11,z2,z3,z644,z5])],[(0,[z107,z31,z3,z553,z5,z6]),(0,[z0,z11,z2,z3,z4,z475]),(0,[z0,z2,z3,z4,z814,z6]),(0,[z0,z2,z4,z283,z174,z6]),(0,[z0,z11,z2,z98,z4,z8]),(0,[z621,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z815,z5])],[(0,[z0,z2,z3,z710,z4,z5]),(0,[z0,z2,z3,z142,z4,z20]),(0,[z0,z2,z449,z3,z4,z428])],[(0,[z0,z2,z3,z4,z5,z816]),(0,[z0,z2,z817,z4,z5,z6]),(0,[z0,z2,z3,z289,z4,z470]),(0,[z0,z2,z3,z22,z5,z184])],[(0,[z0,z2,z3,z818,z4,z5]),(0,[z0,z13,z2,z14,z20,z6])],[(0,[z0,z1,z2,z14,z5,z6])],[(0,[z0,z819,z2,z4,z5,z6]),(0,[z0,z2,z3,z204,z5,z6]),(0,[z0,z2,z3,z451,z8,z6]),(0,[z0,z2,z3,z4,z5,z820])],[(0,[z0,z2,z3,z4,z5,z821]),(0,[z0,z2,z3,z4,z822,z6]),(0,[z0,z2,z3,z22,z4,z20]),(0,[z0,z2,z3,z4,z823,z6]),(0,[z824,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z295,z82,z6])],[(0,[z0,z11,z2,z3,z383,z5]),(0,[z0,z2,z43,z138,z5,z443])],[(0,[z34,z2,z4,z283,z8,z6]),(0,[z0,z2,z60,z4,z588,z6]),(0,[z0,z157,z3,z4,z25,z241]),(0,[z0,z2,z4,z118,z746,z6]),(0,[z0,z2,z3,z4,z5,z780])],[(0,[z0,z13,z2,z22,z14,z5]),(0,[z41,z0,z11,z2,z3,z202])]],
   [[(0,[z0,z2,z3,z142,z393,z5]),(0,[z0,z777,z3,z4,z5,z6]),(0,[z592,z2,z3,z4,z5,z59]),(0,[z0,z2,z60,z4,z190,z6]),(0,[z0,z825,z2,z3,z5,z6]),(0,[z0,z2,z3,z16,z343,z6])],[(0,[z57,z2,z826,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z827]),(0,[z0,z2,z450,z288,z4,z5])],[(0,[z0,z2,z3,z150,z5,z6]),(0,[z0,z157,z3,z4,z162,z6]),(0,[z0,z2,z144,z16,z4,z6]),(0,[z425,z0,z489,z2,z3,z5])],[(0,[z0,z2,z3,z22,z150,z5]),(0,[z0,z622,z21,z4,z5,z6]),(0,[z0,z58,z3,z4,z5,z207]),(0,[z156,z2,z3,z19,z5,z6]),(0,[z0,z2,z144,z4,z5,z828]),(0,[z0,z2,z3,z4,z829,z6])],[(0,[z0,z2,z3,z4,z5,z830]),(0,[z201,z2,z3,z4,z265,z6]),(0,[z196,z0,z2,z3,z4,z202])],[(0,[z0,z2,z3,z831,z5,z6]),(0,[z57,z11,z2,z32,z4,z5]),(0,[z0,z2,z3,z22,z393,z5])],[(0,[z0,z2,z3,z832,z5,z6])],[(0,[z34,z11,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z5,z833]),(0,[z0,z2,z3,z834,z4,z5])],[(0,[z0,z11,z2,z3,z553,z5]),(0,[z0,z2,z3,z4,z835,z6]),(0,[z0,z2,z3,z4,z836,z6]),(0,[z837,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z728,z25,z6]),(0,[z0,z2,z3,z4,z5,z838])],[(0,[z0,z2,z87,z22,z4,z5])],[(0,[z0,z2,z839,z3,z4,z5]),(0,[z2,z3,z18,z840,z5,z6])],[(0,[z0,z2,z3,z225,z280,z6]),(0,[z0,z11,z2,z3,z140,z5])],[(0,[z0,z30,z354,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z841]),(0,[z0,z2,z3,z4,z842,z6]),(0,[z0,z23,z3,z83,z5,z24]),(0,[z0,z2,z3,z4,z5,z843]),(0,[z0,z11,z2,z3,z4,z844])],[(0,[z0,z845,z2,z3,z4,z6]),(0,[z0,z2,z3,z846,z19,z5]),(0,[z0,z2,z847,z3,z4,z6])],[(0,[z0,z2,z3,z4,z807,z209])],[(0,[z0,z11,z2,z144,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z5,z848]),(0,[z0,z2,z3,z4,z5,z849]),(0,[z0,z11,z2,z3,z4,z502])],[(0,[z0,z2,z3,z4,z5,z390]),(0,[z0,z2,z3,z4,z5,z850]),(0,[z0,z2,z3,z22,z4,z51]),(0,[z0,z2,z3,z4,z851,z6]),(0,[z0,z2,z26,z4,z5,z202])],[(0,[z0,z852,z2,z3,z4,z5]),(0,[z0,z2,z3,z22,z171,z5])],[(0,[z0,z2,z3,z22,z4,z421]),(0,[z0,z2,z98,z22,z4,z5]),(0,[z0,z11,z2,z298,z4,z20]),(0,[z41,z0,z2,z3,z431,z6]),(0,[z134,z11,z2,z3,z4,z5]),(0,[z0,z456,z2,z26,z4,z5]),(0,[z853,z2,z3,z22,z4,z5])],[(0,[z0,z137,z3,z4,z20,z6]),(0,[z2,z3,z660,z4,z8,z6]),(0,[z0,z3,z4,z784,z5,z6])],[(0,[z0,z2,z3,z4,z5,z854]),(0,[z215,z0,z3,z4,z8,z146]),(0,[z0,z2,z60,z22,z4,z190])],[(0,[z0,z2,z3,z4,z5,z855]),(0,[z2,z4,z19,z283,z8,z6]),(0,[z0,z13,z2,z775,z5,z6]),(0,[z0,z856,z2,z3,z4,z5]),(0,[z41,z134,z11,z2,z3,z5])],[(0,[z0,z2,z857,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z858])],[(0,[z0,z859,z2,z3,z553,z5]),(0,[z0,z2,z860,z3,z4,z6]),(0,[z0,z2,z3,z4,z48,z318]),(0,[z0,z2,z4,z5,z780,z6]),(0,[z0,z2,z3,z4,z5,z861])],[(0,[z0,z2,z826,z4,z5,z6])],[(0,[z0,z2,z3,z862,z150,z5]),(0,[z107,z31,z3,z4,z20,z6]),(0,[z0,z11,z2,z3,z238,z5]),(0,[z0,z11,z2,z3,z260,z5]),(0,[z0,z2,z3,z4,z8,z380])],[(0,[z0,z137,z3,z4,z126,z6]),(0,[z0,z567,z3,z83,z5,z6]),(0,[z180,z2,z3,z22,z4,z20]),(0,[z452,z0,z3,z4,z5,z146]),(0,[z0,z11,z2,z353,z4,z5])],[(0,[z0,z2,z3,z451,z5,z6]),(0,[z700,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z6,z863])],[(0,[z40,z2,z3,z18,z208,z6]),(0,[z0,z2,z22,z4,z283,z8]),(0,[z0,z2,z284,z4,z5,z6])],[(0,[z0,z2,z3,z393,z8,z6]),(0,[z0,z2,z864,z3,z4,z5])],[(0,[z0,z2,z3,z865,z4,z5]),(0,[z47,z2,z3,z19,z261,z6]),(0,[z0,z2,z866,z4,z5,z6]),(0,[z47,z2,z3,z142,z19,z5]),(0,[z0,z11,z2,z867,z4,z5])]],
   [[(0,[z0,z868,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z869]),(0,[z0,z2,z4,z722,z5,z6]),(0,[z0,z2,z3,z870,z4,z5]),(0,[z285,z0,z564,z3,z193,z6]),(0,[z215,z0,z2,z26,z4,z5]),(0,[z0,z11,z2,z298,z17,z5])],[(0,[z0,z2,z376,z4,z199,z6]),(0,[z0,z11,z2,z3,z451,z5])],[(0,[z463,z0,z2,z4,z606,z5])],[(0,[z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z4,z5,z871,z6]),(1,[z2,z826,z4,z5,z6]),(0,[z65,z0,z2,z4,z20,z67]),(0,[z0,z2,z872,z4,z5,z6]),(0,[z0,z2,z873,z4,z5,z6]),(0,[z0,z2,z138,z775,z5,z6]),(0,[z874,z2,z3,z4,z5,z6])],[(0,[z107,z31,z3,z4,z5,z121]),(0,[z0,z2,z3,z4,z875,z6]),(0,[z47,z2,z3,z22,z19,z5]),(0,[z0,z2,z149,z3,z18,z5]),(0,[z0,z2,z3,z4,z6,z807])],[(0,[z0,z2,z3,z4,z20,z207]),(0,[z34,z2,z3,z4,z876,z6]),(0,[z2,z3,z4,z8,z277,z6]),(0,[z0,z877,z3,z4,z5,z6])],[(0,[z0,z11,z2,z3,z4,z199]),(0,[z201,z2,z3,z4,z8,z6])],[],[(0,[z0,z2,z74,z4,z5,z6]),(0,[z0,z69,z74,z4,z5,z6]),(0,[z0,z2,z3,z4,z878,z6]),(0,[z0,z11,z2,z3,z4,z280]),(0,[z0,z2,z3,z4,z5,z807])],[(0,[z0,z2,z3,z4,z5,z879])],[(0,[z0,z2,z3,z4,z880,z6])],[],[(0,[z0,z2,z3,z4,z126,z207]),(0,[z139,z2,z3,z4,z8,z6]),(0,[z253,z2,z3,z4,z8,z6]),(0,[z2,z3,z4,z881,z5,z6]),(0,[z0,z564,z2,z3,z44,z4]),(0,[z0,z2,z3,z4,z5,z882])],[(0,[z394,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z22,z4,z302]),(0,[z883,z2,z3,z4,z5,z6]),(0,[z0,z2,z450,z4,z5,z85])],[(0,[z69,z713,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z884])],[(0,[z0,z2,z3,z885,z5,z6]),(0,[z0,z2,z3,z4,z5,z886]),(0,[z0,z2,z4,z5,z6,z887]),(0,[z0,z2,z3,z4,z888,z6]),(0,[z0,z2,z3,z4,z728,z6])]],
   [[(0,[z889,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z60,z4,z190])],[(0,[z0,z2,z98,z4,z190,z6]),(0,[z0,z2,z3,z17,z5,z890])],[(0,[z0,z2,z3,z4,z5,z891]),(1,[z201,z11,z2,z3,z5]),(1,[z0,z2,z3,z734,z6])],[(0,[z0,z2,z3,z4,z5,z892]),(0,[z0,z11,z2,z298,z18,z5]),(0,[z0,z2,z356,z4,z5,z85]),(0,[z72,z2,z3,z140,z4,z5])],[(0,[z0,z11,z2,z893,z4,z5])],[(0,[z0,z2,z3,z4,z894,z6]),(0,[z0,z23,z3,z83,z20,z6]),(0,[z0,z2,z3,z4,z5,z895])],[(0,[z465,z0,z11,z2,z3,z5]),(0,[z0,z2,z896,z4,z5,z6])],[(0,[z0,z2,z3,z4,z199,z121]),(0,[z0,z2,z3,z4,z8,z897]),(0,[z0,z2,z3,z393,z487,z6]),(0,[z0,z2,z149,z4,z5,z85]),(0,[z0,z11,z2,z898,z4,z5])],[(0,[z0,z123,z3,z4,z20,z12])],[(0,[z409,z31,z3,z4,z5,z6]),(0,[z0,z2,z3,z899,z4,z5])],[(0,[z0,z2,z775,z14,z5,z6])],[(0,[z0,z2,z3,z4,z8,z112]),(0,[z211,z2,z3,z225,z5,z185])],[(0,[z0,z2,z3,z4,z5,z900]),(0,[z0,z764,z3,z4,z5,z6]),(0,[z0,z901,z21,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z902]),(0,[z0,z2,z3,z22,z8,z71]),(0,[z0,z11,z2,z3,z470,z5]),(0,[z0,z2,z3,z4,z903,z6])],[(0,[z0,z2,z769,z4,z5,z6]),(0,[z0,z2,z3,z904,z4,z5]),(0,[z0,z2,z3,z4,z905,z6]),(0,[z0,z2,z3,z4,z906,z6])],[(0,[z0,z28,z21,z22,z4,z5]),(0,[z0,z2,z907,z4,z5,z6]),(0,[z0,z2,z908,z4,z5,z6]),(0,[z0,z23,z3,z83,z5,z631])]],
   [[(0,[z57,z2,z651,z4,z5,z6]),(0,[z0,z2,z3,z393,z5,z6]),(0,[z0,z11,z2,z3,z17,z8]),(0,[z0,z2,z3,z4,z909,z6]),(0,[z0,z2,z3,z4,z5,z910])],[(0,[z0,z2,z3,z911,z5,z6]),(0,[z0,z11,z2,z26,z4,z5]),(0,[z0,z489,z2,z3,z114,z5])],[(0,[z0,z2,z912,z4,z8,z6]),(0,[z0,z2,z3,z4,z20,z266]),(0,[z0,z11,z564,z2,z3,z4]),(0,[z0,z257,z3,z335,z4,z5])],[(0,[z0,z116,z3,z4,z25,z6]),(0,[z0,z11,z52,z3,z4,z100]),(0,[z0,z2,z3,z4,z5,z913]),(0,[z874,z11,z2,z3,z4,z5])],[(0,[z0,z2,z376,z22,z4,z5]),(0,[z0,z2,z3,z4,z749,z6]),(0,[z2,z3,z19,z8,z71,z6])],[(0,[z203,z69,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z914,z6])],[(0,[z75,z2,z76,z4,z5,z6]),(0,[z0,z915,z3,z4,z5,z6]),(0,[z2,z3,z140,z4,z8,z6])],[(0,[z0,z2,z3,z4,z5,z916]),(0,[z0,z2,z3,z4,z8,z917]),(0,[z0,z2,z3,z4,z20,z918])],[(0,[z11,z2,z3,z19,z8,z6]),(0,[z201,z2,z3,z4,z5,z6]),(0,[z0,z219,z21,z4,z5,z6]),(0,[z0,z2,z3,z4,z281,z108])],[(0,[z0,z2,z3,z919,z553,z5]),(0,[z240,z11,z2,z3,z4,z8]),(0,[z920,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z921]),(0,[z0,z3,z4,z5,z759,z6])],[(0,[z0,z2,z922,z3,z4,z6])],[(0,[z0,z2,z3,z553,z199,z6])],[(0,[z0,z2,z3,z4,z5,z923]),(0,[z0,z2,z3,z22,z4,z336]),(0,[z0,z2,z3,z4,z924,z6]),(0,[z0,z11,z160,z2,z3,z5]),(0,[z0,z11,z2,z3,z4,z925])],[(0,[z0,z2,z60,z4,z283,z6]),(0,[z0,z2,z98,z4,z118,z6]),(0,[z0,z11,z2,z3,z364,z5]),(0,[z0,z2,z3,z5,z734,z6])],[],[(0,[z0,z2,z4,z8,z6,z887]),(0,[z0,z2,z3,z4,z5,z926])]],
   [[(0,[z2,z3,z4,z183,z8,z6]),(0,[z0,z2,z3,z927,z5,z6]),(0,[z233,z0,z2,z298,z4,z5])],[(0,[z0,z928,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z19,z5])],[(0,[z0,z11,z2,z3,z5,z469]),(0,[z0,z11,z2,z3,z4,z929])],[(0,[z0,z2,z3,z930,z5,z6]),(0,[z0,z1,z2,z3,z22,z5])],[(0,[z488,z2,z3,z19,z5,z6]),(0,[z0,z2,z307,z3,z18,z5]),(1,[z0,z2,z4,z746,z6]),(0,[z201,z175,z2,z3,z4,z6])],[(0,[z0,z96,z3,z4,z115,z6]),(0,[z0,z388,z2,z4,z283,z6]),(0,[z0,z2,z931,z3,z4,z5])],[],[(0,[z0,z11,z2,z3,z4,z369]),(0,[z0,z157,z3,z4,z728,z6])],[(0,[z0,z2,z144,z4,z20,z6]),(0,[z134,z2,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z470,z209])],[(0,[z0,z2,z3,z4,z5,z932])],[(0,[z0,z11,z2,z3,z265,z5]),(0,[z0,z2,z4,z5,z933,z6]),(0,[z191,z2,z3,z4,z5,z59]),(0,[z0,z11,z13,z2,z14,z5]),(0,[z0,z2,z3,z4,z5,z934])],[(0,[z0,z2,z3,z935,z4,z5]),(0,[z57,z58,z32,z4,z5,z6]),(0,[z0,z726,z3,z4,z5,z6]),(0,[z2,z3,z83,z19,z8,z6])],[(0,[z0,z2,z3,z4,z936,z5]),(0,[z57,z2,z32,z4,z5,z64]),(0,[z0,z2,z149,z3,z19,z5]),(0,[z2,z3,z4,z20,z876,z6]),(0,[z201,z157,z2,z3,z4,z6]),(0,[z41,z0,z11,z52,z2,z3]),(0,[z0,z11,z2,z3,z5,z293])],[(0,[z211,z2,z3,z4,z20,z185]),(0,[z136,z2,z3,z4,z20,z6]),(0,[z0,z3,z4,z5,z146,z759]),(0,[z0,z2,z3,z4,z5,z112]),(0,[z0,z714,z3,z22,z4,z5])],[(0,[z0,z564,z2,z3,z4,z6])],[(0,[z937,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z938,z6]),(0,[z0,z2,z3,z4,z5,z890])]],
   [[(0,[z0,z2,z3,z18,z5,z380]),(0,[z0,z2,z3,z4,z8,z250]),(0,[z0,z2,z298,z22,z4,z5])],[(0,[z11,z2,z3,z18,z19,z5]),(0,[z0,z2,z3,z4,z939,z6])],[(0,[z0,z11,z2,z3,z182,z5]),(0,[z0,z489,z2,z152,z3,z5])],[(0,[z0,z940,z2,z3,z20,z6])],[(0,[z0,z2,z3,z846,z4,z5]),(0,[z409,z2,z3,z4,z8,z6]),(0,[z0,z2,z912,z4,z5,z6]),(0,[z0,z11,z2,z3,z5,z500])],[(0,[z0,z2,z353,z22,z4,z5]),(0,[z0,z13,z2,z149,z14,z5]),(1,[z0,z2,z4,z5,z780]),(0,[z0,z2,z791,z4,z5,z6])],[(0,[z0,z2,z3,z4,z941,z6]),(0,[z0,z137,z3,z204,z5,z6]),(0,[z0,z2,z3,z4,z942,z6]),(0,[z0,z2,z3,z4,z5,z827]),(0,[z0,z2,z3,z4,z5,z943])],[(0,[z2,z3,z4,z441,z8,z6]),(0,[z0,z2,z3,z4,z8,z273]),(0,[z0,z11,z2,z4,z283,z8]),(0,[z0,z319,z3,z4,z368,z6]),(0,[z0,z2,z3,z4,z5,z751])],[(0,[z285,z0,z87,z193,z5,z6]),(0,[z201,z11,z2,z3,z4,z5])],[],[(0,[z0,z944,z2,z3,z4,z5]),(0,[z47,z2,z3,z19,z20,z6]),(0,[z0,z2,z945,z4,z8,z6]),(0,[z0,z2,z3,z4,z946,z6]),(0,[z0,z2,z3,z4,z947,z6])],[(0,[z0,z2,z3,z4,z5,z948]),(0,[z215,z0,z3,z4,z417,z5]),(0,[z0,z2,z3,z4,z5,z949]),(0,[z0,z201,z11,z2,z3,z5])],[(0,[z0,z2,z3,z4,z950,z6]),(0,[z0,z11,z2,z3,z846,z5]),(0,[z0,z951,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z952])],[(0,[z0,z2,z3,z4,z5,z953]),(0,[z0,z2,z3,z16,z17,z6])],[(0,[z0,z2,z3,z4,z954,z6]),(0,[z0,z955,z3,z4,z5,z6])],[(0,[z0,z11,z2,z3,z5,z242])]],
   [[(0,[z0,z2,z3,z4,z5,z956]),(0,[z0,z123,z3,z4,z8,z12]),(0,[z0,z2,z3,z4,z541,z108])],[(0,[z0,z11,z2,z376,z4,z5]),(0,[z2,z713,z3,z4,z5,z6]),(0,[z0,z957,z2,z3,z4,z6]),(0,[z0,z58,z3,z22,z4,z5]),(0,[z180,z11,z2,z3,z19,z5]),(0,[z39,z0,z11,z2,z3,z5])],[(0,[z0,z2,z3,z4,z8,z720]),(0,[z0,z2,z3,z419,z265,z6]),(0,[z512,z2,z3,z4,z5,z59])],[(0,[z0,z13,z2,z14,z8,z6]),(0,[z0,z11,z2,z43,z138,z5])],[(0,[z107,z31,z3,z150,z5,z6]),(0,[z40,z2,z3,z18,z441,z6]),(0,[z0,z2,z60,z4,z55,z6]),(0,[z0,z11,z958,z3,z4,z5])],[(0,[z0,z859,z2,z3,z4,z5]),(0,[z0,z58,z3,z4,z336,z6]),(0,[z0,z2,z3,z4,z959,z6]),(0,[z65,z0,z2,z4,z5,z780])],[(0,[z0,z2,z3,z4,z336,z64])],[(0,[z0,z2,z3,z204,z5,z207]),(0,[z0,z2,z3,z4,z960,z6])],[(0,[z0,z2,z3,z4,z961,z6]),(0,[z0,z2,z98,z16,z4,z6]),(0,[z0,z2,z3,z962,z4,z5]),(0,[z0,z2,z3,z4,z5,z963])],[(0,[z75,z2,z4,z286,z5,z6]),(0,[z0,z11,z2,z3,z504,z5]),(0,[z41,z0,z11,z2,z3,z17])],[(0,[z0,z2,z3,z4,z801,z6]),(0,[z2,z3,z138,z19,z8,z6]),(0,[z40,z2,z98,z4,z8,z6]),(0,[z0,z2,z4,z8,z933,z6]),(0,[z0,z2,z197,z3,z4,z8]),(0,[z0,z2,z3,z4,z20,z403]),(0,[z215,z0,z3,z4,z5,z146]),(0,[z0,z2,z3,z4,z6,z964])],[(0,[z0,z965,z2,z3,z4,z5]),(0,[z0,z966,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z967]),(0,[z0,z2,z968,z4,z5,z6])],[(0,[z484,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z20,z443]),(0,[z211,z2,z3,z4,z5,z790])],[(0,[z0,z2,z3,z22,z4,z475]),(0,[z57,z2,z32,z4,z20,z6])],[(0,[z0,z2,z969,z3,z4,z5]),(0,[z0,z2,z98,z4,z283,z6]),(0,[z0,z2,z26,z4,z20,z6]),(0,[z0,z106,z42,z4,z5,z6]),(0,[z0,z2,z87,z4,z5,z970])],[(0,[z0,z2,z3,z4,z5,z380]),(0,[z0,z2,z3,z4,z487,z6]),(0,[z937,z11,z2,z3,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z971,z6]),(0,[z0,z2,z3,z4,z972,z6]),(0,[z973,z2,z3,z4,z5,z6])],[(0,[z0,z2,z87,z4,z20,z6]),(0,[z0,z2,z3,z4,z5,z974]),(0,[z0,z2,z152,z3,z4,z209])],[(0,[z0,z2,z3,z4,z20,z241]),(0,[z0,z2,z3,z393,z280,z6]),(0,[z0,z2,z3,z4,z5,z250]),(0,[z0,z2,z975,z4,z5,z6])],[(0,[z107,z31,z3,z4,z5,z390]),(0,[z191,z2,z3,z22,z4,z8]),(0,[z2,z3,z4,z8,z618,z6])],[(0,[z57,z2,z32,z4,z126,z6])],[(0,[z0,z11,z2,z3,z4,z103]),(0,[z0,z976,z2,z3,z4,z6]),(0,[z0,z2,z197,z3,z4,z20]),(0,[z285,z0,z3,z784,z5,z6])],[(0,[z285,z0,z307,z3,z193,z5]),(0,[z65,z0,z2,z26,z4,z5])],[(0,[z0,z2,z3,z150,z199,z6]),(0,[z0,z2,z3,z977,z5,z6]),(0,[z2,z3,z341,z4,z8,z6]),(0,[z0,z2,z3,z4,z280,z6])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z137,z3,z451,z5,z6]),(0,[z0,z978,z2,z3,z4,z5]),(0,[z2,z3,z19,z14,z8,z6]),(0,[z0,z2,z3,z20,z6,z184])],[(0,[z0,z2,z3,z4,z979,z6]),(0,[z0,z2,z3,z4,z5,z273]),(0,[z980,z2,z3,z4,z5,z6]),(0,[z0,z981,z2,z3,z4,z5])],[(0,[z0,z982,z3,z4,z5,z6]),(0,[z0,z226,z2,z4,z118,z6])],[],[(0,[z0,z2,z945,z4,z5,z6]),(0,[z0,z2,z43,z138,z20,z6]),(0,[z0,z2,z4,z14,z5,z53]),(0,[z0,z2,z298,z4,z5,z443]),(0,[z0,z983,z3,z4,z5,z6]),(0,[z0,z2,z3,z22,z282,z5])],[(0,[z46,z2,z3,z4,z8,z6]),(0,[z0,z984,z3,z4,z5,z6])],[(0,[z2,z3,z826,z4,z5,z6]),(0,[z0,z2,z307,z3,z4,z502]),(0,[z0,z123,z3,z4,z5,z759])],[(0,[z0,z137,z3,z4,z8,z6]),(0,[z34,z2,z3,z22,z4,z8]),(0,[z0,z2,z985,z4,z8,z6]),(0,[z0,z2,z149,z26,z4,z5])]],
   [[(0,[z0,z2,z3,z22,z553,z5]),(0,[z40,z2,z4,z283,z8,z6]),(0,[z46,z2,z3,z18,z5,z6]),(0,[z0,z489,z2,z3,z20,z6]),(0,[z285,z0,z3,z22,z193,z5]),(0,[z0,z52,z3,z4,z254,z6]),(0,[z0,z11,z2,z3,z389,z5])],[(0,[z485,z0,z11,z2,z3,z5])],[(0,[z0,z11,z2,z3,z4,z261]),(0,[z0,z2,z26,z19,z5,z6]),(0,[z0,z2,z197,z3,z17,z5])],[(0,[z0,z2,z986,z3,z4,z5]),(0,[z0,z2,z3,z987,z5,z6]),(0,[z0,z2,z3,z4,z502,z6])],[(0,[z0,z2,z3,z4,z5,z988]),(0,[z2,z3,z4,z19,z261,z6])],[(0,[z0,z2,z3,z553,z103,z6]),(0,[z107,z31,z3,z4,z8,z6]),(0,[z211,z2,z3,z4,z8,z185]),(0,[z2,z651,z3,z4,z20,z6])],[(0,[z0,z2,z3,z4,z199,z390]),(0,[z0,z11,z2,z3,z18,z8]),(0,[z0,z2,z3,z4,z5,z989]),(0,[z0,z2,z3,z990,z4,z5])],[(0,[z0,z2,z3,z4,z991,z6]),(0,[z0,z2,z3,z992,z5,z6])],[(0,[z0,z993,z2,z3,z4,z5]),(0,[z0,z11,z2,z87,z4,z5]),(0,[z0,z2,z3,z22,z4,z502]),(0,[z0,z11,z2,z3,z4,z994])],[(0,[z0,z2,z4,z995,z5,z6]),(0,[z0,z2,z3,z451,z5,z207]),(0,[z0,z2,z43,z138,z5,z159])],[(0,[z107,z31,z74,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z996]),(0,[z0,z2,z3,z4,z5,z721]),(0,[z0,z2,z3,z4,z997,z6]),(0,[z0,z2,z998,z4,z8,z6]),(0,[z0,z2,z60,z4,z190,z266])],[(0,[z0,z2,z3,z4,z999,z6]),(0,[z0,z2,z3,z4,z5,z1000]),(0,[z0,z2,z133,z21,z4,z6]),(0,[z0,z2,z3,z4,z5,z1001])],[(0,[z0,z2,z3,z1002,z4,z5]),(0,[z0,z2,z3,z4,z5,z897]),(0,[z0,z2,z3,z4,z1003,z6]),(0,[z0,z2,z3,z4,z5,z1004])],[(0,[z0,z2,z3,z142,z5,z71]),(0,[z0,z2,z3,z44,z4,z8]),(0,[z0,z2,z26,z4,z5,z59]),(0,[z0,z2,z3,z4,z1005,z6]),(0,[z41,z0,z11,z157,z2,z3]),(0,[z41,z0,z2,z197,z3,z81])],[(0,[z65,z0,z2,z4,z8,z67])],[(0,[z0,z2,z3,z1006,z5,z6]),(0,[z2,z3,z22,z4,z20,z8]),(0,[z1007,z0,z2,z3,z4,z6]),(0,[z0,z181,z2,z26,z4,z5]),(0,[z0,z11,z2,z26,z22,z5])]],
   [[(0,[z0,z2,z857,z4,z421,z6]),(0,[z0,z2,z3,z4,z8,z207]),(0,[z163,z0,z2,z26,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1008]),(0,[z0,z11,z809,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1009]),(0,[z0,z575,z21,z4,z5,z6]),(0,[z0,z2,z3,z22,z5,z71])],[(0,[z0,z2,z3,z22,z5,z401]),(0,[z1010,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1011]),(0,[z0,z11,z157,z3,z4,z25]),(1,[z0,z2,z3,z4,z807])],[(0,[z0,z2,z60,z4,z126,z6])],[(0,[z581,z2,z3,z19,z8,z6]),(0,[z0,z2,z3,z4,z5,z741]),(0,[z0,z2,z98,z4,z255,z6])],[(0,[z0,z2,z3,z204,z336,z6]),(0,[z0,z77,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z20,z1012])],[(0,[z0,z2,z3,z4,z1013,z6])],[(0,[z0,z11,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z1014,z6]),(0,[z0,z2,z1015,z4,z5,z6]),(0,[z548,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z44,z4,z20]),(0,[z2,z3,z4,z5,z790,z6]),(0,[z0,z2,z26,z4,z5,z185]),(0,[z0,z52,z3,z4,z100,z6]),(0,[z0,z1016,z3,z4,z5,z6])],[(0,[z0,z2,z1017,z4,z5,z6]),(0,[z0,z2,z3,z22,z451,z5]),(0,[z0,z2,z3,z4,z1018,z6]),(0,[z0,z2,z3,z4,z5,z1019])],[(0,[z0,z2,z3,z4,z5,z1020]),(0,[z0,z2,z3,z4,z1021,z6])],[(0,[z0,z2,z4,z779,z421,z6]),(0,[z0,z2,z3,z4,z114,z108])],[(0,[z0,z2,z3,z1022,z5,z6]),(0,[z0,z2,z3,z4,z1023,z6]),(0,[z2,z3,z22,z4,z19,z8]),(0,[z0,z2,z3,z4,z5,z917])],[(0,[z0,z2,z74,z4,z199,z6]),(0,[z0,z2,z1024,z3,z4,z5]),(0,[z1025,z2,z3,z4,z5,z6])],[(0,[z0,z2,z376,z4,z103,z6]),(0,[z0,z2,z3,z22,z4,z199]),(0,[z0,z11,z2,z3,z542,z5]),(0,[z2,z3,z19,z193,z8,z6]),(0,[z0,z11,z2,z298,z19,z5])],[(0,[z0,z2,z3,z1026,z4,z5]),(0,[z0,z958,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1027]),(0,[z0,z23,z3,z83,z8,z6]),(0,[z0,z11,z2,z3,z20,z95]),(0,[z0,z2,z3,z22,z4,z280]),(0,[z0,z2,z3,z1028,z4,z5]),(0,[z0,z2,z3,z4,z1029,z6])],[(0,[z0,z137,z3,z4,z5,z6]),(0,[z0,z77,z2,z3,z4,z20]),(0,[z511,z2,z3,z4,z20,z6])],[(0,[z0,z2,z3,z4,z20,z53])],[(0,[z0,z2,z149,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1030])],[(0,[z57,z2,z32,z4,z8,z6]),(0,[z1031,z0,z2,z3,z8,z6]),(0,[z0,z2,z3,z4,z20,z1032]),(0,[z0,z2,z3,z4,z1033,z5])],[(0,[z0,z2,z3,z4,z5,z1034]),(0,[z191,z2,z3,z4,z8,z6]),(0,[z0,z181,z3,z4,z5,z146]),(0,[z0,z11,z2,z908,z4,z5])],[(0,[z107,z31,z3,z4,z5,z6]),(0,[z107,z713,z3,z4,z5,z6]),(0,[z240,z11,z2,z3,z18,z5]),(0,[z645,z2,z3,z4,z20,z6]),(0,[z0,z2,z1035,z4,z5,z6])],[(0,[z0,z3,z4,z5,z1036,z6]),(0,[z41,z0,z11,z175,z2,z3])],[(0,[z0,z2,z3,z4,z1037,z6]),(0,[z0,z2,z3,z4,z174,z6]),(0,[z641,z2,z3,z4,z8,z6]),(0,[z578,z2,z3,z4,z8,z6]),(0,[z348,z2,z3,z4,z20,z6]),(0,[z0,z489,z2,z152,z3,z209])],[(0,[z75,z2,z76,z4,z174,z6]),(0,[z75,z2,z76,z4,z369,z6]),(0,[z0,z2,z474,z3,z4,z229]),(0,[z0,z11,z2,z3,z5,z688]),(0,[z0,z2,z519,z4,z5,z67])],[],[(0,[z0,z2,z376,z4,z20,z6]),(0,[z0,z1038,z2,z3,z4,z5]),(0,[z0,z11,z2,z3,z4,z954])],[(0,[z0,z2,z3,z4,z8,z266])],[(1,[z0,z3,z4,z728,z6])],[(0,[z0,z978,z2,z3,z204,z5]),(0,[z643,z2,z3,z4,z20,z6]),(0,[z0,z13,z2,z133,z14,z6])]],
   [[(0,[z0,z11,z2,z3,z387,z5]),(0,[z0,z257,z3,z4,z5,z12]),(0,[z0,z2,z4,z775,z5,z6]),(0,[z65,z0,z2,z4,z5,z67])],[(0,[z214,z2,z3,z4,z20,z59]),(0,[z0,z2,z3,z4,z5,z1039]),(0,[z0,z2,z384,z4,z5,z85])],[(0,[z0,z2,z3,z4,z5,z207]),(0,[z0,z137,z4,z118,z5,z6]),(0,[z34,z2,z3,z4,z8,z6]),(0,[z0,z2,z152,z3,z4,z428])],[(0,[z0,z2,z3,z5,z71,z293]),(0,[z0,z11,z2,z3,z22,z5])],[(0,[z0,z2,z3,z4,z103,z121]),(0,[z0,z2,z43,z138,z8,z6]),(0,[z0,z2,z29,z4,z20,z85]),(0,[z0,z2,z3,z16,z734,z6]),(0,[z0,z2,z3,z5,z184,z293]),(0,[z425,z0,z2,z3,z4,z559])],[(0,[z0,z2,z3,z4,z5,z1040]),(0,[z39,z2,z3,z4,z8,z6]),(0,[z40,z2,z3,z550,z5,z6]),(0,[z0,z2,z284,z22,z4,z5])],[(0,[z0,z2,z1041,z4,z5,z6]),(0,[z0,z2,z3,z4,z1042,z6])],[(0,[z0,z11,z2,z3,z5,z82]),(0,[z201,z11,z2,z3,z5,z6])],[(0,[z0,z2,z3,z1043,z4,z5]),(0,[z0,z2,z3,z451,z336,z6]),(0,[z0,z2,z3,z4,z5,z1044])],[(0,[z10,z2,z3,z4,z8,z6]),(0,[z0,z489,z2,z3,z5,z12])],[(0,[z0,z2,z4,z118,z174,z6]),(0,[z0,z2,z839,z3,z4,z8]),(0,[z214,z2,z3,z4,z143,z59]),(0,[z0,z2,z3,z4,z5,z1045]),(0,[z0,z11,z2,z968,z4,z5])],[(0,[z40,z2,z3,z19,z8,z6]),(0,[z0,z1046,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z1047,z6]),(0,[z0,z2,z873,z22,z4,z5])],[(0,[z0,z116,z3,z4,z272,z6]),(0,[z0,z2,z43,z531,z5,z6])],[(0,[z134,z2,z3,z4,z441,z6]),(0,[z0,z2,z3,z496,z4,z5]),(0,[z0,z2,z26,z4,z5,z108]),(0,[z0,z877,z3,z22,z4,z5])],[(0,[z203,z69,z3,z4,z421,z6]),(0,[z0,z2,z3,z4,z377,z6]),(0,[z0,z2,z98,z4,z20,z6]),(0,[z0,z2,z3,z1048,z5,z6])],[(0,[z57,z2,z32,z204,z5,z6]),(0,[z0,z2,z3,z4,z929,z6]),(0,[z0,z2,z307,z3,z19,z5]),(0,[z677,z2,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z74,z22,z4,z5]),(0,[z0,z11,z2,z3,z5,z63])],[(0,[z40,z2,z3,z4,z261,z6]),(0,[z0,z1049,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z1050,z6]),(0,[z0,z2,z3,z4,z20,z631]),(0,[z0,z2,z152,z3,z184,z209])],[(0,[z0,z2,z98,z22,z4,z8]),(0,[z0,z2,z144,z4,z8,z6]),(0,[z0,z2,z1051,z4,z5,z6]),(0,[z0,z2,z3,z4,z1052,z6])],[(0,[z0,z2,z3,z1053,z5,z6]),(0,[z581,z0,z2,z98,z4,z6])],[(0,[z0,z11,z137,z3,z4,z5]),(0,[z0,z2,z98,z4,z126,z6]),(0,[z671,z0,z2,z4,z5,z67]),(0,[z0,z123,z3,z4,z5,z12])],[(0,[z0,z11,z2,z866,z4,z5])],[(0,[z0,z2,z3,z4,z5,z720]),(0,[z581,z0,z2,z3,z81,z6]),(0,[z0,z2,z901,z4,z5,z6])],[(0,[z0,z674,z21,z4,z5,z6]),(0,[z0,z224,z21,z4,z5,z6]),(1,[z11,z2,z3,z19,z8]),(0,[z539,z2,z3,z4,z8,z6]),(0,[z0,z3,z4,z8,z1036,z6]),(0,[z0,z2,z298,z4,z20,z6]),(0,[z0,z13,z2,z14,z5,z6]),(0,[z0,z2,z3,z4,z108,z807])],[(0,[z0,z11,z23,z3,z83,z5]),(0,[z41,z0,z2,z3,z337,z6]),(0,[z0,z2,z133,z149,z3,z4])],[(0,[z0,z2,z376,z553,z5,z6]),(0,[z0,z2,z3,z4,z1054,z6]),(0,[z47,z77,z2,z3,z19,z5])],[(0,[z0,z153,z3,z4,z5,z12]),(0,[z0,z2,z3,z1055,z4,z5]),(0,[z0,z123,z2,z26,z4,z5])],[(0,[z166,z0,z3,z193,z5,z6]),(0,[z89,z2,z3,z19,z5,z6]),(0,[z40,z11,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z5,z1056]),(0,[z0,z11,z2,z133,z3,z4])],[(0,[z0,z1057,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1058,z6]),(0,[z41,z0,z2,z98,z4,z6]),(0,[z0,z2,z353,z4,z20,z6]),(0,[z0,z11,z2,z3,z16,z17])],[(0,[z0,z2,z3,z1059,z5,z6]),(0,[z0,z2,z3,z4,z1060,z6]),(0,[z0,z615,z3,z4,z162,z6]),(0,[z480,z2,z3,z4,z5,z185]),(0,[z0,z2,z3,z4,z925,z6]),(0,[z0,z11,z2,z3,z5,z890])],[(0,[z0,z11,z2,z3,z204,z5]),(0,[z0,z2,z3,z22,z4,z369]),(0,[z0,z2,z3,z4,z5,z1061]),(0,[z0,z268,z3,z4,z5,z12]),(0,[z0,z2,z3,z4,z1062,z5])]],
   [[(0,[z203,z69,z3,z4,z475,z6]),(0,[z0,z2,z3,z4,z5,z1063]),(0,[z41,z0,z2,z3,z81,z6])],[(0,[z2,z3,z22,z140,z4,z8]),(0,[z0,z2,z3,z4,z20,z80])],[(0,[z0,z2,z3,z4,z20,z24]),(0,[z0,z1064,z2,z3,z4,z5]),(0,[z0,z2,z60,z4,z746,z6]),(0,[z0,z489,z2,z3,z5,z85]),(0,[z65,z0,z2,z4,z606,z5]),(0,[z201,z2,z3,z4,z81,z6])],[(0,[z0,z2,z1065,z4,z5,z6]),(0,[z0,z2,z3,z4,z1066,z6]),(0,[z0,z2,z1067,z4,z5,z6])],[(0,[z0,z11,z2,z3,z18,z20]),(0,[z0,z2,z4,z283,z20,z6]),(0,[z285,z0,z3,z502,z193,z6])],[(0,[z47,z2,z3,z19,z8,z6])],[(0,[z0,z2,z3,z553,z20,z6]),(0,[z0,z489,z2,z3,z5,z146]),(0,[z0,z11,z2,z3,z5,z751])],[(0,[z0,z11,z2,z3,z664,z5])],[(0,[z47,z2,z3,z840,z5,z6]),(0,[z0,z2,z3,z142,z4,z5]),(0,[z0,z2,z3,z4,z20,z458])],[(0,[z0,z2,z3,z919,z4,z5]),(0,[z0,z58,z3,z4,z20,z6]),(0,[z0,z2,z3,z225,z20,z6]),(0,[z0,z2,z864,z3,z4,z20]),(0,[z0,z11,z2,z3,z4,z487]),(0,[z0,z2,z3,z4,z5,z1068])],[(0,[z0,z2,z3,z4,z20,z64]),(0,[z0,z11,z2,z3,z4,z377]),(0,[z1069,z2,z3,z4,z5,z6]),(0,[z0,z23,z3,z784,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1070])],[(0,[z211,z2,z3,z140,z4,z5]),(0,[z0,z2,z3,z4,z5,z1071])],[(0,[z203,z69,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z345,z108]),(0,[z0,z2,z3,z1072,z5,z6])],[(0,[z75,z2,z76,z22,z4,z5]),(0,[z548,z2,z3,z18,z5,z6]),(0,[z0,z11,z2,z3,z192,z5]),(0,[z0,z2,z1073,z3,z4,z5])],[(0,[z2,z3,z4,z8,z6,z267]),(0,[z0,z2,z3,z4,z1074,z6]),(0,[z0,z2,z1075,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z751])]],
   [[(0,[z0,z2,z3,z553,z5,z121]),(0,[z0,z2,z1076,z4,z5,z6]),(0,[z0,z58,z3,z4,z126,z6]),(0,[z0,z2,z3,z4,z1077,z6]),(0,[z0,z2,z3,z16,z82,z6]),(0,[z187,z2,z3,z4,z8,z6]),(0,[z201,z2,z3,z22,z4,z5])],[(0,[z0,z2,z1078,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1079]),(0,[z57,z2,z32,z451,z5,z6]),(0,[z0,z2,z3,z4,z126,z64]),(0,[z211,z2,z3,z4,z487,z185]),(0,[z0,z11,z2,z3,z626,z5]),(0,[z0,z2,z3,z4,z765,z6])],[(0,[z0,z11,z2,z98,z4,z5]),(0,[z285,z0,z3,z193,z20,z6]),(0,[z0,z11,z2,z3,z523,z5])],[(0,[z56,z2,z3,z4,z8,z6])],[(0,[z0,z2,z985,z4,z5,z6]),(0,[z2,z3,z4,z286,z20,z6]),(0,[z0,z11,z2,z3,z652,z5])],[(0,[z0,z2,z3,z4,z1080,z6]),(0,[z0,z2,z3,z4,z8,z403]),(0,[z211,z2,z3,z393,z5,z185]),(0,[z0,z2,z43,z4,z5,z53]),(0,[z0,z175,z2,z4,z374,z6])],[(0,[z0,z2,z3,z1081,z5,z6]),(0,[z240,z2,z3,z4,z5,z185])],[(0,[z0,z2,z1082,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z443]),(0,[z0,z2,z474,z3,z4,z209]),(0,[z0,z2,z3,z16,z364,z6])],[(0,[z605,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z1083,z4,z5]),(0,[z0,z2,z3,z4,z1084,z5])],[(0,[z2,z3,z4,z20,z8,z6]),(0,[z0,z2,z26,z4,z8,z6]),(0,[z0,z2,z1085,z4,z5,z6])],[(0,[z0,z28,z21,z4,z20,z6]),(0,[z211,z2,z3,z4,z5,z185]),(0,[z214,z2,z3,z4,z302,z59])],[(0,[z0,z28,z901,z4,z5,z6]),(0,[z0,z2,z1086,z4,z5,z6])],[(0,[z0,z2,z3,z4,z369,z6]),(0,[z0,z2,z26,z18,z5,z6]),(0,[z0,z2,z87,z4,z8,z6])],[(0,[z40,z2,z3,z18,z20,z6]),(0,[z613,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z241]),(0,[z0,z52,z3,z22,z4,z100])],[(0,[z0,z2,z1087,z4,z5,z6]),(0,[z0,z2,z3,z1088,z4,z5])],[(0,[z0,z11,z2,z3,z4,z126]),(0,[z0,z2,z998,z4,z5,z6])]],
   [[(0,[z0,z940,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z771])],[(0,[z0,z2,z558,z138,z5,z6]),(0,[z0,z11,z2,z26,z4,z8]),(0,[z0,z2,z3,z4,z1089,z6]),(0,[z0,z2,z4,z746,z5,z6])],[(0,[z0,z2,z3,z4,z208,z380]),(0,[z0,z2,z1090,z4,z8,z6])],[(0,[z0,z2,z3,z1091,z5,z6]),(0,[z0,z2,z786,z4,z20,z6]),(0,[z0,z2,z152,z3,z4,z202])],[(0,[z2,z826,z32,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z1092]),(0,[z240,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z1093,z6]),(0,[z191,z2,z3,z110,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1094]),(0,[z0,z11,z2,z298,z4,z5])],[(0,[z0,z397,z2,z14,z5,z6]),(0,[z0,z2,z3,z4,z8,z1095]),(0,[z0,z11,z2,z3,z82,z8]),(0,[z0,z2,z1096,z4,z5,z6]),(0,[z0,z2,z3,z22,z4,z1097]),(0,[z0,z2,z3,z4,z114,z559])],[(0,[z47,z2,z3,z19,z5,z6]),(0,[z240,z2,z3,z18,z5,z6]),(0,[z0,z2,z3,z4,z5,z1098])],[(0,[z0,z2,z1099,z4,z5,z6]),(0,[z0,z2,z3,z225,z5,z59])],[(0,[z0,z2,z376,z4,z5,z121]),(0,[z0,z11,z2,z3,z362,z5])],[(0,[z581,z2,z3,z19,z5,z6]),(0,[z1069,z11,z2,z3,z4,z5])],[(0,[z0,z58,z3,z4,z5,z64]),(0,[z0,z2,z3,z4,z208,z6]),(0,[z0,z489,z2,z3,z8,z6])],[(0,[z0,z2,z1100,z4,z5,z6]),(0,[z0,z2,z3,z4,z208,z273]),(0,[z0,z2,z3,z1101,z5,z6]),(0,[z0,z566,z2,z4,z118,z6]),(0,[z41,z0,z11,z2,z60,z3])],[(0,[z0,z2,z3,z4,z199,z6]),(0,[z0,z2,z3,z22,z4,z103])],[(0,[z0,z11,z2,z3,z5,z619])],[(0,[z0,z2,z3,z4,z1102,z6]),(0,[z161,z2,z3,z4,z5,z185]),(0,[z0,z2,z3,z4,z1103,z6])]],
   [[(0,[z0,z2,z3,z4,z1104,z6]),(0,[z1105,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z421,z6]),(0,[z0,z11,z2,z3,z4,z174]),(0,[z0,z11,z2,z3,z19,z8]),(0,[z40,z2,z3,z840,z5,z6]),(0,[z0,z2,z3,z4,z1106,z6]),(0,[z1107,z2,z3,z4,z5,z6])],[(0,[z0,z1108,z2,z3,z5,z6]),(0,[z41,z0,z11,z2,z26,z5])],[(0,[z134,z2,z3,z4,z20,z6]),(0,[z0,z11,z915,z3,z4,z5]),(0,[z0,z2,z3,z4,z1109,z6])],[(0,[z0,z2,z3,z150,z103,z6])],[(0,[z0,z2,z3,z4,z20,z121]),(0,[z0,z23,z3,z83,z5,z6])],[(0,[z0,z2,z376,z150,z5,z6]),(0,[z0,z11,z28,z21,z4,z5])],[(0,[z2,z3,z4,z19,z8,z6])],[(0,[z0,z2,z3,z4,z1110,z6]),(0,[z2,z3,z4,z801,z8,z6]),(0,[z0,z2,z3,z4,z20,z159]),(0,[z0,z2,z3,z4,z1111,z6])],[(0,[z2,z3,z4,z876,z8,z6]),(0,[z0,z11,z2,z26,z17,z5])],[(0,[z1031,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1112]),(0,[z57,z2,z32,z4,z5,z6]),(0,[z0,z2,z3,z22,z4,z261]),(0,[z2,z3,z4,z840,z5,z6]),(0,[z0,z2,z22,z4,z283,z5]),(0,[z0,z2,z1113,z3,z4,z6])],[(1,[z2,z3,z4,z5,z790]),(0,[z0,z1114,z2,z3,z4,z5]),(0,[z0,z2,z43,z775,z5,z6]),(1,[z0,z2,z3,z5,z751])],[(0,[z0,z2,z3,z4,z936,z8]),(0,[z0,z2,z3,z4,z20,z718]),(0,[z0,z52,z3,z4,z728,z6])],[(0,[z581,z0,z11,z2,z3,z5]),(0,[z0,z2,z3,z4,z1115,z6])],[(0,[z0,z2,z3,z4,z844,z6])],[(0,[z0,z175,z2,z4,z118,z6]),(0,[z0,z2,z3,z4,z114,z807])]],
   [[(0,[z0,z2,z3,z4,z1116,z6]),(0,[z0,z2,z3,z4,z1117,z6]),(0,[z0,z462,z2,z26,z4,z5]),(0,[z0,z2,z3,z22,z4,z1118])],[(0,[z0,z2,z536,z4,z5,z85])],[(0,[z0,z2,z3,z4,z8,z1119]),(0,[z0,z2,z3,z4,z5,z266]),(0,[z0,z2,z3,z22,z102,z5]),(0,[z0,z2,z3,z22,z16,z17])],[(0,[z0,z2,z3,z4,z475,z6]),(0,[z0,z2,z3,z4,z103,z390]),(0,[z0,z2,z3,z4,z1120,z6])],[(0,[z107,z11,z31,z3,z4,z5]),(0,[z285,z0,z284,z193,z5,z6]),(0,[z0,z157,z3,z4,z25,z6])],[(0,[z485,z0,z2,z3,z277,z6])],[(0,[z0,z2,z3,z4,z1121,z6]),(0,[z0,z2,z3,z4,z5,z1092]),(0,[z0,z2,z307,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1122]),(0,[z41,z0,z11,z2,z3,z5])],[(0,[z0,z2,z3,z4,z1123,z6]),(0,[z0,z2,z3,z4,z5,z918]),(0,[z0,z11,z2,z3,z599,z5])],[(0,[z0,z2,z3,z1124,z5,z6]),(0,[z0,z2,z43,z138,z22,z5]),(0,[z0,z2,z867,z4,z5,z6])],[(0,[z0,z1125,z2,z3,z451,z5]),(0,[z0,z2,z43,z138,z5,z6]),(0,[z0,z11,z2,z26,z5,z95])],[(0,[z285,z0,z3,z193,z8,z6]),(0,[z0,z2,z98,z4,z8,z917]),(0,[z0,z2,z1126,z4,z8,z6]),(0,[z0,z2,z298,z4,z5,z85]),(0,[z201,z2,z3,z4,z17,z6])],[(0,[z0,z11,z2,z3,z8,z95]),(0,[z0,z11,z2,z3,z650,z5]),(0,[z0,z2,z1127,z3,z4,z6]),(0,[z0,z2,z3,z22,z5,z751])],[(0,[z0,z2,z3,z4,z1128,z6]),(0,[z0,z2,z3,z1129,z5,z6]),(0,[z0,z2,z3,z1130,z5,z6])],[(0,[z0,z2,z3,z1131,z5,z6]),(0,[z0,z2,z3,z4,z8,z53]),(0,[z498,z2,z3,z4,z8,z6]),(0,[z0,z11,z2,z3,z478,z5])],[(0,[z0,z137,z3,z4,z5,z207]),(0,[z214,z2,z3,z4,z5,z790]),(0,[z201,z2,z3,z5,z71,z6])],[(0,[z0,z2,z3,z1132,z4,z5]),(0,[z0,z2,z3,z4,z1133,z6]),(0,[z0,z2,z1134,z4,z5,z6]),(0,[z0,z3,z4,z100,z728,z6]),(0,[z0,z2,z3,z22,z5,z73])]],
   [[(0,[z0,z2,z3,z22,z4,z5]),(0,[z0,z2,z4,z1135,z8,z6]),(0,[z0,z2,z1136,z3,z4,z6]),(0,[z0,z2,z3,z22,z531,z5]),(0,[z1105,z11,z2,z3,z4,z5])],[(0,[z0,z11,z2,z3,z4,z441]),(0,[z0,z2,z3,z4,z1137,z6]),(0,[z0,z2,z3,z4,z1138,z6])],[(0,[z0,z28,z21,z4,z8,z6]),(0,[z0,z11,z2,z3,z4,z143]),(0,[z0,z2,z3,z1139,z4,z5])],[(0,[z75,z2,z826,z4,z5,z6]),(0,[z11,z2,z3,z4,z20,z8])],[(0,[z0,z2,z3,z4,z5,z1140]),(0,[z0,z2,z3,z4,z336,z6]),(0,[z0,z2,z898,z4,z5,z6])],[(0,[z40,z2,z3,z18,z8,z6])],[(0,[z0,z2,z3,z4,z1141,z6]),(0,[z0,z2,z1142,z3,z4,z6])],[(0,[z0,z2,z376,z4,z8,z6]),(0,[z0,z2,z3,z4,z1143,z6])],[(0,[z0,z2,z144,z4,z5,z6]),(0,[z0,z1144,z2,z3,z4,z5]),(0,[z0,z2,z1145,z3,z4,z5])],[(0,[z0,z11,z2,z3,z678,z5]),(0,[z0,z2,z43,z9,z5,z6]),(0,[z0,z2,z301,z3,z4,z209]),(0,[z0,z1146,z2,z3,z4,z5])],[(0,[z0,z2,z74,z4,z103,z6]),(0,[z0,z2,z3,z4,z5,z1147]),(0,[z0,z2,z3,z1148,z5,z6]),(0,[z0,z11,z2,z3,z398,z5]),(0,[z0,z2,z3,z4,z360,z108])],[(0,[z0,z58,z3,z204,z5,z6]),(0,[z0,z11,z2,z3,z4,z208]),(0,[z0,z2,z3,z4,z5,z1149])],[(0,[z107,z31,z3,z4,z199,z6]),(0,[z0,z2,z3,z204,z5,z64]),(0,[z77,z2,z3,z4,z19,z8]),(0,[z214,z2,z3,z4,z8,z59]),(0,[z211,z2,z3,z4,z280,z185]),(0,[z0,z2,z3,z4,z1150,z6])],[(0,[z0,z2,z3,z5,z1151,z6]),(0,[z0,z2,z1152,z4,z5,z6]),(0,[z0,z2,z284,z4,z20,z6]),(0,[z285,z0,z3,z44,z193,z5])],[(0,[z0,z2,z3,z110,z225,z5])],[(0,[z0,z2,z29,z4,z8,z85]),(0,[z0,z2,z298,z26,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z20,z293])],[(0,[z0,z2,z778,z4,z20,z6]),(0,[z0,z309,z2,z26,z4,z5])],[(0,[z0,z2,z133,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z1153]),(0,[z0,z2,z3,z4,z876,z6])],[(0,[z0,z2,z4,z5,z1154,z6])],[(0,[z0,z2,z3,z1155,z5,z6]),(0,[z0,z275,z21,z4,z5,z6]),(0,[z0,z2,z3,z44,z4,z502])],[],[(0,[z0,z2,z3,z862,z4,z5]),(0,[z0,z2,z3,z4,z1156,z6]),(0,[z11,z2,z3,z19,z5,z8]),(0,[z0,z2,z3,z1157,z5,z6])],[(0,[z0,z2,z74,z4,z20,z6])],[(0,[z0,z2,z98,z4,z8,z6])],[(0,[z40,z11,z2,z3,z18,z5]),(0,[z0,z564,z2,z3,z22,z4])],[(0,[z0,z13,z2,z51,z14,z6])],[(0,[z0,z2,z3,z4,z5,z1158]),(0,[z0,z2,z1126,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1159]),(1,[z2,z3,z4,z876,z6]),(0,[z0,z2,z3,z4,z8,z631]),(0,[z0,z2,z60,z155,z4,z6]),(0,[z0,z2,z3,z5,z71,z751])],[(0,[z0,z965,z2,z3,z150,z5]),(0,[z0,z1160,z3,z4,z5,z6]),(0,[z0,z2,z3,z1161,z5,z6]),(0,[z0,z564,z2,z307,z3,z4]),(0,[z0,z2,z4,z5,z443,z85])],[(0,[z0,z2,z3,z553,z5,z390]),(0,[z0,z2,z3,z4,z20,z886]),(0,[z0,z11,z2,z26,z4,z20]),(0,[z0,z2,z3,z4,z5,z53])]],
   [[(0,[z0,z2,z3,z1162,z5,z6]),(0,[z0,z175,z2,z4,z283,z6]),(0,[z0,z11,z2,z3,z186,z5]),(0,[z0,z2,z3,z4,z5,z1163]),(0,[z0,z2,z3,z17,z734,z6])],[(0,[z0,z2,z3,z4,z1164,z6]),(0,[z0,z901,z3,z4,z5,z6]),(0,[z201,z2,z60,z3,z4,z6]),(0,[z41,z0,z2,z3,z22,z81]),(0,[z163,z0,z206,z3,z4,z5])],[],[(0,[z0,z1165,z2,z3,z4,z5]),(0,[z2,z3,z4,z8,z515,z6]),(0,[z0,z2,z298,z4,z8,z6]),(0,[z0,z2,z3,z784,z5,z6]),(0,[z0,z2,z3,z4,z5,z828])],[(0,[z0,z11,z2,z3,z20,z17]),(0,[z0,z2,z3,z4,z5,z790]),(0,[z0,z11,z2,z3,z4,z903])],[(0,[z0,z2,z3,z1166,z5,z6]),(0,[z0,z2,z98,z4,z8,z720]),(0,[z41,z0,z11,z2,z3,z360]),(0,[z1025,z2,z3,z22,z4,z5])],[(0,[z0,z2,z3,z1167,z5,z6]),(0,[z0,z2,z3,z225,z5,z185]),(0,[z0,z2,z3,z4,z1168,z6]),(0,[z0,z11,z2,z3,z343,z5])],[(0,[z0,z2,z3,z4,z103,z6]),(0,[z0,z2,z3,z4,z5,z759]),(0,[z0,z2,z3,z22,z328,z5])],[(0,[z0,z2,z353,z4,z8,z6]),(0,[z0,z2,z3,z4,z1169,z6]),(0,[z0,z52,z144,z4,z100,z6])],[(0,[z0,z137,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z441,z380])],[(0,[z0,z2,z1170,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z403])],[(0,[z219,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z6,z1171]),(0,[z240,z456,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1172]),(0,[z0,z2,z3,z4,z8,z80]),(0,[z485,z0,z11,z2,z3,z20]),(0,[z0,z2,z3,z4,z5,z443]),(0,[z0,z2,z3,z1173,z4,z5])],[(0,[z0,z137,z3,z4,z336,z6]),(0,[z0,z58,z3,z451,z5,z6]),(0,[z0,z2,z3,z204,z20,z6]),(0,[z0,z2,z3,z4,z8,z24]),(0,[z0,z2,z3,z1174,z5,z6]),(0,[z0,z2,z893,z4,z5,z6])],[(0,[z0,z2,z3,z451,z5,z64]),(0,[z0,z1175,z3,z4,z5,z6]),(0,[z0,z2,z3,z935,z4,z8]),(0,[z0,z2,z3,z4,z1176,z6]),(0,[z0,z2,z26,z4,z5,z6])],[(0,[z107,z31,z3,z22,z4,z5]),(0,[z0,z2,z3,z4,z5,z1177]),(0,[z0,z11,z2,z3,z19,z20]),(0,[z0,z2,z4,z283,z8,z6]),(0,[z0,z11,z175,z2,z4,z118])]],
   [[],[(0,[z0,z2,z3,z553,z8,z6]),(0,[z0,z1178,z2,z3,z4,z6]),(0,[z0,z2,z87,z4,z5,z6]),(0,[z0,z2,z3,z1179,z4,z5]),(0,[z0,z157,z3,z4,z25,z250])],[(0,[z0,z2,z3,z4,z441,z6]),(0,[z2,z3,z840,z19,z5,z6]),(0,[z0,z2,z3,z4,z5,z970]),(0,[z0,z2,z3,z4,z5,z241])],[(0,[z2,z76,z826,z4,z5,z6]),(0,[z0,z2,z3,z4,z441,z273]),(0,[z0,z2,z3,z4,z8,z458]),(0,[z180,z2,z3,z4,z876,z6]),(0,[z0,z11,z2,z298,z22,z5])],[(0,[z0,z58,z3,z4,z8,z6]),(0,[z0,z2,z3,z204,z126,z6]),(1,[z2,z3,z840,z5,z6]),(0,[z40,z2,z3,z22,z4,z8]),(0,[z0,z2,z3,z225,z8,z6]),(0,[z0,z2,z4,z8,z1154,z6]),(0,[z0,z2,z3,z5,z6,z802]),(0,[z0,z2,z806,z4,z5,z6]),(0,[z201,z52,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1180,z6])],[(0,[z0,z2,z3,z4,z5,z1181]),(0,[z0,z2,z3,z150,z20,z6]),(0,[z0,z1182,z2,z4,z5,z6]),(0,[z203,z69,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z5,z1183]),(0,[z0,z2,z3,z4,z8,z64]),(0,[z0,z2,z3,z4,z1184,z6]),(0,[z0,z2,z3,z5,z6,z1185])],[(0,[z0,z2,z74,z553,z5,z6]),(0,[z0,z2,z3,z1186,z5,z6])],[(0,[z0,z2,z1090,z4,z5,z6]),(0,[z0,z2,z3,z22,z204,z5]),(0,[z0,z2,z3,z1187,z4,z5]),(0,[z0,z175,z2,z22,z4,z118])],[(0,[z0,z2,z376,z4,z5,z390]),(0,[z0,z2,z3,z4,z5,z1188]),(0,[z0,z11,z2,z3,z4,z8]),(0,[z0,z11,z2,z3,z265,z20])],[],[(0,[z0,z2,z3,z1189,z5,z6]),(0,[z2,z3,z4,z265,z8,z6]),(0,[z0,z2,z3,z16,z17,z458])],[(0,[z0,z2,z98,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1095]),(0,[z0,z673,z3,z4,z5,z146]),(0,[z853,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z17,z6,z491])],[(0,[z2,z3,z4,z5,z185,z790]),(0,[z0,z2,z3,z4,z5,z1190])],[(0,[z0,z1125,z2,z3,z4,z5]),(0,[z0,z157,z410,z3,z4,z6])],[(0,[z0,z2,z3,z4,z336,z207]),(0,[z0,z11,z2,z3,z129,z5]),(0,[z41,z0,z2,z3,z202,z6])],[(0,[z0,z2,z3,z150,z5,z121]),(0,[z713,z31,z3,z4,z5,z6]),(0,[z0,z11,z2,z26,z18,z5]),(0,[z2,z98,z4,z20,z8,z6]),(0,[z0,z2,z3,z4,z5,z1191]),(0,[z0,z489,z2,z3,z22,z5])]],
   [[(0,[z2,z3,z4,z8,z576,z6]),(0,[z0,z3,z784,z193,z5,z6]),(0,[z0,z489,z2,z3,z5,z6]),(0,[z41,z0,z11,z2,z298,z5])],[(0,[z0,z2,z3,z22,z4,z487])],[(0,[z0,z2,z3,z22,z4,z377]),(0,[z0,z2,z3,z4,z5,z1192])],[(0,[z0,z2,z3,z4,z1193,z6])],[(0,[z0,z2,z3,z4,z20,z390]),(0,[z0,z52,z3,z4,z115,z6]),(0,[z1194,z2,z3,z4,z5,z6]),(0,[z0,z489,z2,z3,z5,z67])],[(0,[z0,z2,z3,z4,z5,z1195]),(0,[z0,z11,z2,z3,z225,z5]),(0,[z0,z772,z2,z3,z8,z6]),(0,[z0,z2,z3,z775,z5,z6])],[(0,[z0,z2,z1196,z4,z5,z6]),(0,[z0,z2,z3,z4,z1197,z6]),(0,[z2,z3,z4,z8,z590,z6]),(0,[z0,z2,z3,z5,z6,z1198]),(0,[z0,z11,z2,z1100,z4,z5])],[(0,[z0,z2,z3,z4,z1097,z6]),(0,[z0,z2,z1199,z3,z4,z5])],[(0,[z0,z2,z3,z1200,z5,z6]),(0,[z0,z2,z3,z4,z1201,z6])],[(0,[z0,z2,z3,z4,z1202,z6]),(0,[z0,z11,z2,z1067,z4,z5])],[],[(0,[z0,z11,z2,z3,z150,z5])],[(0,[z0,z2,z3,z712,z4,z5]),(0,[z0,z2,z3,z4,z5,z1203]),(0,[z41,z201,z2,z3,z81,z6])],[(0,[z0,z2,z1204,z3,z4,z6]),(0,[z0,z11,z2,z3,z393,z5]),(0,[z0,z2,z3,z4,z5,z1205])],[(0,[z0,z2,z3,z4,z5,z1206]),(0,[z2,z3,z4,z876,z5,z6])],[(0,[z0,z2,z3,z451,z20,z6]),(0,[z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z1207,z3,z4,z5]),(0,[z41,z201,z11,z2,z3,z5])]],
   [[(0,[z0,z1208,z2,z3,z4,z5]),(0,[z0,z1209,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z17,z5]),(0,[z0,z11,z2,z3,z653,z5])],[(0,[z0,z2,z4,z283,z5,z6]),(0,[z0,z2,z1210,z3,z4,z6])],[(0,[z180,z2,z3,z4,z441,z6])],[(0,[z0,z2,z3,z4,z1211,z6]),(0,[z11,z2,z3,z4,z19,z8]),(0,[z0,z2,z1212,z3,z4,z5]),(0,[z0,z56,z2,z26,z4,z5])],[(0,[z0,z1213,z3,z4,z5,z6]),(0,[z0,z2,z754,z4,z5,z6]),(0,[z0,z2,z98,z295,z4,z6]),(0,[z1214,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1215,z6]),(0,[z215,z0,z3,z4,z5,z628]),(0,[z0,z2,z3,z4,z1216,z6])],[(0,[z0,z2,z3,z8,z6,z1185]),(0,[z0,z2,z3,z4,z1217,z6]),(0,[z0,z2,z3,z4,z5,z458])],[(0,[z0,z2,z3,z4,z5,z1218]),(0,[z57,z137,z32,z4,z5,z6]),(0,[z0,z2,z3,z451,z126,z6]),(0,[z0,z2,z3,z4,z5,z1012]),(0,[z0,z2,z3,z4,z5,z1219]),(0,[z0,z2,z3,z4,z1220,z6])],[(0,[z0,z2,z3,z4,z1221,z6]),(0,[z0,z2,z3,z22,z4,z126]),(0,[z0,z2,z3,z4,z5,z1119]),(0,[z0,z11,z2,z3,z5,z574]),(0,[z65,z0,z2,z149,z4,z5])],[(0,[z2,z3,z4,z135,z8,z6])],[(0,[z0,z11,z2,z3,z4,z51])],[(0,[z0,z2,z3,z1222,z4,z5]),(0,[z0,z2,z4,z5,z780,z85])],[(0,[z0,z11,z2,z3,z4,z421])],[(0,[z0,z2,z408,z4,z55,z6]),(0,[z0,z123,z206,z3,z4,z5])],[(0,[z2,z98,z4,z19,z8,z6]),(0,[z0,z2,z3,z496,z4,z8])],[(0,[z40,z2,z3,z4,z8,z380]),(0,[z134,z2,z3,z4,z8,z6])],[(0,[z40,z2,z3,z22,z18,z5]),(0,[z0,z2,z98,z4,z5,z917]),(0,[z285,z0,z3,z193,z5,z6]),(0,[z0,z2,z26,z4,z5,z209])]],
   [[(0,[z0,z2,z3,z4,z8,z121]),(0,[z47,z2,z3,z19,z377,z6]),(0,[z0,z11,z2,z3,z110,z5]),(0,[z0,z11,z2,z3,z550,z5]),(0,[z65,z0,z2,z4,z5,z443]),(0,[z0,z11,z2,z3,z5,z95])],[(0,[z0,z11,z2,z3,z5,z78]),(0,[z40,z2,z3,z18,z5,z380])],[(0,[z0,z2,z3,z4,z5,z1223])],[(0,[z0,z2,z3,z4,z8,z159]),(0,[z180,z11,z2,z3,z4,z20]),(0,[z0,z11,z489,z2,z3,z5])],[(0,[z0,z2,z3,z4,z1224,z6]),(0,[z0,z2,z3,z1225,z5,z6])],[(0,[z0,z2,z74,z4,z5,z121]),(0,[z0,z2,z4,z1135,z5,z6]),(0,[z0,z2,z3,z204,z8,z6]),(0,[z0,z2,z3,z4,z5,z1032]),(0,[z2,z3,z4,z20,z242,z6]),(0,[z0,z2,z3,z4,z1226,z6]),(0,[z41,z0,z2,z3,z80,z81])],[(0,[z0,z2,z3,z4,z1227,z6])],[(0,[z57,z2,z32,z4,z5,z207]),(0,[z40,z2,z3,z4,z8,z6]),(0,[z0,z28,z21,z4,z5,z6])],[(0,[z0,z31,z74,z4,z5,z6]),(0,[z0,z137,z76,z4,z5,z6]),(0,[z40,z2,z3,z4,z8,z273]),(0,[z0,z2,z3,z4,z1228,z6]),(0,[z0,z2,z3,z496,z4,z20]),(0,[z0,z2,z3,z419,z17,z6]),(0,[z0,z2,z3,z4,z5,z1229]),(0,[z0,z2,z744,z4,z5,z6])],[(0,[z0,z2,z3,z1230,z4,z5]),(0,[z0,z2,z3,z22,z4,z174]),(0,[z0,z2,z144,z4,z5,z1068]),(0,[z0,z2,z3,z22,z5,z263])],[(0,[z40,z2,z3,z18,z5,z6]),(0,[z215,z0,z3,z4,z20,z146]),(0,[z0,z2,z3,z44,z4,z5])],[(0,[z11,z56,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z5,z1231]),(0,[z0,z3,z83,z784,z5,z6]),(0,[z0,z2,z1232,z4,z5,z6])],[(0,[z0,z2,z376,z4,z5,z6]),(0,[z47,z11,z2,z3,z19,z5])],[(0,[z0,z2,z3,z150,z8,z6]),(0,[z0,z2,z3,z4,z1233,z6]),(0,[z0,z2,z3,z840,z5,z6]),(0,[z581,z0,z2,z3,z151,z6]),(0,[z0,z104,z2,z3,z22,z5])],[(0,[z0,z2,z321,z3,z4,z209])],[(0,[z0,z2,z3,z4,z20,z380]),(0,[z0,z2,z1234,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z261,z6]),(0,[z0,z2,z3,z8,z1151,z6]),(0,[z0,z3,z4,z5,z6,z730]),(0,[z0,z11,z2,z3,z5,z632])],[(0,[z214,z2,z3,z4,z5,z59])],[(0,[z0,z2,z3,z4,z5,z1235]),(0,[z0,z11,z2,z284,z4,z5]),(0,[z0,z3,z4,z5,z759,z12]),(0,[z0,z2,z3,z4,z5,z1236])],[(0,[z0,z2,z3,z4,z1237,z6]),(0,[z0,z2,z3,z393,z20,z6])],[(0,[z0,z2,z3,z4,z994,z6]),(0,[z0,z2,z29,z4,z5,z85])],[(0,[z0,z1238,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z302]),(0,[z0,z2,z3,z4,z5,z1239])],[(0,[z0,z137,z60,z4,z5,z6]),(0,[z2,z3,z4,z5,z1240,z6]),(0,[z0,z2,z3,z1241,z5,z6])],[(0,[z0,z11,z2,z4,z283,z5]),(0,[z0,z2,z3,z1242,z5,z6]),(0,[z0,z123,z3,z4,z5,z538])],[(0,[z0,z2,z3,z4,z20,z6]),(0,[z0,z2,z1243,z4,z5,z6]),(0,[z0,z2,z3,z1244,z4,z5]),(0,[z0,z1245,z2,z3,z4,z5]),(0,[z0,z2,z29,z4,z5,z780])],[(0,[z0,z2,z3,z1246,z4,z5]),(0,[z0,z2,z3,z4,z1118,z6])],[],[(0,[z201,z2,z3,z4,z20,z6])],[(0,[z2,z3,z4,z704,z20,z6])],[(0,[z0,z2,z3,z4,z345,z327])],[(0,[z0,z2,z3,z1247,z5,z6]),(0,[z0,z2,z3,z1248,z5,z6]),(0,[z0,z2,z60,z4,z174,z6]),(0,[z0,z2,z3,z496,z4,z51]),(0,[z0,z2,z3,z1249,z4,z5]),(0,[z0,z2,z1096,z22,z4,z5])],[(0,[z0,z2,z3,z4,z126,z6]),(0,[z1250,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1251,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 503) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 503).take 506) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1009).take 378) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1387)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [503, 506, 378] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 139).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 139).take 155).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 294).take 149).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 443).take 69).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [139, 155, 149, 69] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38873

theorem PEqualNP.Outside.L_meta_38873 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4272611488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4272611488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38873.solve
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36356

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
  Nat.testBit (4278124200 * 2 ^ 32 + 4274585224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x50080c09b0614150#64 ++ 0x450080c09b061415#64 ++ 0xec281c1ff0e343fd#64 ++ 0xfec281c1ff0e343f#64 : BitVec 256),
   (0x20106224410e84a2#64 ++ 0x820106224410e84a#64 ++ 0xdc50e264633f8cff#64 ++ 0xbdc50e264633f8cf#64 : BitVec 256),
   (0x401b02869434d0c3#64 ++ 0x1401b02869434d0c#64 ++ 0xbb9f03879c3cf0cb#64 ++ 0x6bb9f03879c3cf0c#64 : BitVec 256),
   (0x80e001500a802a08#64 ++ 0x280e001500a802a0#64 ++ 0x7fe003f81fc0ff0f#64 ++ 0xe7fe003f81fc0ff0#64 : BitVec 256),
   (0x01edb4001ffb000c#64 ++ 0x301edb4001ffb000#64 ++ 0xf9fffc001fff0007#64 ++ 0x1f9fffc001fff000#64 : BitVec 256),
   (0x02f6dbff6000000f#64 ++ 0xc02f6dbff6000000#64 ++ 0xfaffffffe0000000#64 ++ 0xffaffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [8, 11]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [3, 13]⟩, ⟨.and, [9, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc001fff0007 0x1f9fffc001fff000

def z1 : W := mkw 0x02e699db2000000d 0x402e699db2000000 0xfafffd9b80000000 0x5fafffd9b8000000

def z2 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfaffffffe0000000 0xffaffffffe000000

def z3 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xdc50e264633f8cff 0xbdc50e264633f8cf

def z4 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbb9f03879c3cf0cb 0x6bb9f03879c3cf0c

def z5 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xec281c1ff0e343fd 0xfec281c1ff0e343f

def z6 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7fe003f81fc0ff0f 0xe7fe003f81fc0ff0

def z7 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0x801ffc07e0000000 0x1801ffc07e000000

def z8 : W := mkw 0x51edbc09bffb415c 0x751edbc09bffb415 0xfdfffc1fffff43ff 0xffdfffc1fffff43f

def z9 : W := mkw 0x010db400157b0004 0x1010db400157b000 0x801ffc00003f0000 0x1801ffc00003f000

def z10 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z11 : W := mkw 0xc0fb03d69eb4facb 0x3c0fb03d69eb4fac 0xffff03ff9ffcffcf 0xeffff03ff9ffcffc

def z12 : W := mkw 0x51092c09bffb4150 0x751092c09bffb415 0xed281c1fffff43ff 0xfed281c1fffff43f

def z13 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x466003f803c0ff0c 0xe466003f803c0ff0

def z14 : W := mkw 0x401202868004d0c3 0x0401202868004d0c 0x020003878000f0c8 0x6020003878000f0c

def z15 : W := mkw 0x41ffb6869fffd0cf 0x341ffb6869fffd0c 0xfbffff879ffff0cf 0x7fbffff879ffff0c

def z16 : W := mkw 0xc1ffb7d69ffffacf 0x3c1ffb7d69ffffac 0xffffffff9fffffcf 0xfffffffff9fffffc

def z17 : W := mkw 0x211df624557f84a6 0x9211df624557f84a 0xdc5ffe64633f8cff 0xbdc5ffe64633f8cf

def z18 : W := mkw 0x10000c0920410110 0x410000c092041011 0xec281c1fe0c30334 0xfec281c1fe0c3033

def z19 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x139703801c3cf0cb 0x0139703801c3cf0c

def z20 : W := mkw 0x01e5b4000fdb000c 0x301e5b4000fdb000 0x51f7fc000fdf0006 0x151f7fc000fdf000

def z21 : W := mkw 0x4008000090204040 0x0400800009020404 0xa8080007902040c9 0x6a8080007902040c

def z22 : W := mkw 0x010024000bcb0000 0x2010024000bcb000 0x0000000003c30004 0x00000000003c3000

def z23 : W := mkw 0x52f6dbffe000415f 0xc52f6dbffe000415 0xfeffffffe00043f8 0xffeffffffe00043f

def z24 : W := mkw 0x0010422440000002 0x8001042244000000 0xd850e26460000000 0xbd850e2646000000

def z25 : W := mkw 0x20002000010e84a0 0x020002000010e84a 0x04000000033f8cff 0x004000000033f8cf

def z26 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xe8281c1ff0c04300 0xfe8281c1ff0c0430

def z27 : W := mkw 0x0012028600000003 0x0001202860000000 0xba9f038780000000 0x6ba9f03878000000

def z28 : W := mkw 0x2216faaf610e84a7 0xc2216faaf610e84a 0xdc5ffe67e33f8cff 0xbdc5ffe67e33f8cf

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0x5c40026003008c0f 0xa5c40026003008c0

def z30 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xfc681e7ff3e3cfff 0xffc681e7ff3e3cff

def z31 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xc07ffc7fe0000000 0x9c07ffc7fe000000

def z32 : W := mkw 0x00e490000000000c 0x000e490000000000 0xf8fffc0000000000 0x1f8fffc000000000

def z33 : W := mkw 0x03ffffff7ffb000f 0xf03ffffff7ffb000 0xfbffffffffff0007 0xffbffffffffff000

def z34 : W := mkw 0x00e000000a800008 0x200e000000a80000 0x21a000001cc00000 0x021a000001cc0000

def z35 : W := mkw 0x21f5f2244f9e84ae 0xb21f5f2244f9e84a 0xddd7e2646f3f8cff 0xbddd7e2646f3f8cf

def z36 : W := mkw 0x5008040090614150 0x0500804009061415 0x0000000010c04300 0x00000000010c0430

def z37 : W := mkw 0x0009000014300000 0x1000900001430000 0xb99f00001c3c0003 0x0b99f00001c3c000

def z38 : W := mkw 0x401a02869024d0c3 0x0401a02869024d0c 0xaa0803879020f0c9 0x6aa0803879020f0c

def z39 : W := mkw 0x00e000000a800008 0x200e000000a80000 0x79e000001fc00007 0x079e000001fc0000

def z40 : W := mkw 0x02f6dbff6a80000f 0xe02f6dbff6a80000 0xfbffffffffc00007 0xffbffffffffc0000

def z41 : W := mkw 0x400b008294305041 0x1400b00829430504 0x238f01839c007000 0x4238f01839c00700

def z42 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfffffff81fffff0f 0xffffffff81fffff0

def z43 : W := mkw 0x8000015000002a00 0x08000015000002a0 0x060003f80000ff08 0xe060003f80000ff0

def z44 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x67e001f81fc07f04 0xc67e001f81fc07f0

def z45 : W := mkw 0x10000c0920410110 0x410000c092041011 0x6c201c1870c3433d 0xf6c201c1870c3433

def z46 : W := mkw 0x001b028614349083 0x1001b02861434908 0xbb9f03801c3cb003 0x0bb9f03801c3cb00

def z47 : W := mkw 0x10000c0920410110 0x410000c092041011 0x44201c1860c30334 0x944201c1860c3033

def z48 : W := mkw 0x50000809a0004150 0x450000809a000415 0x0400001fe00043f8 0xe0400001fe00043f

def z49 : W := mkw 0x03efbddb3ffb000d 0x703efbddb3ffb000 0xfbfffd9b9fff0007 0x5fbfffd9b9fff000

def z50 : W := mkw 0x00e0015000000008 0x000e001500000000 0x7be003f81c00f00b 0xe7be003f81c00f00

def z51 : W := mkw 0x0000080920000000 0x4000008092000000 0xe8281c1fe0000000 0xfe8281c1fe000000

def z52 : W := mkw 0x5008040090614150 0x0500804009061415 0x0400000010e343fd 0x00400000010e343f

def z53 : W := mkw 0x42ffdbfff430504f 0xd42ffdbfff430504 0xfbfffffffc007000 0xffbfffffffc00700

def z54 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xff9f0387fc3ff0ff 0xfff9f0387fc3ff0f

def z55 : W := mkw 0x0000000000000000 0x0000000000000000 0x138003800c00b002 0x0138003800c00b00

def z56 : W := mkw 0x0004900000000004 0x0000490000000000 0x801ffc0000000000 0x1801ffc000000000

def z57 : W := mkw 0x52fedffff061415f 0xc52fedffff061415 0xfefffffff0e343fd 0xffefffffff0e343f

def z58 : W := mkw 0x02f6d3f64000000f 0x802f6d3f64000000 0x12d7e3e000000000 0x012d7e3e00000000

def z59 : W := mkw 0xc0e801509aa06a48 0x2c0e801509aa06a4 0xffe803ff9fe0ffcf 0xeffe803ff9fe0ffc

def z60 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c20001810c0430d 0xe6c20001810c0430

def z61 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x939f03878c3cb0c2 0x0939f03878c3cb0c

def z62 : W := mkw 0x0013028604149083 0x1001302860414908 0x3b9703801c1cf00b 0x63b9703801c1cf00

def z63 : W := mkw 0x0009000014300000 0x1000900001430000 0x010000001c3c0003 0x0010000001c3c000

def z64 : W := mkw 0x50000809a0004150 0x450000809a000415 0x00000007e00000f0 0x000000007e00000f

def z65 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x801f0007803c00c0 0x0801f0007803c00c

def z66 : W := mkw 0x00e0015000000008 0x000e001500000000 0x4060007800000000 0x8406000780000000

def z67 : W := mkw 0x70186624d16fc5f2 0x870186624d16fc5f 0xdc50e26473ffcfff 0xbdc50e26473ffcff

def z68 : W := mkw 0x50000809a0004150 0x450000809a000415 0x6c20001ff0c043fd 0xe6c20001ff0c043f

def z69 : W := mkw 0x4009000094305040 0x1400900009430504 0x010000001c007000 0x0010000001c00700

def z70 : W := mkw 0x80e009592a802a08 0x680e009592a802a0 0xffe81fffffc0ff0f 0xfffe81fffffc0ff0

def z71 : W := mkw 0x0010020400048082 0x0001002040004808 0x10100200001c8002 0x010100200001c800

def z72 : W := mkw 0x42ffdbfff434d0cf 0xd42ffdbfff434d0c 0xfaffffffe03c00c0 0xffaffffffe03c00c

def z73 : W := mkw 0x20f4f224410e84ae 0x820f4f224410e84a 0xfcfffe64633f8cff 0xbfcfffe64633f8cf

def z74 : W := mkw 0x43ffffffffffd0cf 0xf43ffffffffffd0c 0xfbfffffffffff0cf 0xffbfffffffffff0c

def z75 : W := mkw 0x82f6dbff60002a0f 0xc82f6dbff60002a0 0xfeffffffe000ff08 0xffeffffffe000ff0

def z76 : W := mkw 0x501b0e8fb475d1d3 0x5501b0e8fb475d1d 0xffbf1f9ffcfff3ff 0xfffbf1f9ffcfff3f

def z77 : W := mkw 0x601b62a6d53ed4e3 0x9601b62a6d53ed4e 0xffdfe3e7ff3ffcff 0xfffdfe3e7ff3ffcf

def z78 : W := mkw 0x0000000000000000 0x0000000000000000 0x3b8003801c00f00b 0x63b8003801c00f00

def z79 : W := mkw 0x80f303d60e94ba8b 0x380f303d60e94ba8 0x13d703e00f1cbc02 0x013d703e00f1cbc0

def z80 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x80081c07e02300f0 0x180081c07e02300f

def z81 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x13c003e00f00bc02 0x013c003e00f00bc0

def z82 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xa81f0007903c40c9 0x6a81f0007903c40c

def z83 : W := mkw 0x0105b000051a0004 0x10105b000051a000 0x0017e000001c0000 0x00017e000001c000

def z84 : W := mkw 0xd1edbd59bffb6b5c 0x7d1edbd59bffb6b5 0xffffffffffffffff 0xffffffffffffffff

def z85 : W := mkw 0x400900009434d0c0 0x1400900009434d0c 0x010000001c3cf0cb 0x0010000001c3cf0c

def z86 : W := mkw 0x01e5b0000f9a000c 0x301e5b0000f9a000 0xf9fffc000f1c0002 0x1f9fffc000f1c000

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z88 : W := mkw 0x20104224400484a2 0x820104224400484a 0x9c100264603c8cfb 0xa9c100264603c8cf

def z89 : W := mkw 0x00e498092000000c 0x400e498092000000 0xf8fffc1fe0000000 0xff8fffc1fe000000

def z90 : W := mkw 0x02e691d20000000d 0x002e691d20000000 0x0287018000000000 0x0028701800000000

def z91 : W := mkw 0x82e699db2a802a0d 0x682e699db2a802a0 0x23af1d9b9cc07300 0x423af1d9b9cc0730

def z92 : W := mkw 0x60092000953ed4e0 0x160092000953ed4e 0x050000001f3ffcff 0x0050000001f3ffcf

def z93 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfeffffffe02300fd 0xffeffffffe02300f

def z94 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x1050e260031c8c02 0x01050e260031c8c0

def z95 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x20281c1b90c04300 0x420281c1b90c0430

def z96 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffc047fff00ff 0xbfdfffc047fff00f

def z97 : W := mkw 0xd0e80d59bae16b58 0x6d0e80d59bae16b5 0x7fe81ffb9fc0ff0f 0xe7fe81ffb9fc0ff0

def z98 : W := mkw 0x00e490000000000c 0x000e490000000000 0x20af1c0000000000 0x020af1c000000000

def z99 : W := mkw 0x00e491500000000c 0x000e491500000000 0xfafffff800000000 0xffafffff80000000

def z100 : W := mkw 0x601b62a6d53ed4e3 0x9601b62a6d53ed4e 0xbb9fe387fc3ff0fb 0x7bb9fe387fc3ff0f

def z101 : W := mkw 0x0000080920000000 0x4000008092000000 0xec281c1fe02300fd 0xfec281c1fe02300f

def z102 : W := mkw 0x42ffdbfff434d0cf 0xd42ffdbfff434d0c 0xfbfffffffc3cf0cb 0xffbfffffffc3cf0c

def z103 : W := mkw 0x01edb400157b000c 0x101edb400157b000 0xf8fffc00003f0000 0x1f8fffc00003f000

def z104 : W := mkw 0x8000000000002a00 0x08000000000002a0 0x040000000000ff08 0x0040000000000ff0

def z105 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x4260ffffe0000000 0xf4260ffffe000000

def z106 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x17c003f80f00ff0a 0xe17c003f80f00ff0

def z107 : W := mkw 0x80f203d60a802a0b 0x280f203d60a802a0 0xffff03ff9fc0ff0f 0xeffff03ff9fc0ff0

def z108 : W := mkw 0x21fdf6245fff84ae 0xb21fdf6245fff84a 0xf9fffc047fff00f7 0x1f9fffc047fff00f

def z109 : W := mkw 0x0013028604149083 0x1001302860414908 0x139703800c1cb002 0x0139703800c1cb00

def z110 : W := mkw 0x00e0015000000008 0x000e001500000000 0x7ae003f800000000 0xe7ae003f80000000

def z111 : W := mkw 0x02e4d9796000000c 0xc02e4d9796000000 0xe868fc7fe0000000 0xfe868fc7fe000000

def z112 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xb99ffc001c3f0003 0x1b99ffc001c3f000

def z113 : W := mkw 0x01ed94001ef1000c 0x301ed94001ef1000 0x21af1c001cc00000 0x021af1c001cc0000

def z114 : W := mkw 0xc0f203d68a84facb 0x2c0f203d68a84fac 0x7fe003ff9fc0ffcf 0xe7fe003ff9fc0ffc

def z115 : W := mkw 0x00e000000a800008 0x200e000000a80000 0x7de000181fc0430f 0xe7de000181fc0430

def z116 : W := mkw 0x0206988b20000005 0x40206988b2000000 0x000f1c0380000000 0x0000f1c038000000

def z117 : W := mkw 0x03ef9ddb3ef1000d 0x703ef9ddb3ef1000 0x23af1d9b9cc00000 0x423af1d9b9cc0000

def z118 : W := mkw 0xd0e80d59bae16b58 0x6d0e80d59bae16b5 0xffe81fffffe3ffff 0xfffe81fffffe3fff

def z119 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x52f7fff860000000 0x952f7fff86000000

def z120 : W := mkw 0x02124bff60000003 0xc02124bff6000000 0x020003ffe0000000 0xe020003ffe000000

def z121 : W := mkw 0x01e4b4000bcb000c 0x201e4b4000bcb000 0x4060fc0003c30004 0x14060fc0003c3000

def z122 : W := mkw 0x0012028600000003 0x0001202860000000 0x801f000780000000 0x0801f00078000000

def z123 : W := mkw 0x02e4d9796000000c 0xc02e4d9796000000 0xf8fffc7860000000 0x9f8fffc786000000

def z124 : W := mkw 0x00ed90001430000c 0x100ed90001430000 0xf9fffc001c3c0003 0x1f9fffc001c3c000

def z125 : W := mkw 0x521edeaff0614157 0xc521edeaff061415 0xec3ffc1ff0e343fd 0xfec3ffc1ff0e343f

def z126 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x811f00079c3cf0cb 0x0811f00079c3cf0c

def z127 : W := mkw 0x0012028600000003 0x0001202860000000 0xbb9f03879c00f00b 0x6bb9f03879c00f00

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc000004602300fd 0xbcc000004602300f

def z129 : W := mkw 0x501b0e8fb475d1d3 0x5501b0e8fb475d1d 0xbbbf1f9f9cfcf3cb 0x6bbbf1f9f9cfcf3c

def z130 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xc07ffc0003ff0004 0x1c07ffc0003ff000

def z131 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfbffffffef00bc02 0xffbffffffef00bc0

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0x6820001800000000 0xe682000180000000

def z133 : W := mkw 0x0000000000000000 0x0000000000000000 0x4400000060030034 0x9440000006003003

def z134 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xa1bffc001cff0000 0x1a1bffc001cff000

def z135 : W := mkw 0x800001500a802a00 0x2800001500a802a0 0x070003f81fc0ff0f 0xe070003f81fc0ff0

def z136 : W := mkw 0x0008040010610000 0x0000804001061000 0xec281c1810e3430d 0xfec281c1810e3430

def z137 : W := mkw 0x20106a2d610e84a2 0xc20106a2d610e84a 0xfc78fe7fe33f8cff 0xffc78fe7fe33f8cf

def z138 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x8010e004603f00f0 0x18010e004603f00f

def z139 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x23a001981cc07300 0x423a001981cc0730

def z140 : W := mkw 0x401202868004d0c3 0x0401202868004d0c 0x3b8003879c00f0cb 0x63b8003879c00f0c

def z141 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x04000264633f8cff 0xa04000264633f8cf

def z142 : W := mkw 0x0001000004100000 0x1000100000410000 0x119700000c1c0002 0x0119700000c1c000

def z143 : W := mkw 0x0008040010610000 0x0000804001061000 0xe8281c0010e30005 0x1e8281c0010e3000

def z144 : W := mkw 0x4008000090204040 0x0400800009020404 0x00000000102040c9 0x000000000102040c

def z145 : W := mkw 0x010924001ffb0000 0x3010924001ffb000 0x010000001fff0007 0x0010000001fff000

def z146 : W := mkw 0x001b028614300003 0x1001b02861430000 0xbb9f03879c3c0003 0x6bb9f03879c3c000

def z147 : W := mkw 0x210924001fff84a0 0x3210924001fff84a 0x050000001fff8cff 0x0050000001fff8cf

def z148 : W := mkw 0x50090c09b4714150 0x550090c09b471415 0xfdbf1c1ffcff43ff 0xffdbf1c1ffcff43f

def z149 : W := mkw 0x601262a6c10ed4e3 0x8601262a6c10ed4e 0xde50e3e7e33ffcff 0xfde50e3e7e33ffcf

def z150 : W := mkw 0x501b0a8fb434d1d3 0x5501b0a8fb434d1d 0xbf9f039ffc3cf3fb 0xebf9f039ffc3cf3f

def z151 : W := mkw 0x81e5b1500f9a2a0c 0x381e5b1500f9a2a0 0x13d7e3e00f1cbc02 0x013d7e3e00f1cbc0

def z152 : W := mkw 0x02e4d9796000000c 0xc02e4d9796000000 0x4060fc7860000000 0x94060fc786000000

def z153 : W := mkw 0x400b008294305041 0x1400b00829430504 0x000f000380000000 0x0000f00038000000

def z154 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x32fffffb80000000 0x432fffffb8000000

def z155 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xffdf03e79f3cfccf 0xeffdf03e79f3cfcc

def z156 : W := mkw 0x00f203d60000000b 0x000f203d60000000 0xfaff03ff80000000 0xefaff03ff8000000

def z157 : W := mkw 0x02f6d3f64000000f 0x802f6d3f64000000 0xfaffffe000000000 0x1faffffe00000000

def z158 : W := mkw 0x20102204010e84a2 0x020102204010e84a 0x9c100204033f8cff 0x29c100204033f8cf

def z159 : W := mkw 0x01edbc093ffb000c 0x701edbc093ffb000 0xf9fffc1fffff0007 0xff9fffc1fffff000

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc40026463238cff 0xbdc40026463238cf

def z161 : W := mkw 0x0000080920000000 0x4000008092000000 0x0000001fe0000000 0xe0000001fe000000

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400026000008c08 0xa0400026000008c0

def z163 : W := mkw 0x03f6ffff6bcb000f 0xe03f6ffff6bcb000 0xfaffffffe3c30004 0xffaffffffe3c3000

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000000002300fd 0x004000000002300f

def z165 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfdfffc781fff0f07 0x9fdfffc781fff0f0

def z166 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfeffffffe3c00f04 0xffeffffffe3c00f0

def z167 : W := mkw 0xc2ffdbfffeb4facf 0xfc2ffdbfffeb4fac 0xfffffffffffcffcf 0xffffffffffffcffc

def z168 : W := mkw 0x52ecdd79f061415c 0xc52ecdd79f061415 0xec68fc7ff0e343fd 0xfec68fc7ff0e343f

def z169 : W := mkw 0x401302868414d0c3 0x1401302868414d0c 0x139703878c1cf0ca 0x6139703878c1cf0c

def z170 : W := mkw 0xd0e80d59bae16b58 0x6d0e80d59bae16b5 0xefa81d9ffce373fd 0xfefa81d9ffce373f

def z171 : W := mkw 0x20104224400484a2 0x820104224400484a 0x0400026460008cf8 0xa0400026460008cf

def z172 : W := mkw 0x81e4b5500bcb2a0c 0x281e4b5500bcb2a0 0x4460fc7803c30f04 0x94460fc7803c30f0

def z173 : W := mkw 0x82124bff60002a03 0xc82124bff60002a0 0x060003ffe000ff08 0xe060003ffe000ff0

def z174 : W := mkw 0x20002000010e84a0 0x020002000010e84a 0x5c400260033f8cff 0xa5c400260033f8cf

def z175 : W := mkw 0x00e490000a80000c 0x200e490000a80000 0xf9fffc001fc00007 0x1f9fffc001fc0000

def z176 : W := mkw 0x0010020400048082 0x0001002040004808 0x98100204003c80cb 0x298100204003c80c

def z177 : W := mkw 0xd0e80d59bae16b58 0x6d0e80d59bae16b5 0x23a81d9b9cc07300 0x423a81d9b9cc0730

def z178 : W := mkw 0x72fefffff16fc5ff 0xc72fefffff16fc5f 0xfefffffff3ffcfff 0xffefffffff3ffcff

def z179 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000003008c0f 0x00400000003008c0

def z180 : W := mkw 0x41edb4009ffb404c 0x341edb4009ffb404 0xf9fffc079fff40cf 0x7f9fffc079fff40c

def z181 : W := mkw 0x02e4d9796000000c 0xc02e4d9796000000 0x7ae0fff860000000 0xf7ae0fff86000000

def z182 : W := mkw 0x20006020410a0420 0x820006020410a042 0x5c40e26063038c3f 0xb5c40e26063038c3

def z183 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x9810e204603f80fb 0x39810e204603f80f

def z184 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xffbf039f9cfcf3cf 0xeffbf039f9cfcf3c

def z185 : W := mkw 0x021243f640000003 0x8021243f64000000 0x020003e000000000 0x0020003e00000000

def z186 : W := mkw 0x21fdf6245fff84ae 0xb21fdf6245fff84a 0xfdfffe647fff8cff 0xbfdfffe647fff8cf

def z187 : W := mkw 0x421fdaaff434d0c7 0xd421fdaaff434d0c 0x801ffc07e03c00c0 0x1801ffc07e03c00c

def z188 : W := mkw 0x03edfd797ffb000c 0xf03edfd797ffb000 0xf9fffc787fff0007 0x9f9fffc787fff000

def z189 : W := mkw 0x01e5b0000f9a000c 0x301e5b0000f9a000 0x11d7e0000f1c0002 0x011d7e0000f1c000

def z190 : W := mkw 0x03ffffff757b000f 0xd03ffffff757b000 0xfaffffffe03f0000 0xffaffffffe03f000

def z191 : W := mkw 0x22f6fbff610e84af 0xc22f6fbff610e84a 0xfeffffffe33f8cff 0xffeffffffe33f8cf

def z192 : W := mkw 0x0010020400048082 0x0001002040004808 0x80100004003c00c0 0x080100004003c00c

def z193 : W := mkw 0x01e5b0000f9a000c 0x301e5b0000f9a000 0x79f7e0001fdc0007 0x079f7e0001fdc000

def z194 : W := mkw 0x42f6dbffe004d0cf 0xc42f6dbffe004d0c 0xfaffffffe000f0c8 0xffaffffffe000f0c

def z195 : W := mkw 0x501b06869475d1d3 0x1501b06869475d1d 0xbf9f03879cfff3ff 0x6bf9f03879cfff3f

def z196 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xfc70e27c73ffcfff 0xffc70e27c73ffcff

def z197 : W := mkw 0x510924009ffb4150 0x3510924009ffb415 0x050000001fff43ff 0x0050000001fff43f

def z198 : W := mkw 0x20006020410a0420 0x820006020410a042 0x4440e06063030c34 0x94440e06063030c3

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0xd850e00000000000 0x1d850e0000000000

def z200 : W := mkw 0x50000809a0004150 0x450000809a000415 0xec281c1fe00043f8 0xfec281c1fe00043f

def z201 : W := mkw 0xc0eb01d29eb07a49 0x3c0eb01d29eb07a4 0x7fef03fb9fc0ff0f 0xe7fef03fb9fc0ff0

def z202 : W := mkw 0x02e699db2000000d 0x402e699db2000000 0xeaaf1d9fe0000000 0xfeaaf1d9fe000000

def z203 : W := mkw 0x02e699db2000000d 0x402e699db2000000 0x22af1d9b80000000 0x422af1d9b8000000

def z204 : W := mkw 0x00e0015000000008 0x000e001500000000 0x7ee003f803008c0f 0xe7ee003f803008c0

def z205 : W := mkw 0xa0f063744b8eaeaa 0xaa0f063744b8eaea 0xfff0e3fc7fffffff 0xffff0e3fc7ffffff

def z206 : W := mkw 0x0010020400000002 0x0001002040000000 0x9810020400000000 0x2981002040000000

def z207 : W := mkw 0x0010422440000002 0x8001042244000000 0xdc50e26463008c0f 0xbdc50e26463008c0

def z208 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x4460007803c00f04 0x84460007803c00f0

def z209 : W := mkw 0x800000000a802a00 0x2800000000a802a0 0x050000001fc0ff0f 0x0050000001fc0ff0

def z210 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0xffe003fc7fe3ffff 0xfffe003fc7fe3fff

def z211 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x92dfffe7e0000000 0x192dfffe7e000000

def z212 : W := mkw 0x80e491500a802a0c 0x280e491500a802a0 0xfffffff81fc0ff0f 0xffffffff81fc0ff0

def z213 : W := mkw 0x41ffb2869fbed0cf 0x341ffb2869fbed0c 0xbbdfe3879f3cf0cb 0x6bbdfe3879f3cf0c

def z214 : W := mkw 0x02f6fbff610a000f 0xc02f6fbff610a000 0xfaffffffe33f0007 0xffaffffffe33f000

def z215 : W := mkw 0x01e494000ac1000c 0x201e494000ac1000 0x00201c0000c00000 0x000201c0000c0000

def z216 : W := mkw 0x00e000000a800008 0x200e000000a80000 0x11c000000f000002 0x011c000000f00000

def z217 : W := mkw 0x401b42a6d434d0c3 0x9401b42a6d434d0c 0xfbdfe3e7fc3cf0cb 0xffbdfe3e7fc3cf0c

def z218 : W := mkw 0x42124bffe004d0c3 0xc42124bffe004d0c 0x020003ffe000f0c8 0xe020003ffe000f0c

def z219 : W := mkw 0x52ffdffff475d1df 0xd52ffdffff475d1d 0xfffffffffcfff3ff 0xffffffffffcfff3f

def z220 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x33e003f81fc0ff02 0x433e003f81fc0ff0

def z221 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfefffffff0c0430d 0xffefffffff0c0430

def z222 : W := mkw 0x60196224d53ed4e2 0x960196224d53ed4e 0xdd50e2647f3ffcff 0xbdd50e2647f3ffcf

def z223 : W := mkw 0xd0080c09bae16b50 0x6d0080c09bae16b5 0xed281c1fffe3ffff 0xfed281c1fffe3fff

def z224 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xa8081c07f02340f9 0x7a8081c07f02340f

def z225 : W := mkw 0x401202868004d0c3 0x0401202868004d0c 0xba9f03878000f0c8 0x6ba9f03878000f0c

def z226 : W := mkw 0xd0e805509ae16b58 0x2d0e805509ae16b5 0x7fe003f81fe3ffff 0xe7fe003f81fe3fff

def z227 : W := mkw 0x70186e2df16fc5f2 0xc70186e2df16fc5f 0xfc78fe7ff3ffcfff 0xffc78fe7ff3ffcff

def z228 : W := mkw 0x00e0000000000008 0x000e000000000000 0x78e0000000000000 0x078e000000000000

def z229 : W := mkw 0x10080c0930610110 0x410080c093061011 0xec281c1870e30335 0x9ec281c1870e3033

def z230 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x64281c1bf0c34334 0xd64281c1bf0c3433

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x7c60027813c0cf0f 0xe7c60027813c0cf0

def z232 : W := mkw 0x01ed94001ef1000c 0x301ed94001ef1000 0xf9fffc001cc00000 0x1f9fffc001cc0000

def z233 : W := mkw 0x01e4b4000bcb000c 0x201e4b4000bcb000 0xd870fc0003ff0007 0x1d870fc0003ff000

def z234 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x5c60027803c08f0f 0xa5c60027803c08f0

def z235 : W := mkw 0x90e00d592ac12b18 0x690e00d592ac12b1 0x7fe01ff87fc3ff3f 0xf7fe01ff87fc3ff3

def z236 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xffd0e3e47f3ffcff 0xfffd0e3e47f3ffcf

def z237 : W := mkw 0x00002000010a0000 0x000002000010a000 0x00000000033f0007 0x000000000033f000

def z238 : W := mkw 0x0000000000048080 0x0000000000004808 0x00000000003c80cb 0x000000000003c80c

def z239 : W := mkw 0x010db4001ffb0004 0x3010db4001ffb000 0x811ffc001fff0007 0x1811ffc001fff000

def z240 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xa2bffd9fe0000000 0x5a2bffd9fe000000

def z241 : W := mkw 0x00002000010a0000 0x000002000010a000 0xd850e000033f0007 0x1d850e000033f000

def z242 : W := mkw 0x0010422440000002 0x8001042244000000 0x8010e00460000000 0x18010e0046000000

def z243 : W := mkw 0x501a0e8fb065d1d3 0x4501a0e8fb065d1d 0xee281f9ff0e3f3fd 0xfee281f9ff0e3f3f

def z244 : W := mkw 0x10000c0920410110 0x410000c092041011 0x00001c0060030030 0x100001c006003003

def z245 : W := mkw 0x03f7fbff6f9a000f 0xf03f7fbff6f9a000 0xfbffffffef1c0002 0xffbffffffef1c000

def z246 : W := mkw 0x00092000153a0000 0x100092000153a000 0xf9dfe0001f3f0007 0x1f9dfe0001f3f000

def z247 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x00081c0380000000 0x000081c038000000

def z248 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xe83ffc0010ff0005 0x1e83ffc0010ff000

def z249 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfbfffd981fff7307 0x5fbfffd981fff730

def z250 : W := mkw 0x00e000000a800008 0x200e000000a80000 0x7de002601fc08c0f 0xa7de002601fc08c0

def z251 : W := mkw 0x50000c09a0414150 0x450000c09a041415 0x44201c1fe0c343fc 0xf44201c1fe0c343f

def z252 : W := mkw 0x01fdf6245ffb000e 0xb01fdf6245ffb000 0xf9fffe647fff0007 0xbf9fffe647fff000

def z253 : W := mkw 0x0000000000000000 0x0000000000000000 0x180002000000800b 0x2180002000000800

def z254 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xd85ffc00033f0007 0x1d85ffc00033f000

def z255 : W := mkw 0x0019020414348082 0x1001902041434808 0xb99f02041c3c80cb 0x2b99f02041c3c80c

def z256 : W := mkw 0x401202868004d0c3 0x0401202868004d0c 0x9a100387803cf0cb 0x69a100387803cf0c

def z257 : W := mkw 0x601b42a6d434d4e3 0x9601b42a6d434d4e 0xbf9f03e7fc3cfcfb 0xebf9f03e7fc3cfcf

def z258 : W := mkw 0x20104224400484a2 0x820104224400484a 0xcc00026460238cfd 0xbcc00026460238cf

def z259 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x21af1c001fff0007 0x021af1c001fff000

def z260 : W := mkw 0x12f6dfff6041011f 0xc12f6dfff6041011 0xfeffffffe0c30334 0xffeffffffe0c3033

def z261 : W := mkw 0x20f062244b8e84aa 0xa20f062244b8e84a 0xfdf0e2647fff8cff 0xbfdf0e2647fff8cf

def z262 : W := mkw 0x5008040090614150 0x0500804009061415 0xac08000790e343fd 0x6ac08000790e343f

def z263 : W := mkw 0x0013028604149083 0x1001302860414908 0xbb9f03878c1cb002 0x6bb9f03878c1cb00

def z264 : W := mkw 0x40fb03d69434d0cb 0x140fb03d69434d0c 0xfbff03ff9c3cf0cb 0xefbff03ff9c3cf0c

def z265 : W := mkw 0x00f043744000000a 0x800f043744000000 0xfaf0e3fc60000000 0xffaf0e3fc6000000

def z266 : W := mkw 0x02e499592000000c 0x402e499592000000 0x00201c1800000000 0x000201c180000000

def z267 : W := mkw 0x0008040010610000 0x0000804001061000 0x80081c0000230000 0x180081c000023000

def z268 : W := mkw 0x510dbc09b57b4154 0x5510dbc09b57b415 0xec3ffc1ff0ff43fd 0xfec3ffc1ff0ff43f

def z269 : W := mkw 0x03fff7f65ffb000f 0xb03fff7f65ffb000 0xfbffffe01fff0007 0x1fbffffe01fff000

def z270 : W := mkw 0x501b0e8fb475d1d3 0x5501b0e8fb475d1d 0xbb9f1f87fc3ff0fb 0x7bb9f1f87fc3ff0f

def z271 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xd850e260033f8c07 0x1d850e260033f8c0

def z272 : W := mkw 0x02124bff60000003 0xc02124bff6000000 0xea281fffe0000000 0xfea281fffe000000

def z273 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x1450e260033f8cff 0x01450e260033f8cf

def z274 : W := mkw 0x800000000a802a00 0x2800000000a802a0 0x6d2000181fc0ff0f 0xe6d2000181fc0ff0

def z275 : W := mkw 0x4008000090204040 0x0400800009020404 0xec080007f02340fd 0xfec080007f02340f

def z276 : W := mkw 0xa1fdf7745fffaeae 0xba1fdf7745fffaea 0xfffffffc7fffffff 0xffffffffc7ffffff

def z277 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x22af1fffe0000000 0xe22af1fffe000000

def z278 : W := mkw 0x401b2286953ed0c3 0x1401b2286953ed0c 0xfbdfe3879f3ff0cf 0x7fbdfe3879f3ff0c

def z279 : W := mkw 0x50184e2df0614152 0xc50184e2df061415 0xfc78fe7ff0e343fd 0xffc78fe7ff0e343f

def z280 : W := mkw 0x201262a6410e84a3 0x8201262a6410e84a 0xfedfe3e7e33f8cff 0xffedfe3e7e33f8cf

def z281 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xa8281c1f90e043c9 0x6a8281c1f90e043c

def z282 : W := mkw 0x03e4fd796bcb000c 0xe03e4fd796bcb000 0x4060fc7863c30004 0x94060fc7863c3000

def z283 : W := mkw 0x01092400157b0000 0x101092400157b000 0x00000000003f0000 0x000000000003f000

def z284 : W := mkw 0xe0fb63f6dfbefeeb 0xbe0fb63f6dfbefee 0xffffe3ffffffffff 0xfffffe3fffffffff

def z285 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xffa81f9ffce3f3ff 0xfffa81f9ffce3f3f

def z286 : W := mkw 0x400900009434d0c0 0x1400900009434d0c 0x00000000003c00c0 0x000000000003c00c

def z287 : W := mkw 0x50180e0db065c1d2 0x450180e0db065c1d 0xfc381e1ff0ffc3ff 0xffc381e1ff0ffc3f

def z288 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x0020001800c00300 0x00020001800c0030

def z289 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xa39f01879c3c70c0 0x4a39f01879c3c70c

def z290 : W := mkw 0x0009040014710000 0x1000904001471000 0xf9bf1c001cff0007 0x1f9bf1c001cff000

def z291 : W := mkw 0x0012028600048083 0x0001202860004808 0xba9f0387803c80cb 0x6ba9f0387803c80c

def z292 : W := mkw 0x401b028694305043 0x1401b02869430504 0xbb9f03879c007000 0x6bb9f03879c00700

def z293 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xe8281c07f0e300f5 0x1e8281c07f0e300f

def z294 : W := mkw 0xa01043744004aea2 0x8a01043744004aea 0x060003fc6000fff8 0xe060003fc6000fff

def z295 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x9050e264633f8cf2 0x19050e264633f8cf

def z296 : W := mkw 0x00080c0930610000 0x400080c093061000 0xe8281c1ff0e30005 0xfe8281c1ff0e3000

def z297 : W := mkw 0x00002000010a0000 0x000002000010a000 0xdc50e004633f00ff 0xbdc50e004633f00f

def z298 : W := mkw 0x0000000000000000 0x0000000000000000 0x1040026003008c02 0x01040026003008c0

def z299 : W := mkw 0x020209db20000001 0x4020209db2000000 0x0200019b80000000 0x40200019b8000000

def z300 : W := mkw 0x410924009fffd0c0 0x3410924009fffd0c 0x010000001ffff0cf 0x0010000001ffff0c

def z301 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfbffffe01fffbc07 0x1fbffffe01fffbc0

def z302 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfeffffffe3008c0f 0xffeffffffe3008c0

def z303 : W := mkw 0xa0f063744b8eaeaa 0xaa0f063744b8eaea 0xdfd0e3e46f3fbcff 0xbdfd0e3e46f3fbcf

def z304 : W := mkw 0x50ec9c09b061415c 0x450ec9c09b061415 0xfcfffc1ff0e343fd 0xffcfffc1ff0e343f

def z305 : W := mkw 0x20104224400484a2 0x820104224400484a 0x0000026000008c00 0x00000026000008c0

def z306 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x821f0387803cf0c8 0x6821f0387803cf0c

def z307 : W := mkw 0x80f043744a802a0a 0xa80f043744a802a0 0xfff0e3fc7fc0ff0f 0xffff0e3fc7fc0ff0

def z308 : W := mkw 0x02e6d9fb6000000d 0xc02e6d9fb6000000 0x62effdfbe0000000 0xd62effdfbe000000

def z309 : W := mkw 0x601b62a6d53ed4e3 0x9601b62a6d53ed4e 0x801fe007e03f00f0 0x1801fe007e03f00f

def z310 : W := mkw 0x00e490000000000c 0x000e490000000000 0x4060fc0000000000 0x14060fc000000000

def z311 : W := mkw 0x211966245fff84a2 0xb211966245fff84a 0xdd50e2647fff8cff 0xbdd50e2647fff8cf

def z312 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xb99f00079c3c00c3 0x0b99f00079c3c00c

def z313 : W := mkw 0xd2fedffffae16b5f 0xed2fedffffae16b5 0xffffffffffe3ffff 0xfffffffffffe3fff

def z314 : W := mkw 0xa0f063744b8eaeaa 0xaa0f063744b8eaea 0x13d0e3e00f1cbc02 0x013d0e3e00f1cbc0

def z315 : W := mkw 0x03f7f3f64f9a000f 0xb03f7f3f64f9a000 0x13d7e3e00f1c0002 0x013d7e3e00f1c000

def z316 : W := mkw 0x521a4ffff0614153 0xc521a4ffff061415 0xee281ffff0e343fd 0xfee281ffff0e343f

def z317 : W := mkw 0x400b008294305041 0x1400b00829430504 0xbb9f01839c3c7003 0x4bb9f01839c3c700

def z318 : W := mkw 0x2216faaf610e84a7 0xc2216faaf610e84a 0x801ffc07e03f00f0 0x1801ffc07e03f00f

def z319 : W := mkw 0x0204d82960000004 0xc0204d8296000000 0x0000fc0060000000 0x10000fc006000000

def z320 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfbfffffffcc07300 0xffbfffffffcc0730

def z321 : W := mkw 0x8000015000002a00 0x08000015000002a0 0x3f8003f81c00ff0b 0xe3f8003f81c00ff0

def z322 : W := mkw 0x510dbc09b57b4154 0x5510dbc09b57b415 0x801ffc07e03f00f0 0x1801ffc07e03f00f

def z323 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7be003f81cc07300 0xe7be003f81cc0730

def z324 : W := mkw 0x00e000000a800008 0x200e000000a80000 0x4060000003c00004 0x04060000003c0000

def z325 : W := mkw 0x22124bff600484a3 0xc22124bff600484a 0x060003ffe0008cf8 0xe060003ffe0008cf

def z326 : W := mkw 0x40080809b0204040 0x440080809b020404 0xe8281c1ff02040c9 0xfe8281c1ff02040c

def z327 : W := mkw 0x401b0a8fb434d0c3 0x5401b0a8fb434d0c 0xfbbf1f9ffc3cf0cb 0xffbbf1f9ffc3cf0c

def z328 : W := mkw 0x5008040090614150 0x0500804009061415 0x00000000002300f0 0x000000000002300f

def z329 : W := mkw 0x601b62a6d53ed4e3 0x9601b62a6d53ed4e 0xbbdfe3e79f3cfccb 0x6bbdfe3e79f3cfcc

def z330 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x6c281c1b90c0430d 0xe6c281c1b90c0430

def z331 : W := mkw 0x80e901501eb02a08 0x380e901501eb02a0 0xffff03f81ffcff0f 0xeffff03f81ffcff0

def z332 : W := mkw 0x52ee9ddbb061415d 0x452ee9ddbb061415 0x22af1d9b90c04300 0x422af1d9b90c0430

def z333 : W := mkw 0x401802049024c0c2 0x0401802049024c0c 0xb8180207903cc0cb 0x6b8180207903cc0c

def z334 : W := mkw 0xd0000959a0006b50 0x4d0000959a0006b5 0x060003ffe000fff8 0xe060003ffe000fff

def z335 : W := mkw 0x00f4d2244000000e 0x800f4d2244000000 0xf8fffe6460000000 0xbf8fffe646000000

def z336 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7be001981fc07307 0x47be001981fc0730

def z337 : W := mkw 0x20186624516f84a2 0x820186624516f84a 0xfc78fe6473ff8cff 0xbfc78fe6473ff8cf

def z338 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xd850e264603f00f0 0xbd850e264603f00f

def z339 : W := mkw 0x82e4d9796a802a0c 0xe82e4d9796a802a0 0x4460fc7863c00f04 0x94460fc7863c00f0

def z340 : W := mkw 0x0000000000000000 0x0000000000000000 0x88000004002000c9 0x288000004002000c

def z341 : W := mkw 0x4002008280005041 0x0400200828000504 0x0200018380007000 0x4020001838000700

def z342 : W := mkw 0xc0e901509eb4fac8 0x3c0e901509eb4fac 0x7fe003f81ffcffcf 0xe7fe003f81ffcffc

def z343 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x8410e264603f8cf8 0xb8410e264603f8cf

def z344 : W := mkw 0x02f7d3f64414908f 0x902f7d3f64414908 0x13d7e3e00c1cb002 0x013d7e3e00c1cb00

def z345 : W := mkw 0x010924001ffb0000 0x3010924001ffb000 0xb99f00001fff0007 0x0b99f00001fff000

def z346 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x339f03839c1cf002 0x4339f03839c1cf00

def z347 : W := mkw 0x51edbc09bffb415c 0x751edbc09bffb415 0xf9fffc1b9fff4307 0x5f9fffc1b9fff430

def z348 : W := mkw 0x0008040010610000 0x0000804001061000 0x0000000010e30005 0x00000000010e3000

def z349 : W := mkw 0x80e021500b8a2a08 0x280e021500b8a2a0 0xfff0e3f81fffff0f 0xffff0e3f81fffff0

def z350 : W := mkw 0x70184e2df065c5f2 0xc70184e2df065c5f 0xec281e7ff0e3cffd 0xfec281e7ff0e3cff

def z351 : W := mkw 0x52ee9ddbb061415d 0x452ee9ddbb061415 0xeeaf1d9ff0e343fd 0xfeeaf1d9ff0e343f

def z352 : W := mkw 0x800000000a802a00 0x2800000000a802a0 0x3f8003801fc0ff0f 0x63f8003801fc0ff0

def z353 : W := mkw 0x00e804001ae10008 0x200e804001ae1000 0xf9e81c001fe30007 0x1f9e81c001fe3000

def z354 : W := mkw 0x401a028690204043 0x0401a02869020404 0xba9f0387902040c9 0x6ba9f0387902040c

def z355 : W := mkw 0x0000080920000000 0x4000008092000000 0xec281c1ff0c0430d 0xfec281c1ff0c0430

def z356 : W := mkw 0x00e4b000010a000c 0x000e4b000010a000 0xf8fffc00033f0007 0x1f8fffc00033f000

def z357 : W := mkw 0x0010020400048082 0x0001002040004808 0xdc500264033c8ccf 0xadc500264033c8cc

def z358 : W := mkw 0x031ffeaf757b0007 0xd031ffeaf757b000 0x801ffc07e03f0000 0x1801ffc07e03f000

def z359 : W := mkw 0x70106a2de10ec5f2 0xc70106a2de10ec5f 0xdc50e27fe33fcfff 0xfdc50e27fe33fcff

def z360 : W := mkw 0x01e4b4000bcb000c 0x201e4b4000bcb000 0xf8fffc0003c30004 0x1f8fffc0003c3000

def z361 : W := mkw 0x20104224400484a2 0x820104224400484a 0x5c40026463008cff 0xa5c40026463008cf

def z362 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x84081c07f0e343fd 0x184081c07f0e343f

def z363 : W := mkw 0x82f6d3f64a802a0f 0xa82f6d3f64a802a0 0x13d7e3e00f00bc02 0x013d7e3e00f00bc0

def z364 : W := mkw 0x70186e2df16fc5f2 0xc70186e2df16fc5f 0x8018fc07e03f00f0 0x18018fc07e03f00f

def z365 : W := mkw 0x0200497960000000 0xc020049796000000 0x0000007860000000 0x8000000786000000

def z366 : W := mkw 0x22f6dbff600484af 0xc22f6dbff600484a 0xfeffffffe0008cf8 0xffeffffffe0008cf

def z367 : W := mkw 0x01e4b0000b8a000c 0x201e4b0000b8a000 0x0040e00003000000 0x00040e0000300000

def z368 : W := mkw 0x81edb4001ffb2a0c 0x381edb4001ffb2a0 0xfdfffc001fffff0f 0x1fdfffc001fffff0

def z369 : W := mkw 0x400b008294305041 0x1400b00829430504 0x3b8f03839c00f00b 0x63b8f03839c00f00

def z370 : W := mkw 0x80f303d60e94ba8b 0x380f303d60e94ba8 0x7ff703f81fdcff0f 0xe7ff703f81fdcff0

def z371 : W := mkw 0x42ffd3f6d434d0cf 0x942ffd3f6d434d0c 0xbbdfe3e79c3cf0cb 0x6bbdfe3e79c3cf0c

def z372 : W := mkw 0x21f4f6244bcf84ae 0xa21f4f6244bcf84a 0xdc70fe6463ff8cff 0xbdc70fe6463ff8cf

def z373 : W := mkw 0x00f692860000000f 0x000f692860000000 0xfaffff8780000000 0x7faffff878000000

def z374 : W := mkw 0x12e4dd796041011c 0xc12e4dd796041011 0x4460fc7860c30334 0x94460fc7860c3033

def z375 : W := mkw 0x601242a6c004d4e3 0x8601242a6c004d4e 0x060003e7e000fcf8 0xe060003e7e000fcf

def z376 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffe601fff8c0f 0xbfdfffe601fff8c0

def z377 : W := mkw 0x0000000000000000 0x0000000000000000 0x398000001c000003 0x0398000001c00000

def z378 : W := mkw 0x0010422440000002 0x8001042244000000 0xdc50e264602300fd 0xbdc50e264602300f

def z379 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xa0281c1ff0e343f0 0x5a0281c1ff0e343f

def z380 : W := mkw 0xc01b02869eb4fac3 0x3c01b02869eb4fac 0xbf9f03879ffcffcf 0x6bf9f03879ffcffc

def z381 : W := mkw 0x02f6dbff6004808f 0xc02f6dbff6004808 0xfaffffffe03c80cb 0xffaffffffe03c80c

def z382 : W := mkw 0x0010020400048082 0x0001002040004808 0xbb9003841c3cf0cb 0x6bb9003841c3cf0c

def z383 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xba9fff87e0000000 0x7ba9fff87e000000

def z384 : W := mkw 0x400900009434d0c0 0x1400900009434d0c 0xb99f00001c3cf0cb 0x0b99f00001c3cf0c

def z385 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x9850e264033c8ccb 0x29850e264033c8cc

def z386 : W := mkw 0xa0f063744b8eaeaa 0xaa0f063744b8eaea 0xdc70e27c63ff8fff 0xbdc70e27c63ff8ff

def z387 : W := mkw 0x211df624557f84a6 0x9211df624557f84a 0x801ffc04603f00f0 0x1801ffc04603f00f

def z388 : W := mkw 0x5008040090614150 0x0500804009061415 0xec281c0010e343fd 0x1ec281c0010e343f

def z389 : W := mkw 0x5000000080004150 0x0500000008000415 0x04000000000043f8 0x004000000000043f

def z390 : W := mkw 0xc0fb03d69eb4facb 0x3c0fb03d69eb4fac 0xbbbf039f9cfcf3cb 0x6bbbf039f9cfcf3c

def z391 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfbffff801ffff00f 0x7fbffff801ffff00

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8281c0000000000 0x1e8281c000000000

def z393 : W := mkw 0x21edb4001fff84ac 0x321edb4001fff84a 0xfdfffc001fff8cff 0x1fdfffc001fff8cf

def z394 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x5450e260631f8c36 0x95450e260631f8c3

def z395 : W := mkw 0x010120000f9a0000 0x3010120000f9a000 0x010000000f1c0002 0x0010000000f1c000

def z396 : W := mkw 0x8000015000002a00 0x08000015000002a0 0x0200019800007300 0x4020001980000730

def z397 : W := mkw 0x0216dbff60000007 0xc0216dbff6000000 0x821fffffe0000000 0xf821fffffe000000

def z398 : W := mkw 0x82e699db2a802a0d 0x682e699db2a802a0 0x7fef1ffb9fc0ff0f 0xe7fef1ffb9fc0ff0

def z399 : W := mkw 0x61fff6a6dfffd4ef 0xb61fff6a6dfffd4e 0xffffffe7fffffcff 0xfffffffe7fffffcf

def z400 : W := mkw 0x41ff96869ef5d0cf 0x341ff96869ef5d0c 0xbbbf1f879cfcf0cb 0x6bbbf1f879cfcf0c

def z401 : W := mkw 0x51edb4009ffb415c 0x351edb4009ffb415 0xfdfffc001fff43ff 0x1fdfffc001fff43f

def z402 : W := mkw 0x4008000090204040 0x0400800009020404 0x2008000390004000 0x4200800039000400

def z403 : W := mkw 0x01ffb6861fff908f 0x301ffb6861fff908 0xfbffff801fffb007 0x1fbffff801fffb00

def z404 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xcc10e004603f00fd 0xbcc10e004603f00f

def z405 : W := mkw 0x0000015000000000 0x0000001500000000 0x020003f800000000 0xe020003f80000000

def z406 : W := mkw 0x81e5b1500f9a2a0c 0x381e5b1500f9a2a0 0x7ff7e3f81fdcff0f 0xe7ff7e3f81fdcff0

def z407 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x3bc003e01f00fc0b 0x63bc003e01f00fc0

def z408 : W := mkw 0x80e805501ae12a08 0x280e805501ae12a0 0xffe81ff81fe3ff0f 0xfffe81ff81fe3ff0

def z409 : W := mkw 0x20104224400484a2 0x820104224400484a 0xdc50e26460008cf8 0xbdc50e26460008cf

def z410 : W := mkw 0x0000080920000000 0x4000008092000000 0x80081c07e0000000 0x180081c07e000000

def z411 : W := mkw 0x0009000014300000 0x1000900001430000 0x218f00001c000000 0x0218f00001c00000

def z412 : W := mkw 0x400b00829434d0c1 0x1400b00829434d0c 0x238f01839c3cf0cb 0x4238f01839c3cf0c

def z413 : W := mkw 0x52fedffff061415f 0xc52fedffff061415 0xfafffffff0c04300 0xffafffffff0c0430

def z414 : W := mkw 0xd00804009ae16b50 0x2d00804009ae16b5 0x050000001fe3ffff 0x0050000001fe3fff

def z415 : W := mkw 0x00002000010a0000 0x000002000010a000 0x1050e000031c0002 0x01050e000031c000

def z416 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7de000781fc00f07 0x87de000781fc00f0

def z417 : W := mkw 0x421fdaaff434d0c7 0xd421fdaaff434d0c 0xbb9fff87fc3cf0cb 0x7bb9fff87fc3cf0c

def z418 : W := mkw 0x500b0c8bb4715151 0x5500b0c8bb471515 0x23af1d9b9cc07300 0x423af1d9b9cc0730

def z419 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xe8281c1b90e34305 0x5e8281c1b90e3430

def z420 : W := mkw 0x0000000000000000 0x0000000000000000 0x020003800000f008 0x6020003800000f00

def z421 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x27a001981fc0ff0f 0x427a001981fc0ff0

def z422 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xd85ffe67e0000000 0xbd85ffe67e000000

def z423 : W := mkw 0x800000000a802a00 0x2800000000a802a0 0x5d4002601fc0ff0f 0xa5d4002601fc0ff0

def z424 : W := mkw 0x01edb5501ffb000c 0x301edb5501ffb000 0xfbfffff81fff0007 0xffbfffff81fff000

def z425 : W := mkw 0x02f6d3f64000000f 0x802f6d3f64000000 0x7af7e3f800000000 0xe7af7e3f80000000

def z426 : W := mkw 0x00106224410a0002 0x800106224410a000 0xd850e264633f0007 0xbd850e264633f000

def z427 : W := mkw 0x0000000000000000 0x0000000000000000 0x98100000003c0003 0x098100000003c000

def z428 : W := mkw 0x50000809a0004150 0x450000809a000415 0x0000001b80004300 0x40000001b8000430

def z429 : W := mkw 0x01f7b2860f9e908f 0x301f7b2860f9e908 0x13d7e3800f1cb002 0x013d7e3800f1cb00

def z430 : W := mkw 0x0010422440048082 0x8001042244004808 0xd850e264603c80cb 0xbd850e264603c80c

def z431 : W := mkw 0x601b62a6d53ed4e3 0x9601b62a6d53ed4e 0xdc5fe267e33f8cff 0xbdc5fe267e33f8cf

def z432 : W := mkw 0x00e0095920000008 0x400e009592000000 0xfae81fffe0000000 0xffae81fffe000000

def z433 : W := mkw 0x4000000080004040 0x0400000008000404 0x00000007800040c8 0x600000007800040c

def z434 : W := mkw 0x20002000010a0420 0x020002000010a042 0x0400000003030c34 0x00400000003030c3

def z435 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x4160fc001fff0007 0x14160fc001fff000

def z436 : W := mkw 0x500b0c8bb4715151 0x5500b0c8bb471515 0xefaf1d9ffce373fd 0xfefaf1d9ffce373f

def z437 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x57e003f80fc0bf06 0x857e003f80fc0bf0

def z438 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xe8281c1fe02300f0 0xfe8281c1fe02300f

def z439 : W := mkw 0xa0e061704b8a2e28 0xaa0e061704b8a2e2 0x4460e07863c30f34 0x94460e07863c30f3

def z440 : W := mkw 0x02f6daaf6000000f 0xc02f6daaf6000000 0xf8fffc07e0000000 0x1f8fffc07e000000

def z441 : W := mkw 0x20106224410a0422 0x820106224410a042 0xdc50e26463030c34 0xbdc50e26463030c3

def z442 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x5fc003e00f00bc0f 0xa5fc003e00f00bc0

def z443 : W := mkw 0x21e4f4204bcb042c 0xa21e4f4204bcb042 0x4460fc6063c30c34 0x94460fc6063c30c3

def z444 : W := mkw 0x0009000014300000 0x1000900001430000 0xbb9f03801c3cf00b 0x6bb9f03801c3cf00

def z445 : W := mkw 0x501a0e8fb0614153 0x4501a0e8fb061415 0xfebf1f9ff0e343fd 0xffebf1f9ff0e343f

def z446 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x31fffc001fdc0002 0x031fffc001fdc000

def z447 : W := mkw 0x51ecbc09bbeb415c 0x651ecbc09bbeb415 0xec68fc1ff3e343fd 0xfec68fc1ff3e343f

def z448 : W := mkw 0x02f24bff6000000b 0xc02f24bff6000000 0x7ae003ffe0000000 0xe7ae003ffe000000

def z449 : W := mkw 0x20002000010e84a0 0x020002000010e84a 0xcc000004633f8cff 0xbcc000004633f8cf

def z450 : W := mkw 0x50120a8fa004d1d3 0x450120a8fa004d1d 0x0600039fe000f3f8 0xe0600039fe000f3f

def z451 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfbfffffffc00f00b 0xffbfffffffc00f00

def z452 : W := mkw 0x83ffffff7ffb2a0f 0xf83ffffff7ffb2a0 0xffffffffffffff0f 0xfffffffffffffff0

def z453 : W := mkw 0xc0eb01d29eb07a49 0x3c0eb01d29eb07a4 0x23af019b9cc07300 0x423af019b9cc0730

def z454 : W := mkw 0xa0e021500b8eaea8 0x2a0e021500b8eaea 0x7fe003f81fffffff 0xe7fe003f81ffffff

def z455 : W := mkw 0x01ed94001ef1000c 0x301ed94001ef1000 0xb9bf1c001cfc0003 0x0b9bf1c001cfc000

def z456 : W := mkw 0x20006020410a0420 0x820006020410a042 0x0000e00060030030 0x10000e0006003003

def z457 : W := mkw 0x60186224d12ec4e2 0x860186224d12ec4e 0xfc58e267f33fccff 0xffc58e267f33fccf

def z458 : W := mkw 0x02f7dbff6414908f 0xd02f7dbff6414908 0xfbffffffec1cb002 0xffbffffffec1cb00

def z459 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x4440e26463038cfc 0xb4440e26463038cf

def z460 : W := mkw 0x401b06869475d0c3 0x1401b06869475d0c 0xfbbf1f879cfff0cf 0x7fbbf1f879cfff0c

def z461 : W := mkw 0x00104a2d60000002 0xc00104a2d6000000 0xf878fe7fe0000000 0xff878fe7fe000000

def z462 : W := mkw 0x41ef94829ef1504d 0x341ef94829ef1504 0x23af1d839cc07000 0x423af1d839cc0700

def z463 : W := mkw 0x0002008200000001 0x0000200820000000 0x228f018380000000 0x4228f01838000000

def z464 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x0010e000001c0000 0x00010e000001c000

def z465 : W := mkw 0x000000000a800000 0x2000000000a80000 0x010000001fc00007 0x0010000001fc0000

def z466 : W := mkw 0x02fedfff7061000f 0xc02fedfff7061000 0xfafffffff0e30005 0xffafffffff0e3000

def z467 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xba9f0387803c00c0 0x6ba9f0387803c00c

def z468 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c0000000000000d 0xa4c0000000000000

def z469 : W := mkw 0x5008040090614150 0x0500804009061415 0xcc00000470e343fd 0xbcc00000470e343f

def z470 : W := mkw 0x50090c09b475d1d0 0x550090c09b475d1d 0xed281c1ffcfff3ff 0xfed281c1ffcfff3f

def z471 : W := mkw 0x21fdf6245fff84ae 0xb21fdf6245fff84a 0xf9fffe601fff8c07 0x1f9fffe601fff8c0

def z472 : W := mkw 0x0013028604149083 0x1001302860414908 0x9b9703840c3cb0cb 0x29b9703840c3cb0c

def z473 : W := mkw 0x02f6d3f64000000f 0x802f6d3f64000000 0xdad7e3e460000000 0xbdad7e3e46000000

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000004600000f8 0xa04000004600000f

def z475 : W := mkw 0x0000000000000000 0x0000000000000000 0x6820000010c00005 0x06820000010c0000

def z476 : W := mkw 0x701b6eaff57fd5f3 0xd701b6eaff57fd5f 0xffffffffffffffff 0xffffffffffffffff

def z477 : W := mkw 0x00e0015000000008 0x000e001500000000 0x12c003e000000000 0x012c003e00000000

def z478 : W := mkw 0x4008000090204040 0x0400800009020404 0xec28001f90e043cd 0xeec28001f90e043c

def z479 : W := mkw 0x400900009434d0c0 0x1400900009434d0c 0x3b8003801c3cf0cb 0x63b8003801c3cf0c

def z480 : W := mkw 0x81ed95501ef12a0c 0x381ed95501ef12a0 0x7fef1ff81fc0ff0f 0xe7fef1ff81fc0ff0

def z481 : W := mkw 0x0009000014300000 0x1000900001430000 0x801f0000003c0000 0x0801f0000003c000

def z482 : W := mkw 0x62fffbfff53ed4ef 0xd62fffbfff53ed4e 0xffffffffff3ffcff 0xfffffffffff3ffcf

def z483 : W := mkw 0x01ecb4001beb000c 0x201ecb4001beb000 0xe868fc0013e30005 0x1e868fc0013e3000

def z484 : W := mkw 0x70186e2df16fc5f2 0xc70186e2df16fc5f 0xdc58fe67e33f8cff 0xbdc58fe67e33f8cf

def z485 : W := mkw 0x00e001500a800008 0x200e001500a80000 0x7be003f81fc00007 0xe7be003f81fc0000

def z486 : W := mkw 0xa2f6fbff6b8eaeaf 0xea2f6fbff6b8eaea 0xffffffffffffffff 0xffffffffffffffff

def z487 : W := mkw 0x51ffbe8fbfffd1df 0x751ffbe8fbfffd1d 0xffffff9ffffff3ff 0xfffffff9ffffff3f

def z488 : W := mkw 0x03fffeaf7ffb000f 0xf03fffeaf7ffb000 0xf9fffc07ffff0007 0x1f9fffc07ffff000

def z489 : W := mkw 0x800000000a802a00 0x2800000000a802a0 0x010000001cc07300 0x0010000001cc0730

def z490 : W := mkw 0x02f6d3f64000000f 0x802f6d3f64000000 0xbadfe3e780000000 0x6badfe3e78000000

def z491 : W := mkw 0x8000015000002a00 0x08000015000002a0 0x0400007800000f00 0x80400007800000f0

def z492 : W := mkw 0x81e4b5500bcb2a0c 0x281e4b5500bcb2a0 0x7fe0fff81fc3ff0f 0xf7fe0fff81fc3ff0

def z493 : W := mkw 0x00002000010a0000 0x000002000010a000 0xdc50e260033f8c0f 0xbdc50e260033f8c0

def z494 : W := mkw 0x82f24bff6a802a0b 0xe82f24bff6a802a0 0x7fe003ffffc0ff0f 0xe7fe003ffffc0ff0

def z495 : W := mkw 0x0010422440000002 0x8001042244000000 0x1050e26000000000 0x01050e2600000000

def z496 : W := mkw 0x00e000000a800008 0x200e000000a80000 0x7be003801fc0f00f 0x67be003801fc0f00

def z497 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800000460000000 0xbc80000046000000

def z498 : W := mkw 0x20002000010e84a0 0x020002000010e84a 0x00000000031c8c02 0x000000000031c8c0

def z499 : W := mkw 0xa01062244b8eaea2 0xaa01062244b8eaea 0xdd50e2647fffffff 0xbdd50e2647ffffff

def z500 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x038001800c003000 0x0038001800c00300

def z501 : W := mkw 0x010904001ef10000 0x3010904001ef1000 0x010000001cc00000 0x0010000001cc0000

def z502 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xd850e264631c8c02 0xbd850e264631c8c0

def z503 : W := mkw 0x20002000010e84a0 0x020002000010e84a 0x00000000003f00f0 0x000000000003f00f

def z504 : W := mkw 0x41ffb6869fffd0cf 0x341ffb6869fffd0c 0xf9fffc079fff00c7 0x1f9fffc079fff00c

def z505 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x1450e264631c8cfa 0xa1450e264631c8cf

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0x4440006003000c04 0x84440006003000c0

def z507 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xc450e064633f0cf4 0x9c450e064633f0cf

def z508 : W := mkw 0x010924001ffb0000 0x3010924001ffb000 0xd950e0001fff0007 0x1d950e0001fff000

def z509 : W := mkw 0x42ef99dbb430504d 0x542ef99dbb430504 0x23af1d9b9c007000 0x423af1d9b9c00700

def z510 : W := mkw 0x800000000a802a00 0x2800000000a802a0 0x0400000003c00f04 0x00400000003c00f0

def z511 : W := mkw 0x52124bffe0004153 0xc52124bffe000415 0x060003ffe00043f8 0xe060003ffe00043f

def z512 : W := mkw 0x5008040090614150 0x0500804009061415 0x6c20001810e343fd 0xe6c20001810e343f

def z513 : W := mkw 0x8000015000002a00 0x08000015000002a0 0x5e4003f80300ff0f 0xe5e4003f80300ff0

def z514 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x6fa001981cc0730d 0xe6fa001981cc0730

def z515 : W := mkw 0xa0106374410eaea2 0x8a0106374410eaea 0xde50e3fc633fffff 0xfde50e3fc633ffff

def z516 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7ee003f803c00f04 0xe7ee003f803c00f0

def z517 : W := mkw 0x521edeaff0614157 0xc521edeaff061415 0x801ffc07e02300f0 0x1801ffc07e02300f

def z518 : W := mkw 0xc00900009eb4fac0 0x3c00900009eb4fac 0x050000001ffcffcf 0x0050000001ffcffc

def z519 : W := mkw 0xd0e80d59bae16b58 0x6d0e80d59bae16b5 0xec681c7ff3e34ffd 0xfec681c7ff3e34ff

def z520 : W := mkw 0x010d940014710004 0x1010d94001471000 0x000f1c0000000000 0x0000f1c000000000

def z521 : W := mkw 0x02ffdbff7430000f 0xd02ffdbff7430000 0xfbfffffffc3c0003 0xffbfffffffc3c000

def z522 : W := mkw 0x51ed9c09bef1415c 0x751ed9c09bef1415 0x21af1c1b9cc04300 0x421af1c1b9cc0430

def z523 : W := mkw 0x601b2286953ed4e3 0x1601b2286953ed4e 0xbf9f03879f3ffcff 0x6bf9f03879f3ffcf

def z524 : W := mkw 0x20006020410a0420 0x820006020410a042 0xdc50e060633f0c37 0x9dc50e060633f0c3

def z525 : W := mkw 0x400900009434d0c0 0x1400900009434d0c 0xa90800079c3cf0cb 0x6a90800079c3cf0c

def z526 : W := mkw 0x01e924001ffb0008 0x301e924001ffb000 0x79e000001fff0007 0x079e000001fff000

def z527 : W := mkw 0xd0fb0fdfbef5fbdb 0x7d0fb0fdfbef5fbd 0xffff1fffffffffff 0xfffff1ffffffffff

def z528 : W := mkw 0xc01203d68004fac3 0x0c01203d68004fac 0x060003ff8000ffc8 0xe060003ff8000ffc

def z529 : W := mkw 0x22f4fb7d610e84ae 0xc22f4fb7d610e84a 0xdc70fe7c633f8cff 0xbdc70fe7c633f8cf

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0x238001801c007000 0x4238001801c00700

def z531 : W := mkw 0x00082400116b0000 0x000082400116b000 0xf878fc0013ff0007 0x1f878fc0013ff000

def z532 : W := mkw 0x70104a2de004c5f2 0xc70104a2de004c5f 0x0400027fe000cff8 0xe0400027fe000cff

def z533 : W := mkw 0x52fedffff061415f 0xc52fedffff061415 0xfaffffffe02300f0 0xffaffffffe02300f

def z534 : W := mkw 0x51ed9c09bef1415c 0x751ed9c09bef1415 0xedaf1c1ffce343fd 0xfedaf1c1ffce343f

def z535 : W := mkw 0x30006c29614b0530 0xc30006c29614b053 0x4460fc7863c30f34 0x94460fc7863c30f3

def z536 : W := mkw 0xa0f063744b8eaeaa 0xaa0f063744b8eaea 0x7ff0e3f81fdcff0f 0xe7ff0e3f81fdcff0

def z537 : W := mkw 0x00102204010e8082 0x000102204010e808 0xd850e204033f80cf 0x3d850e204033f80c

def z538 : W := mkw 0x0216d2a640000007 0x80216d2a64000000 0x0017e00000000000 0x00017e0000000000

def z539 : W := mkw 0x400b008294305041 0x1400b00829430504 0xab8f01879c2070c9 0x6ab8f01879c2070c

def z540 : W := mkw 0x20002000010e84a0 0x020002000010e84a 0xdc50e000033f8cff 0x1dc50e000033f8cf

def z541 : W := mkw 0x20006020410e84a0 0x820006020410e84a 0x4440e060633f8cff 0x94440e060633f8cf

def z542 : W := mkw 0x00e900001eb00008 0x300e900001eb0000 0xf9ff00001ffc0007 0x0f9ff00001ffc000

def z543 : W := mkw 0x53fffffffffb415f 0xf53fffffffffb415 0xffffffffffff43ff 0xfffffffffffff43f

def z544 : W := mkw 0x411fb686957fd0c7 0x1411fb686957fd0c 0x801ffc07803f00c0 0x1801ffc07803f00c

def z545 : W := mkw 0x00002000010a0000 0x000002000010a000 0x8010e000003f0000 0x18010e000003f000

def z546 : W := mkw 0x401202868004d0c3 0x0401202868004d0c 0x00000007800000c0 0x000000007800000c

def z547 : W := mkw 0x70186e2df16fc5f2 0xc70186e2df16fc5f 0xec38fc1ff0ff43fd 0xfec38fc1ff0ff43f

def z548 : W := mkw 0x0000000000000000 0x0000000000000000 0x4420001800c00304 0x84420001800c0030

def z549 : W := mkw 0x50082c09b16b4150 0x450082c09b16b415 0xfc78fc1ff3ff43ff 0xffc78fc1ff3ff43f

def z550 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000010c0430d 0x00400000010c0430

def z551 : W := mkw 0x4008000090204040 0x0400800009020404 0x80080007802000c0 0x080080007802000c

def z552 : W := mkw 0x500904009475d1d0 0x1500904009475d1d 0x050000001cfff3ff 0x0050000001cfff3f

def z553 : W := mkw 0x2000402040000420 0x8200040204000042 0x0400006060000c30 0x80400006060000c3

def z554 : W := mkw 0x82e4d9796a802a0c 0xe82e4d9796a802a0 0x7fe0fff87fc0ff0f 0xf7fe0fff87fc0ff0

def z555 : W := mkw 0x10000c0920410110 0x410000c092041011 0xcc201c1c60e303fd 0xbcc201c1c60e303f

def z556 : W := mkw 0x71fdfe2dffffc5fe 0xf71fdfe2dffffc5f 0xfdfffe7fffffcfff 0xffdfffe7fffffcff

def z557 : W := mkw 0x0012028600049083 0x0001202860004908 0x020003800000b000 0x0020003800000b00

def z558 : W := mkw 0x00e0015000000008 0x000e001500000000 0x22a0019800000000 0x422a001980000000

def z559 : W := mkw 0x11edbc093ffb011c 0x711edbc093ffb011 0xfdfffc187fff0337 0x9fdfffc187fff033

def z560 : W := mkw 0x80e000000a802a08 0x280e000000a802a0 0x7de000001fc0ff0f 0x07de000001fc0ff0

def z561 : W := mkw 0x00e0015000000008 0x000e001500000000 0x7ee003f810c0430d 0xe7ee003f810c0430

def z562 : W := mkw 0x42fedbfff020404f 0xc42fedbfff020404 0xfafffffff02040c9 0xffafffffff02040c

def z563 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xe83ffc1fe0000000 0xfe83ffc1fe000000

def z564 : W := mkw 0x20000000000484a0 0x020000000000484a 0x0400000000008cf8 0x00400000000008cf

def z565 : W := mkw 0x0008040010610000 0x0000804001061000 0xec281c0470e300fd 0xbec281c0470e300f

def z566 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x24281c1b90e343fd 0x424281c1b90e343f

def z567 : W := mkw 0x82f6d3f64a802a0f 0xa82f6d3f64a802a0 0x7ff7e3f81fc0ff0f 0xe7ff7e3f81fc0ff0

def z568 : W := mkw 0x50e80d59b0614158 0x450e80d59b061415 0xfee81ffff0e343fd 0xffee81ffff0e343f

def z569 : W := mkw 0x20006020410a0420 0x820006020410a042 0xcc40e06463230cfd 0xbcc40e06463230cf

def z570 : W := mkw 0x01edb0001fba000c 0x301edb0001fba000 0xb9dfe0001f3c0003 0x0b9dfe0001f3c000

def z571 : W := mkw 0x23ffffff7fff84af 0xf23ffffff7fff84a 0xffffffffffff8cff 0xfffffffffffff8cf

def z572 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x27a003f81cc0ff08 0xe27a003f81cc0ff0

def z573 : W := mkw 0x0000402040000000 0x8000040204000000 0x4040e06060000000 0x94040e0606000000

def z574 : W := mkw 0x20104224400484a2 0x820104224400484a 0x00000004600000f0 0x000000004600000f

def z575 : W := mkw 0x81e925501ffb2a08 0x381e925501ffb2a0 0x7fe003f81fffff0f 0xe7fe003f81fffff0

def z576 : W := mkw 0x0010422440000002 0x8001042244000000 0x0000026460000000 0xa000002646000000

def z577 : W := mkw 0x02f4db7d6000000e 0xc02f4db7d6000000 0xd870fe7c60000000 0xbd870fe7c6000000

def z578 : W := mkw 0xa0f043744a84aeaa 0xaa0f043744a84aea 0x7fe003fc7fc0ffff 0xe7fe003fc7fc0fff

def z579 : W := mkw 0x40fb02869eb4d0cb 0x340fb02869eb4d0c 0xfbff03879ffcf0cf 0x6fbff03879ffcf0c

def z580 : W := mkw 0x01ed94001ef1000c 0x301ed94001ef1000 0x79ef1c001fc00007 0x079ef1c001fc0000

def z581 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xcc081c07e02300fd 0xbcc081c07e02300f

def z582 : W := mkw 0x01fdb6041fff808e 0x301fdb6041fff808 0xf9fffe041fff80cf 0x3f9fffe041fff80c

def z583 : W := mkw 0x0104b400014b0004 0x00104b400014b000 0x0000fc0000030000 0x10000fc000003000

def z584 : W := mkw 0x70086c29f16b4570 0xc70086c29f16b457 0xec68fc7ff3e34ffd 0xfec68fc7ff3e34ff

def z585 : W := mkw 0x22e4f979610a042c 0xc22e4f979610a042 0x4460fc7863030c34 0x94460fc7863030c3

def z586 : W := mkw 0x70082c09b16fc5f0 0x470082c09b16fc5f 0xec281c1ff3ffcfff 0xfec281c1ff3ffcff

def z587 : W := mkw 0x40ff92869434d0cf 0x140ff92869434d0c 0xfbffff879c3cf0cb 0x7fbffff879c3cf0c

def z588 : W := mkw 0x01e590000e90000c 0x301e590000e90000 0x018700000c000000 0x0018700000c00000

def z589 : W := mkw 0x50080809b0204150 0x450080809b020415 0xac08001ff02043f9 0xeac08001ff02043f

def z590 : W := mkw 0x501b0e8fb475d1d3 0x5501b0e8fb475d1d 0x801f1c07e03f00f0 0x1801f1c07e03f00f

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0xa808000780000000 0x6a80800078000000

def z592 : W := mkw 0x10000c0920410110 0x410000c092041011 0x00201c1800c00300 0x000201c1800c0030

def z593 : W := mkw 0x0003008204101001 0x1000300820410100 0x038701800c003000 0x0038701800c00300

def z594 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x3ba003981cc0f30b 0x63ba003981cc0f30

def z595 : W := mkw 0xd0e00959aa806b58 0x6d0e00959aa806b5 0x7fe003ffffc0ffff 0xe7fe003ffffc0fff

def z596 : W := mkw 0x01e5b0000f9a000c 0x301e5b0000f9a000 0xd9d7e0000f3f0007 0x1d9d7e0000f3f000

def z597 : W := mkw 0x00e020000b8a0008 0x200e020000b8a000 0xf9f0e0001fff0007 0x1f9f0e0001fff000

def z598 : W := mkw 0xd0080d59b0616b50 0x4d0080d59b0616b5 0xee281ffff0e3fffd 0xfee281ffff0e3fff

def z599 : W := mkw 0x0013028604149083 0x1001302860414908 0x00170000001c0000 0x000170000001c000

def z600 : W := mkw 0x0012028600000003 0x0001202860000000 0x0200038780000000 0x6020003878000000

def z601 : W := mkw 0x02124bff60000003 0xc02124bff6000000 0xda50e3ffe0000000 0xfda50e3ffe000000

def z602 : W := mkw 0x41efb4829ffb504d 0x341efb4829ffb504 0xfbfffd839fff7007 0x5fbfffd839fff700

def z603 : W := mkw 0x02124aaf60000003 0xc02124aaf6000000 0x00000007e0000000 0x000000007e000000

def z604 : W := mkw 0x20006020410a0420 0x820006020410a042 0x0040e06003000c00 0x00040e06003000c0

def z605 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x91dffc000f3f0002 0x191dffc000f3f000

def z606 : W := mkw 0x00e490000000000c 0x000e490000000000 0x10d7e00000000000 0x010d7e0000000000

def z607 : W := mkw 0x42ff9bdfb434d0cf 0x542ff9bdfb434d0c 0xbbbf1f9f9c3cf0cb 0x6bbbf1f9f9c3cf0c

def z608 : W := mkw 0x201362a6451e94a3 0x9201362a6451e94a 0x13d7e3e00f1cbc02 0x013d7e3e00f1cbc0

def z609 : W := mkw 0xa00020000b8eaea0 0x2a00020000b8eaea 0x050000001fffffff 0x0050000001ffffff

def z610 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xc4281c1fe0e303f4 0x9c4281c1fe0e303f

def z611 : W := mkw 0x501b0e8fb475d1d3 0x5501b0e8fb475d1d 0xec3f1c1ff0ff43fd 0xfec3f1c1ff0ff43f

def z612 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x12d7e3ffe0000000 0xe12d7e3ffe000000

def z613 : W := mkw 0xc01b03d69434fac3 0x1c01b03d69434fac 0xbf9f03ff9c3cffcb 0xebf9f03ff9c3cffc

def z614 : W := mkw 0x0000080920000000 0x4000008092000000 0x40201c1860000000 0x940201c186000000

def z615 : W := mkw 0x30106e2d614f85b2 0xc30106e2d614f85b 0xdc70fe7c63ff8fff 0xbdc70fe7c63ff8ff

def z616 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xd850e004633f00f7 0x1d850e004633f00f

def z617 : W := mkw 0x001242a640000003 0x8001242a64000000 0xfadfe3e7e0000000 0xffadfe3e7e000000

def z618 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x8410e004633f8cff 0x18410e004633f8cf

def z619 : W := mkw 0x0000000000000000 0x0000000000000000 0xec20001c70e343fd 0xfec20001c70e343f

def z620 : W := mkw 0x22f6f3f6410e84af 0x822f6f3f6410e84a 0xded7e3e4633f8cff 0xbded7e3e4633f8cf

def z621 : W := mkw 0xc0fb03d69eb4facb 0x3c0fb03d69eb4fac 0xbbdf03e79f3cfccb 0x6bbdf03e79f3cfcc

def z622 : W := mkw 0x4008040090614040 0x0400804009061404 0xe8281c0790e340cd 0x7e8281c0790e340c

def z623 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x0400001ff0e343fd 0xe0400001ff0e343f

def z624 : W := mkw 0x80e0015000002a08 0x080e0015000002a0 0x7ee003f80000ff08 0xe7ee003f80000ff0

def z625 : W := mkw 0x03ffdfff7ef1000f 0xf03ffdfff7ef1000 0xfbfffffffcc00000 0xffbfffffffcc0000

def z626 : W := mkw 0x810924001ffb2a00 0x3810924001ffb2a0 0x050000001fffff0f 0x0050000001fffff0

def z627 : W := mkw 0x11e4bc092bcb011c 0x611e4bc092bcb011 0x4460fc1863c30334 0x94460fc1863c3033

def z628 : W := mkw 0x22f6fbff610e84af 0xc22f6fbff610e84a 0xfaffffffe03f00f0 0xffaffffffe03f00f

def z629 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffc181fff430f 0xffdfffc181fff430

def z630 : W := mkw 0x0008000010200000 0x0000800001020000 0xa808000010200001 0x0a80800001020000

def z631 : W := mkw 0xa0e061704b8a2e28 0xaa0e061704b8a2e2 0x7fe0e3f87fc3ff3f 0xf7fe0e3f87fc3ff3

def z632 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x84081c1fe02343f8 0xf84081c1fe02343f

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800000010004009 0x6280000001000400

def z634 : W := mkw 0x1000040000410110 0x0100004000041011 0x0400000000c30334 0x00400000000c3033

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x7fc003e01f00fc0f 0xe7fc003e01f00fc0

def z636 : W := mkw 0x02f69bdf2000000f 0x402f69bdf2000000 0xbabf1f9f80000000 0x6babf1f9f8000000

def z637 : W := mkw 0x01e4b4000bcb000c 0x201e4b4000bcb000 0x79e0fc001fc30007 0x179e0fc001fc3000

def z638 : W := mkw 0x90e00d592ac12b18 0x690e00d592ac12b1 0x44601c7863c30f34 0x944601c7863c30f3

def z639 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x456000781fc0ff0f 0x8456000781fc0ff0

def z640 : W := mkw 0x0010020400048082 0x0001002040004808 0xdc100204603f80ff 0xbdc100204603f80f

def z641 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a80038000000000 0x63a8003800000000

def z642 : W := mkw 0x201362a6451e94a3 0x9201362a6451e94a 0xdfd7e3e46f3fbcff 0xbdfd7e3e46f3fbcf

def z643 : W := mkw 0x22126bff610e84a3 0xc22126bff610e84a 0xde50e3ffe33f8cff 0xfde50e3ffe33f8cf

def z644 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7be003e01fc0bc07 0x07be003e01fc0bc0

def z645 : W := mkw 0x010924001ffb0000 0x3010924001ffb000 0xe9281c001fff0007 0x1e9281c001fff000

def z646 : W := mkw 0x00120a8f20000003 0x400120a8f2000000 0xfabf1f9fe0000000 0xffabf1f9fe000000

def z647 : W := mkw 0x0001000004149080 0x1000100000414908 0x010000000c1cb002 0x0010000000c1cb00

def z648 : W := mkw 0x411fb686957fd0c7 0x1411fb686957fd0c 0xbb9fff879c3ff0cb 0x7bb9fff879c3ff0c

def z649 : W := mkw 0x01ffb6861ffb000f 0x301ffb6861ffb000 0xfbffff879fff0007 0x7fbffff879fff000

def z650 : W := mkw 0x00002000010a0000 0x000002000010a000 0x4040e00003030004 0x14040e0000303000

def z651 : W := mkw 0x0008040010610000 0x0000804001061000 0x20281c0010c00000 0x020281c0010c0000

def z652 : W := mkw 0x81ed95501ef12a0c 0x381ed95501ef12a0 0x23af1d981cc07300 0x423af1d981cc0730

def z653 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x5c50e260031c8c0f 0xa5c50e260031c8c0

def z654 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800000000230005 0x1c80000000023000

def z655 : W := mkw 0x0010020400048082 0x0001002040004808 0x00000204000080c8 0x200000204000080c

def z656 : W := mkw 0x20f06374410e84aa 0x820f06374410e84a 0xfef0e3fc633f8cff 0xffef0e3fc633f8cf

def z657 : W := mkw 0x70082400916fc5f0 0x070082400916fc5f 0x0400000013ffcfff 0x00400000013ffcff

def z658 : W := mkw 0x02e699db2000000d 0x402e699db2000000 0x7aef1ffb80000000 0xe7aef1ffb8000000

def z659 : W := mkw 0xf0f86f7dfbefeffa 0xef0f86f7dfbefeff 0xfff8ffffffffffff 0xffff8fffffffffff

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0xb89f000000000000 0x0b89f00000000000

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000004602300f0 0x180000004602300f

def z662 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x61effc001fc30004 0x161effc001fc3000

def z663 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x238f03879c00f0c8 0x6238f03879c00f0c

def z664 : W := mkw 0x401902049434d0c2 0x1401902049434d0c 0x991002041c3cf0cb 0x2991002041c3cf0c

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0x7fa003981cc0f30f 0xe7fa003981cc0f30

def z666 : W := mkw 0x0012028600000003 0x0001202860000000 0x1297038000000000 0x0129703800000000

def z667 : W := mkw 0x01ed94001ef1000c 0x301ed94001ef1000 0xe9af1c001ce30005 0x1e9af1c001ce3000

def z668 : W := mkw 0x400000008004d0c0 0x0400000008004d0c 0x000000000000f0c8 0x0000000000000f0c

def z669 : W := mkw 0x21f5f2244f9e84ae 0xb21f5f2244f9e84a 0x11d7e2600f1c8c02 0x011d7e2600f1c8c0

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0x5840026000000000 0xa584002600000000

def z671 : W := mkw 0x4008000090204040 0x0400800009020404 0xbb8803879c20f0cb 0x6bb8803879c20f0c

def z672 : W := mkw 0x421b4bfff434d0c3 0xd421b4bfff434d0c 0xbb9f03fffc3cf0cb 0xebb9f03fffc3cf0c

def z673 : W := mkw 0x0000040000410000 0x0000004000041000 0x40201c0000c30004 0x140201c0000c3000

def z674 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x17c003e01fc0ff0f 0x017c003e01fc0ff0

def z675 : W := mkw 0x22f6fbff610e84af 0xc22f6fbff610e84a 0xfaffffffe31c8c02 0xffaffffffe31c8c0

def z676 : W := mkw 0x51edbc09bffb415c 0x751edbc09bffb415 0xf9fffc07ffff00f7 0x1f9fffc07ffff00f

def z677 : W := mkw 0x411b26869fffd0c3 0x3411b26869fffd0c 0xbb9f03879ffff0cf 0x6bb9f03879ffff0c

def z678 : W := mkw 0x0000000000000000 0x0000000000000000 0x5840000003000007 0x0584000000300000

def z679 : W := mkw 0x4009000094304040 0x1400900009430404 0xb99f00079c3c40cb 0x6b99f00079c3c40c

def z680 : W := mkw 0x02e4d1704000000c 0x802e4d1704000000 0x0040e06000000000 0x00040e0600000000

def z681 : W := mkw 0x00ec94001061000c 0x000ec94001061000 0xf8fffc0010e30005 0x1f8fffc0010e3000

def z682 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x0040006003000c00 0x00040006003000c0

def z683 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x030003879c3cf0cb 0x6030003879c3cf0c

def z684 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x11d7e0001fff0007 0x011d7e0001fff000

def z685 : W := mkw 0x20196224553e84a2 0x920196224553e84a 0xfddfe2647f3f8cff 0xbfddfe2647f3f8cf

def z686 : W := mkw 0x50e80c09bae14158 0x650e80c09bae1415 0xfde81c1fffe343ff 0xffde81c1fffe343f

def z687 : W := mkw 0x41edb4009fffd0cc 0x341edb4009fffd0c 0xf9fffc001ffff0cf 0x1f9fffc001ffff0c

def z688 : W := mkw 0x800000000a802a00 0x2800000000a802a0 0x010000000f00bc02 0x0010000000f00bc0

def z689 : W := mkw 0x8000015000002a00 0x08000015000002a0 0x020003e00000bc00 0x0020003e00000bc0

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400001800004308 0xe040000180000430

def z691 : W := mkw 0x21edf4205ffb042c 0xb21edf4205ffb042 0xfdfffc607fff0c37 0x9fdfffc607fff0c3

def z692 : W := mkw 0x0000080920000000 0x4000008092000000 0x20281c1b80000000 0x420281c1b8000000

def z693 : W := mkw 0x02124bff60000003 0xc02124bff6000000 0xba9f03ffe0000000 0xeba9f03ffe000000

def z694 : W := mkw 0x80f003540a84aa8a 0x280f003540a84aa8 0xfff003fc1ffcffcf 0xefff003fc1ffcffc

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x2020001810c04300 0x42020001810c0430

def z696 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7be003f80f00bc02 0xe7be003f80f00bc0

def z697 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x24281c1ff0c043f8 0xe24281c1ff0c043f

def z698 : W := mkw 0x50000809a0004150 0x450000809a000415 0xcc00001fe02343fd 0xfcc00001fe02343f

def z699 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x6c60007813c04f0d 0xe6c60007813c04f0

def z700 : W := mkw 0x22f6f3f6410e84af 0x822f6f3f6410e84a 0x12d7e3e0031c8c02 0x012d7e3e0031c8c0

def z701 : W := mkw 0x1000080920000110 0x4100008092000011 0x0400001860000330 0x8040000186000033

def z702 : W := mkw 0x0000000000000000 0x0000000000000000 0x010000001c00f00b 0x0010000001c00f00

def z703 : W := mkw 0x22f6fbff610a042f 0xc22f6fbff610a042 0xfeffffffe3030c34 0xffeffffffe3030c3

def z704 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x981f0207803c80cb 0x2981f0207803c80c

def z705 : W := mkw 0x8000015000002a00 0x08000015000002a0 0x6e2003f810c0ff0d 0xe6e2003f810c0ff0

def z706 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x44201c1870e343fd 0x944201c1870e343f

def z707 : W := mkw 0x22e6b9db210e84ad 0x422e6b9db210e84a 0x26af1d9b833f8cff 0x426af1d9b833f8cf

def z708 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc079fff0007 0x7f9fffc079fff000

def z709 : W := mkw 0xc2f24bffea84facb 0xec2f24bffea84fac 0x7fe003ffffc0ffcf 0xe7fe003ffffc0ffc

def z710 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xffffff981ffff30f 0xfffffff981ffff30

def z711 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xfcbf1c1ff0e343fd 0xffcbf1c1ff0e343f

def z712 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xfb9f0387fc3cf0cb 0xffb9f0387fc3cf0c

def z713 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xa4281c1ff0e343fd 0x5a4281c1ff0e343f

def z714 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfffffffffcc0730d 0xffffffffffcc0730

def z715 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xa2bfffffe0000000 0xfa2bfffffe000000

def z716 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xde50e3e4633ffcff 0xfde50e3e4633ffcf

def z717 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x3be003f81fc0ff0b 0x63be003f81fc0ff0

def z718 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfbfffffffc000003 0xffbfffffffc00000

def z719 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfffffff81fffbf07 0x9fffffff81fffbf0

def z720 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xdc50e264633f0cf4 0xbdc50e264633f0cf

def z721 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xe83ffc00003f0000 0x1e83ffc00003f000

def z722 : W := mkw 0x81e5b1500f9a2a0c 0x381e5b1500f9a2a0 0xfffffff81fdcff0f 0xffffffff81fdcff0

def z723 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc000f3f0002 0x1f9fffc000f3f000

def z724 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xc05ffc67e0000000 0x9c05ffc67e000000

def z725 : W := mkw 0x02f6dbff6a80000f 0xe02f6dbff6a80000 0xffffffffffc0430f 0xfffffffffffc0430

def z726 : W := mkw 0x0000080920000000 0x4000008092000000 0xec281c1ff0e343fd 0xfec281c1ff0e343f

def z727 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffe781fffcf0f 0xffdfffe781fffcf0

def z728 : W := mkw 0x80e491500a802a0c 0x280e491500a802a0 0x7fef1ff81fc0ff0f 0xe7fef1ff81fc0ff0

def z729 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x32ffffffe0000000 0xe32ffffffe000000

def z730 : W := mkw 0x51edb4009ffb415c 0x351edb4009ffb415 0xf9fffc001fff00f7 0x1f9fffc001fff00f

def z731 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbf9f03e79c3cfccb 0xebf9f03e79c3cfcc

def z732 : W := mkw 0x00ed94001471000c 0x100ed94001471000 0xf9fffc001cff0007 0x1f9fffc001cff000

def z733 : W := mkw 0x81edb4001ffb2a0c 0x381edb4001ffb2a0 0xfdfffc181fffff0f 0xffdfffc181fffff0

def z734 : W := mkw 0x83e4fd796bcb2a0c 0xe83e4fd796bcb2a0 0x4460fc7863c30f04 0x94460fc7863c30f0

def z735 : W := mkw 0x70186e2df16fc5f2 0xc70186e2df16fc5f 0x3078fe7b93dccf02 0x43078fe7b93dccf0

def z736 : W := mkw 0x00e499592000000c 0x400e499592000000 0xfaffffffe0000000 0xffaffffffe000000

def z737 : W := mkw 0x0016928600000007 0x0001692860000000 0xba9fff8780000000 0x7ba9fff878000000

def z738 : W := mkw 0x11edb4001ffb011c 0x311edb4001ffb011 0xfdfffc001fff0337 0x1fdfffc001fff033

def z739 : W := mkw 0x010db400157b0004 0x1010db400157b000 0x801ffc04603f00f0 0x1801ffc04603f00f

def z740 : W := mkw 0x41edb4009ffb404c 0x341edb4009ffb404 0xfbffff879ffff0cf 0x7fbffff879ffff0c

def z741 : W := mkw 0x02f6dbff6a80000f 0xe02f6dbff6a80000 0xfaffffffe3c00004 0xffaffffffe3c0000

def z742 : W := mkw 0x02f6daaf6000000f 0xc02f6daaf6000000 0xa0bffc07e0000000 0x1a0bffc07e000000

def z743 : W := mkw 0x20006020410e84a0 0x820006020410e84a 0xcc40e064633f8cff 0xbcc40e064633f8cf

def z744 : W := mkw 0xd10924009ffb6b50 0x3d10924009ffb6b5 0x050000001fffffff 0x0050000001ffffff

def z745 : W := mkw 0x00ed90001eb0000c 0x300ed90001eb0000 0xf9fffc001ffc0007 0x1f9fffc001ffc000

def z746 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbb9f03879c3c70c0 0x6bb9f03879c3c70c

def z747 : W := mkw 0x41f6b6868bcfd0cf 0x241f6b6868bcfd0c 0x4260ff8783c3f0cc 0x74260ff8783c3f0c

def z748 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xf9bffc001cff0007 0x1f9bffc001cff000

def z749 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x9450e264633f8cfa 0xb9450e264633f8cf

def z750 : W := mkw 0x601b42a6d434d4e3 0x9601b42a6d434d4e 0xffdf03e7ff3cfcff 0xeffdf03e7ff3cfcf

def z751 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfbffffffec003000 0xffbffffffec00300

def z752 : W := mkw 0x02f6dbff6a80000f 0xe02f6dbff6a80000 0xfbffffffef000002 0xffbffffffef00000

def z753 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x57e003f81fc0ff0f 0x857e003f81fc0ff0

def z754 : W := mkw 0x601b02869434d4e3 0x1601b02869434d4e 0xbf9f03879c3cfcfb 0x6bf9f03879c3cfcf

def z755 : W := mkw 0x81edb4001ffb2a0c 0x381edb4001ffb2a0 0xfdfffe601fffff0f 0xbfdfffe601fffff0

def z756 : W := mkw 0x81edb4001ffb2a0c 0x381edb4001ffb2a0 0xfdfffc001fff0f07 0x1fdfffc001fff0f0

def z757 : W := mkw 0x02e6d9fb6000000d 0xc02e6d9fb6000000 0x406ffc7be0000000 0x9406ffc7be000000

def z758 : W := mkw 0x50090c09b4714150 0x550090c09b471415 0xedaf1c1ffce343fd 0xfedaf1c1ffce343f

def z759 : W := mkw 0x00002000010a0000 0x000002000010a000 0xdc50e264633f8cff 0xbdc50e264633f8cf

def z760 : W := mkw 0x510924009ffb4150 0x3510924009ffb415 0x010000001fff4307 0x0010000001fff430

def z761 : W := mkw 0x10130e8f24559193 0x510130e8f2455919 0x57b71f986cdfb336 0x957b71f986cdfb33

def z762 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7fe003fc7fc0ffff 0xe7fe003fc7fc0fff

def z763 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xf9fffc181fff0307 0x1f9fffc181fff030

def z764 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xfabfff9fe0000000 0xffabfff9fe000000

def z765 : W := mkw 0x21fdd6245ef584ae 0xb21fdd6245ef584a 0x25af1e647cc08cf8 0xa25af1e647cc08cf

def z766 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xc4281c1ff0e343fd 0x9c4281c1ff0e343f

def z767 : W := mkw 0x501b06869475d1d3 0x1501b06869475d1d 0xffbf1f879cfff3ff 0x7ffbf1f879cfff3f

def z768 : W := mkw 0x50000c09a0414150 0x450000c09a041415 0x44201c1fe0c303f4 0x944201c1fe0c303f

def z769 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xf9dffc001f3f0007 0x1f9dffc001f3f000

def z770 : W := mkw 0x22f6dbff600484af 0xc22f6dbff600484a 0xfeffffffe03c8cfb 0xffeffffffe03c8cf

def z771 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfbffffffff00fc0b 0xffbffffffff00fc0

def z772 : W := mkw 0x22f6dbff600484af 0xc22f6dbff600484a 0xfaffffffe0008c00 0xffaffffffe0008c0

def z773 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfbffff981ffff30f 0x7fbffff981ffff30

def z774 : W := mkw 0x02e6d9fb6000000d 0xc02e6d9fb6000000 0x22affd9be0000000 0x522affd9be000000

def z775 : W := mkw 0x2216daaf600484a7 0xc2216daaf600484a 0x801ffc07e00000f0 0x1801ffc07e00000f

def z776 : W := mkw 0x51edb4009ffb415c 0x351edb4009ffb415 0xfdfffc181fff43ff 0xffdfffc181fff43f

def z777 : W := mkw 0x0216dbff60000007 0xc0216dbff6000000 0x801ffc7fe0000000 0x9801ffc7fe000000

def z778 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x829ffd87e0000000 0x1829ffd87e000000

def z779 : W := mkw 0x410924009ffb4040 0x3410924009ffb404 0x010000001fff40cf 0x0010000001fff40c

def z780 : W := mkw 0x82f6dbff60002a0f 0xc82f6dbff60002a0 0xfeffffffe300ff0f 0xffeffffffe300ff0

def z781 : W := mkw 0x12f6dbff6000011f 0xc12f6dbff6000011 0xfeffffffe0000330 0xffeffffffe000033

def z782 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfaffffe7e0000000 0x1faffffe7e000000

def z783 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xfc58e267e33f8cff 0xffc58e267e33f8cf

def z784 : W := mkw 0xa0f063744b8eaeaa 0xaa0f063744b8eaea 0xa3b0e19c7cff73f0 0x5a3b0e19c7cff73f

def z785 : W := mkw 0xd1ed9d59bef16b5c 0x7d1ed9d59bef16b5 0x23af1d9b9cc07300 0x423af1d9b9cc0730

def z786 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xa19ffc001c3f0000 0x1a19ffc001c3f000

def z787 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x17c003f81fc0ff0f 0xe17c003f81fc0ff0

def z788 : W := mkw 0x02f6daaf6a80000f 0xe02f6daaf6a80000 0xf9fffc07ffc00007 0x1f9fffc07ffc0000

def z789 : W := mkw 0x010db4001ffb0004 0x3010db4001ffb000 0x801ffc0003ff0004 0x1801ffc0003ff000

def z790 : W := mkw 0x01e5b4000fdb000c 0x301e5b4000fdb000 0x4077fc0003df0004 0x14077fc0003df000

def z791 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xcc1ffc04603f00fd 0xbcc1ffc04603f00f

def z792 : W := mkw 0x42edd979f434d0cc 0xd42edd979f434d0c 0x4160fc787c3cf0cb 0x94160fc787c3cf0c

def z793 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xd450e264633f8cf6 0x9d450e264633f8cf

def z794 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0xfff0e3f81fc0ff0f 0xffff0e3f81fc0ff0

def z795 : W := mkw 0x80e491500a802a0c 0x280e491500a802a0 0x7ff7e3f81fc0ff0f 0xe7ff7e3f81fc0ff0

def z796 : W := mkw 0x51e924009ffb4158 0x351e924009ffb415 0x7de000181fff43ff 0xe7de000181fff43f

def z797 : W := mkw 0x50090c09b4714150 0x550090c09b471415 0xffbf1f9ffcfff3ff 0xfffbf1f9ffcfff3f

def z798 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xdc50e064633f0cf7 0x9dc50e064633f0cf

def z799 : W := mkw 0xc1edb5509ffb6a4c 0x3c1edb5509ffb6a4 0xffffffff9fffffcf 0xfffffffff9fffffc

def z800 : W := mkw 0x0216dbff60000007 0xc0216dbff6000000 0x821fffe7e0000000 0x1821fffe7e000000

def z801 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xd2ffffffe0000000 0x9d2ffffffe000000

def z802 : W := mkw 0x82f6dbff60002a0f 0xc82f6dbff60002a0 0xfaffffffe0007300 0xffaffffffe000730

def z803 : W := mkw 0x400b00829434d0c1 0x1400b00829434d0c 0x3b8f03839c3cf0cb 0x63b8f03839c3cf0c

def z804 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfbfffff81fffff07 0x5fbfffff81fffff0

def z805 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xee281f9ff0e3f3fd 0xfee281f9ff0e3f3f

def z806 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfaffffffe3000c00 0xffaffffffe3000c0

def z807 : W := mkw 0x601b42a6d434d4e3 0x9601b42a6d434d4e 0xff9f03e7fc3ffcff 0xfff9f03e7fc3ffcf

def z808 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0xffe81ff81fc0ff0f 0xfffe81ff81fc0ff0

def z809 : W := mkw 0x0013028604149083 0x1001302860414908 0xbb9f03879c1cf00b 0x6bb9f03879c1cf00

def z810 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xfff0e3fc7fffffff 0xffff0e3fc7ffffff

def z811 : W := mkw 0x010db400157b0004 0x1010db400157b000 0x919ffc000c3f0002 0x1919ffc000c3f000

def z812 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xffdf03e7ff3ffcff 0xfffdf03e7ff3ffcf

def z813 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x476003f81fc0ff0f 0xe476003f81fc0ff0

def z814 : W := mkw 0x401b028694305043 0x1401b02869430504 0xbb9f03879c3c7003 0x6bb9f03879c3c700

def z815 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x239f01839c1c7000 0x4239f01839c1c700

def z816 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xc4281c1fe0e343fc 0xfc4281c1fe0e343f

def z817 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x939f03878c3cf0ca 0x6939f03878c3cf0c

def z818 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xdd50e2647f3ffcff 0xbdd50e2647f3ffcf

def z819 : W := mkw 0x00edb000153a000c 0x100edb000153a000 0xf9fffc001f3f0007 0x1f9fffc001f3f000

def z820 : W := mkw 0x82f6dbff6a84aa8f 0xe82f6dbff6a84aa8 0xfffffffffffcffcf 0xffffffffffffcffc

def z821 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xa1bffc001fff0007 0x1a1bffc001fff000

def z822 : W := mkw 0x01e5b0000f9a000c 0x301e5b0000f9a000 0xf9fffc001fdc0007 0x1f9fffc001fdc000

def z823 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbbbf039f9cfcf3cb 0x6bbbf039f9cfcf3c

def z824 : W := mkw 0x51e5b809af9a415c 0x751e5b809af9a415 0x15d7e01fef1c43fa 0xe15d7e01fef1c43f

def z825 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xb89ffc00003f0000 0x1b89ffc00003f000

def z826 : W := mkw 0x00ed90001430000c 0x100ed90001430000 0xf8fffc00003c0000 0x1f8fffc00003c000

def z827 : W := mkw 0x51edb4009ffb415c 0x351edb4009ffb415 0xf9fffc001fff4307 0x1f9fffc001fff430

def z828 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0x981ffe07e0000000 0x3981ffe07e000000

def z829 : W := mkw 0x401b06869475d0c3 0x1401b06869475d0c 0xbb9f1f879c3ff0cb 0x7bb9f1f879c3ff0c

def z830 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xa29ffd87e0000000 0x5a29ffd87e000000

def z831 : W := mkw 0xd0e80d59bae16b58 0x6d0e80d59bae16b5 0x93c81fe7ef23bcf2 0x193c81fe7ef23bcf

def z832 : W := mkw 0xc1e925509ffffac8 0x3c1e925509ffffac 0x7fe003f81fffffcf 0xe7fe003f81fffffc

def z833 : W := mkw 0x22f6dbff600484af 0xc22f6dbff600484a 0xfaffffffe00000f0 0xffaffffffe00000f

def z834 : W := mkw 0x01edb5501ffb000c 0x301edb5501ffb000 0xfbfffff81ffff00f 0xffbfffff81ffff00

def z835 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xc450e064633f8cff 0x9c450e064633f8cf

def z836 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbf9f03879cfcf3cf 0x6bf9f03879cfcf3c

def z837 : W := mkw 0x02124bff60049083 0xc02124bff6004908 0x020003ffe000b000 0xe020003ffe000b00

def z838 : W := mkw 0x00f693d60000000f 0x000f693d60000000 0xfaffffff80000000 0xffaffffff8000000

def z839 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfffffffffcc0ff08 0xffffffffffcc0ff0

def z840 : W := mkw 0x601b42a6d434d4e3 0x9601b42a6d434d4e 0xbb9f0387fc3cf0fb 0x6bb9f0387fc3cf0f

def z841 : W := mkw 0x00e4b150010a000c 0x000e4b150010a000 0xfefffff8033f8c0f 0xffefffff8033f8c0

def z842 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0xffe003f81fe3ff0f 0xfffe003f81fe3ff0

def z843 : W := mkw 0x22f6dbff6000042f 0xc22f6dbff6000042 0xfeffffffe0000c30 0xffeffffffe0000c3

def z844 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xbb9fff87fc00f00b 0x7bb9fff87fc00f00

def z845 : W := mkw 0x510924009ffb4150 0x3510924009ffb415 0x010000001fff00f7 0x0010000001fff00f

def z846 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x44201c1ff0e343fd 0xf44201c1ff0e343f

def z847 : W := mkw 0x20006020410e84a0 0x820006020410e84a 0x4440e060633f0cf4 0x94440e060633f0cf

def z848 : W := mkw 0x8216daaf6a802a07 0xe8216daaf6a802a0 0x851ffc07ffc0ff0f 0x1851ffc07ffc0ff0

def z849 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xdc5ffe67e3008c0f 0xbdc5ffe67e3008c0

def z850 : W := mkw 0xa2f6dbff6a84aeaf 0xea2f6dbff6a84aea 0xffffffffffc0ffff 0xfffffffffffc0fff

def z851 : W := mkw 0x001b028614300003 0x1001b02861430000 0xbb9f03879c3cf00b 0x6bb9f03879c3cf00

def z852 : W := mkw 0x400b00829434d0c1 0x1400b00829434d0c 0xbb9f01839c3cf0cb 0x4bb9f01839c3cf0c

def z853 : W := mkw 0x810db550157b2a04 0x1810db550157b2a0 0x861ffff8003fff08 0xf861ffff8003fff0

def z854 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfafffffb80000000 0x5fafffffb8000000

def z855 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xf8fffc7fe0000000 0x9f8fffc7fe000000

def z856 : W := mkw 0x81edb4001ffb2a0c 0x381edb4001ffb2a0 0xffffff801fffff0f 0x7ffffff801fffff0

def z857 : W := mkw 0x52fed7f6d061415f 0x852fed7f6d061415 0x16d7e3e010e343fd 0x016d7e3e010e343f

def z858 : W := mkw 0x0012028600048083 0x0001202860004808 0xbb9f03879c3cf0cb 0x6bb9f03879c3cf0c

def z859 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfffffff81fff0f07 0xffffffff81fff0f0

def z860 : W := mkw 0x02e699db2000000d 0x402e699db2000000 0xfafffd9fe0000000 0xffafffd9fe000000

def z861 : W := mkw 0x031b6fff7ffb0003 0xf031b6fff7ffb000 0x030003ffffff0007 0xe030003ffffff000

def z862 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xbadfffe7e0000000 0x7badfffe7e000000

def z863 : W := mkw 0x510db400957b4154 0x1510db400957b415 0x841ffc0010ff43fd 0x1841ffc0010ff43f

def z864 : W := mkw 0x010db4001ffb0004 0x3010db4001ffb000 0xd95ffc001fff0007 0x1d95ffc001fff000

def z865 : W := mkw 0x02f6dbff6004808f 0xc02f6dbff6004808 0xfeffffffe03f80ff 0xffeffffffe03f80f

def z866 : W := mkw 0xa2f6f3f64b8eaeaf 0xaa2f6f3f64b8eaea 0x13d7e3e00f1cbc02 0x013d7e3e00f1cbc0

def z867 : W := mkw 0x201262a6410e84a3 0x8201262a6410e84a 0xffdfe3e7ff3ffcff 0xfffdfe3e7ff3ffcf

def z868 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfefffffff3c04f0d 0xffefffffff3c04f0

def z869 : W := mkw 0x01edb400157b000c 0x101edb400157b000 0xc07ffc00003f0000 0x1c07ffc00003f000

def z870 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfaffffffe000800b 0xffaffffffe000800

def z871 : W := mkw 0x02f6dbff6004808f 0xc02f6dbff6004808 0xfbfffffffc3cf0cb 0xffbfffffffc3cf0c

def z872 : W := mkw 0x00e490000000000c 0x000e490000000000 0xf8fffc0780000000 0x7f8fffc078000000

def z873 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xb39f03879c3cf0c2 0x4b39f03879c3cf0c

def z874 : W := mkw 0x02e6d9fb6000000d 0xc02e6d9fb6000000 0xfafffdfbe0000000 0xdfafffdfbe000000

def z875 : W := mkw 0x22124aaf600484a3 0xc22124aaf600484a 0x00000007e00000f0 0x000000007e00000f

def z876 : W := mkw 0x010db400157b0004 0x1010db400157b000 0x801ffc00033f0007 0x1801ffc00033f000

def z877 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xd850e264633f8cf2 0xbd850e264633f8cf

def z878 : W := mkw 0x010db400157b0004 0x1010db400157b000 0x001ffc00001c0000 0x0001ffc00001c000

def z879 : W := mkw 0x610924009fffd4e0 0x3610924009fffd4e 0x050000001ffffcff 0x0050000001ffffcf

def z880 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xffffffffffc00f07 0xfffffffffffc00f0

def z881 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xdc5ffe60033f8c0f 0xbdc5ffe60033f8c0

def z882 : W := mkw 0x81e5b5500fdb2a0c 0x381e5b5500fdb2a0 0x57f7fff80fdfbf06 0x957f7fff80fdfbf0

def z883 : W := mkw 0x51092400957b4150 0x151092400957b415 0x0400000010ff43fd 0x00400000010ff43f

def z884 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x92dfffffe0000000 0xf92dfffffe000000

def z885 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xdc70e27c63ff8fff 0xbdc70e27c63ff8ff

def z886 : W := mkw 0x00e498092000000c 0x400e498092000000 0xf8fffc1b80000000 0x5f8fffc1b8000000

def z887 : W := mkw 0x01e5b4000fdb000c 0x301e5b4000fdb000 0xf9fffc000fdf0006 0x1f9fffc000fdf000

def z888 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfaffffffe03c0003 0xffaffffffe03c000

def z889 : W := mkw 0x010db4001ffb0004 0x3010db4001ffb000 0x811ffc001cff0000 0x1811ffc001cff000

def z890 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xfc70e27c633f8cff 0xffc70e27c633f8cf

def z891 : W := mkw 0x0216daaf60048087 0xc0216daaf6004808 0x981ffe07e03c80cb 0x3981ffe07e03c80c

def z892 : W := mkw 0xa2f24bff6a84aeab 0xea2f24bff6a84aea 0x7fe003ffffc0ffff 0xe7fe003ffffc0fff

def z893 : W := mkw 0x0004980920000004 0x4000498092000000 0xe83ffc1fe0000000 0xfe83ffc1fe000000

def z894 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfdfffc781fffff0f 0x9fdfffc781fffff0

def z895 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbb9f01879c3c70c3 0x4bb9f01879c3c70c

def z896 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffe647fff8cff 0xbfdfffe647fff8cf

def z897 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xc27fffffe0000000 0xfc27fffffe000000

def z898 : W := mkw 0x00124aaf60000003 0xc00124aaf6000000 0xfaffffffe0000000 0xffaffffffe000000

def z899 : W := mkw 0x00e498092a80000c 0x600e498092a80000 0xfdfffc1fffc0430f 0xffdfffc1fffc0430

def z900 : W := mkw 0x710924009fffc5f0 0x3710924009fffc5f 0x050000001fffcfff 0x0050000001fffcff

def z901 : W := mkw 0x001b028614349083 0x1001b02861434908 0xbb9f03879c3cb003 0x6bb9f03879c3cb00

def z902 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x7afffffb80000000 0xe7afffffb8000000

def z903 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfafffffff0004009 0xffafffffff000400

def z904 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfeffffffe00000f8 0xffeffffffe00000f

def z905 : W := mkw 0x0016928600000007 0x0001692860000000 0x801ffc0780000000 0x1801ffc078000000

def z906 : W := mkw 0x41edb4009ffb504c 0x341edb4009ffb504 0xf9fffc001fff7007 0x1f9fffc001fff700

def z907 : W := mkw 0xc2124bffe004fac3 0xcc2124bffe004fac 0x060003ffe000ffc8 0xe060003ffe000ffc

def z908 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xffffffffffc07f04 0xfffffffffffc07f0

def z909 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfeffffffe0030034 0xffeffffffe003003

def z910 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xa39f03879c3cf0c8 0x6a39f03879c3cf0c

def z911 : W := mkw 0x01ed94001ef1000c 0x301ed94001ef1000 0xf9fffc001cfc0003 0x1f9fffc001cfc000

def z912 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfbfffffffc007000 0xffbfffffffc00700

def z913 : W := mkw 0x401b06869475d0c3 0x1401b06869475d0c 0xffbf1f87fcfff0ff 0xfffbf1f87fcfff0f

def z914 : W := mkw 0x01e5b4000fdb000c 0x301e5b4000fdb000 0x11f7fc000fdc0002 0x011f7fc000fdc000

def z915 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xffffffe01ffffc0f 0xfffffffe01ffffc0

def z916 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xffffffffffe3ffff 0xfffffffffffe3fff

def z917 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfeffffffe0008c08 0xffeffffffe0008c0

def z918 : W := mkw 0x02f6daaf6000000f 0xc02f6daaf6000000 0xc07ffc07e0000000 0x1c07ffc07e000000

def z919 : W := mkw 0x01e5b000051a000c 0x101e5b000051a000 0xf8fffc00001c0000 0x1f8fffc00001c000

def z920 : W := mkw 0x400b008294305041 0x1400b00829430504 0x339f01839c1c7002 0x4339f01839c1c700

def z921 : W := mkw 0x42124aafe004d0c3 0xc42124aafe004d0c 0x02000387e000f0c8 0x602000387e000f0c

def z922 : W := mkw 0x800001500a802a00 0x2800001500a802a0 0x3f8003f81fc0ff0f 0xe3f8003f81fc0ff0

def z923 : W := mkw 0x52124bffe004d1d3 0xc52124bffe004d1d 0x060003ffe000f3f8 0xe060003ffe000f3f

def z924 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xc81ffc00003f0005 0x1c81ffc00003f000

def z925 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x9450e264633f8cff 0x19450e264633f8cf

def z926 : W := mkw 0x01edb5501ffb000c 0x301edb5501ffb000 0xfffffff81fff430f 0xffffffff81fff430

def z927 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfeffffffe000000d 0xffeffffffe000000

def z928 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xab9f01879c3c70c9 0x6ab9f01879c3c70c

def z929 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0x905ffe67e0000000 0x1905ffe67e000000

def z930 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0xffe003fc1fe0ffcf 0xeffe003fc1fe0ffc

def z931 : W := mkw 0x70092400957fd5f0 0x170092400957fd5f 0x050000001fffffff 0x0050000001ffffff

def z932 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xffffffffff00fc0f 0xfffffffffff00fc0

def z933 : W := mkw 0x000d900014300004 0x1000d90001430000 0xb99ffc001c3c0003 0x1b99ffc001c3c000

def z934 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfbfffd801fff3007 0x1fbfffd801fff300

def z935 : W := mkw 0x02f69bdf2000000f 0x402f69bdf2000000 0xfaffff9f80000000 0x7faffff9f8000000

def z936 : W := mkw 0x401b42a6d434d0c3 0x9401b42a6d434d0c 0xbb9fe387fc3cf0cb 0x7bb9fe387fc3cf0c

def z937 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x71fffc001fdf0006 0x171fffc001fdf000

def z938 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffe001fff800f 0x3f9fffe001fff800

def z939 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xd9dffc000f3f0007 0x1d9dffc000f3f000

def z940 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7be003f81fc0ff02 0xe7be003f81fc0ff0

def z941 : W := mkw 0x02f6daaf6000000f 0xc02f6daaf6000000 0xf8fffe67e0000000 0xbf8fffe67e000000

def z942 : W := mkw 0x201262a6410e84a3 0x8201262a6410e84a 0xdc5fe267e33f8cff 0xbdc5fe267e33f8cf

def z943 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0x001ffc0380000000 0x0001ffc038000000

def z944 : W := mkw 0x02f6dbff6004808f 0xc02f6dbff6004808 0xfaffffffe01c8002 0xffaffffffe01c800

def z945 : W := mkw 0x600b60a2d53a5461 0x9600b60a2d53a546 0x67cfe1e3ff037c34 0xd67cfe1e3ff037c3

def z946 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xfbdfe3879c3cf0cb 0x7fbdfe3879c3cf0c

def z947 : W := mkw 0x02e699db2000000d 0x402e699db2000000 0xfafffffb80000000 0xffafffffb8000000

def z948 : W := mkw 0x22124bff600484a3 0xc22124bff600484a 0x020003ffe0008c00 0xe020003ffe0008c0

def z949 : W := mkw 0x401b06869475d0c3 0x1401b06869475d0c 0xffbf1f9f9cfff3cf 0xfffbf1f9f9cfff3c

def z950 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfeffffffe3c08f0f 0xffeffffffe3c08f0

def z951 : W := mkw 0x22f6dbff600484af 0xc22f6dbff600484a 0xfeffffffe3008cff 0xffeffffffe3008cf

def z952 : W := mkw 0x81edb4001ffb2a0c 0x381edb4001ffb2a0 0xf9fffc001fff7307 0x1f9fffc001fff730

def z953 : W := mkw 0x80e4b1500b8a2a0c 0x280e4b1500b8a2a0 0xfffffff81fffff0f 0xffffffff81fffff0

def z954 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xfadfffe7e0000000 0xffadfffe7e000000

def z955 : W := mkw 0x800001500a802a00 0x2800001500a802a0 0x6f2003f81fc0ff0f 0xe6f2003f81fc0ff0

def z956 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfbffff801fff0007 0x7fbffff801fff000

def z957 : W := mkw 0x400b00829434d0c1 0x1400b00829434d0c 0x238f01839c3c70c0 0x4238f01839c3c70c

def z958 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfffffffffcc0f30f 0xffffffffffcc0f30

def z959 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xe87ffc7fe0000000 0xfe87ffc7fe000000

def z960 : W := mkw 0x22f24bff600484ab 0xc22f24bff600484a 0x7ee003ffe3008cff 0xe7ee003ffe3008cf

def z961 : W := mkw 0x510db400957b4154 0x1510db400957b415 0x801ffc00003f00f0 0x1801ffc00003f00f

def z962 : W := mkw 0xd1edb4009ffb6b5c 0x3d1edb4009ffb6b5 0xfdfffc001fffffff 0x1fdfffc001ffffff

def z963 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0x801ffe67e0000000 0xb801ffe67e000000

def z964 : W := mkw 0x82f6dbff60002a0f 0xc82f6dbff60002a0 0xfefffffff0c0ff0d 0xffefffffff0c0ff0

def z965 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffc1c7fff43ff 0xffdfffc1c7fff43f

def z966 : W := mkw 0x00e498092000000c 0x400e498092000000 0xf8fffc07e0000000 0x1f8fffc07e000000

def z967 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfbfffff81fff7307 0xffbfffff81fff730

def z968 : W := mkw 0x00f69a8f2000000f 0x400f69a8f2000000 0xfaffff9fe0000000 0xffaffff9fe000000

def z969 : W := mkw 0x701b6eaff57fd5f3 0xd701b6eaff57fd5f 0x801ffc07e03f00f0 0x1801ffc07e03f00f

def z970 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfaffffffe0c00300 0xffaffffffe0c0030

def z971 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfefffffff0e343fd 0xffefffffff0e343f

def z972 : W := mkw 0x401302868414d0c3 0x1401302868414d0c 0x139703878c1cb0c2 0x0139703878c1cb0c

def z973 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xb9bffc001cff0003 0x1b9bffc001cff000

def z974 : W := mkw 0x51092400957b4150 0x151092400957b415 0x00000000003f00f0 0x000000000003f00f

def z975 : W := mkw 0x50000c09a0414150 0x450000c09a041415 0xcc201c1fe0e343fd 0xfcc201c1fe0e343f

def z976 : W := mkw 0xd1edb5509ffb6b5c 0x3d1edb5509ffb6b5 0xfffffff81fffffff 0xffffffff81ffffff

def z977 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xe9bffc001cff0005 0x1e9bffc001cff000

def z978 : W := mkw 0x41edb4009ffb404c 0x341edb4009ffb404 0xf9fffc079fff00c7 0x1f9fffc079fff00c

def z979 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xfc681e7ff0e343fd 0xffc681e7ff0e343f

def z980 : W := mkw 0x010db400157b0004 0x1010db400157b000 0x811ffc001c3f0003 0x1811ffc001c3f000

def z981 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfbffffffec00b002 0xffbffffffec00b00

def z982 : W := mkw 0xc0fb03d69eb4facb 0x3c0fb03d69eb4fac 0xc47f007f83fc0fc4 0x8c47f007f83fc0fc

def z983 : W := mkw 0x0004b000010a0004 0x00004b000010a000 0xd85ffc00033f0007 0x1d85ffc00033f000

def z984 : W := mkw 0x02e6d9fb6000000d 0xc02e6d9fb6000000 0x7aeffffbe0000000 0xf7aeffffbe000000

def z985 : W := mkw 0x00e490000000000c 0x000e490000000000 0xf8fffc00003c0003 0x1f8fffc00003c000

def z986 : W := mkw 0x01e5b0000f9a000c 0x301e5b0000f9a000 0xf9fffc000f3f0007 0x1f9fffc000f3f000

def z987 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfaffffffe02300f0 0xffaffffffe02300f

def z988 : W := mkw 0x82f6dbff60002a0f 0xc82f6dbff60002a0 0xfaffffffe000bc00 0xffaffffffe000bc0

def z989 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xdadfffe7e0000000 0xbdadfffe7e000000

def z990 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x1450e264633f8cff 0xa1450e264633f8cf

def z991 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xa81ffc00103f0001 0x1a81ffc00103f000

def z992 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbf9f03879c3ff0ff 0x6bf9f03879c3ff0f

def z993 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xb9dffc001f3f0003 0x1b9dffc001f3f000

def z994 : W := mkw 0x51edb4009ffb415c 0x351edb4009ffb415 0xfdfffc079fff43ff 0x7fdfffc079fff43f

def z995 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x839f01878c3c30c0 0x0839f01878c3c30c

def z996 : W := mkw 0x02f6daaf6000000f 0xc02f6daaf6000000 0x90dffc07e0000000 0x190dffc07e000000

def z997 : W := mkw 0x0004b000010a0004 0x00004b000010a000 0x801ffc00003f0000 0x1801ffc00003f000

def z998 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x3b9f03839c1cf00b 0x63b9f03839c1cf00

def z999 : W := mkw 0x00f6d2a64000000f 0x800f6d2a64000000 0xfaffffe7e0000000 0xffaffffe7e000000

def z1000 : W := mkw 0x82e6d9fb6a802a0d 0xe82e6d9fb6a802a0 0x7feffffbffc0ff0f 0xf7feffffbffc0ff0

def z1001 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xffe81fffffe3ffff 0xfffe81fffffe3fff

def z1002 : W := mkw 0x02f6dbff6a80000f 0xe02f6dbff6a80000 0xffffffffffc08c0f 0xfffffffffffc08c0

def z1003 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc001fdc0002 0x1f9fffc001fdc000

def z1004 : W := mkw 0x01edb400157b000c 0x101edb400157b000 0xf8fffc0010ff0005 0x1f8fffc0010ff000

def z1005 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfeffffffe3238cff 0xffeffffffe3238cf

def z1006 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfaffffffe0230005 0xffaffffffe023000

def z1007 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc181fff0007 0xff9fffc181fff000

def z1008 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xec3ffc1ff0c0430d 0xfec3ffc1ff0c0430

def z1009 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfffffffc7fffffff 0xffffffffc7ffffff

def z1010 : W := mkw 0x01edb0001fba000c 0x301edb0001fba000 0xf9fffc001f3c0003 0x1f9fffc001f3c000

def z1011 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x238f03879c3cf0cb 0x6238f03879c3cf0c

def z1012 : W := mkw 0x41edb4009ffb404c 0x341edb4009ffb404 0xf9fffc039fff4007 0x5f9fffc039fff400

def z1013 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfbfffffffcc0f30b 0xffbfffffffcc0f30

def z1014 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x9850e264633f8cfb 0x39850e264633f8cf

def z1015 : W := mkw 0x50090c09b4714150 0x550090c09b471415 0xec3f1c1ff0ff43fd 0xfec3f1c1ff0ff43f

def z1016 : W := mkw 0x41edb4009ffb404c 0x341edb4009ffb404 0xfdfffc07ffff40ff 0xffdfffc07ffff40f

def z1017 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0xffff03f81fc0ff0f 0xeffff03f81fc0ff0

def z1018 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xfbdf03879f3cf0cf 0x6fbdf03879f3cf0c

def z1019 : W := mkw 0x00e4b0000b8a000c 0x200e4b0000b8a000 0xf9fffc001fff0007 0x1f9fffc001fff000

def z1020 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xec281e7ff0e3cffd 0xfec281e7ff0e3cff

def z1021 : W := mkw 0x0206d8ab60000005 0xc0206d8ab6000000 0x000ffc03e0000000 0x1000ffc03e000000

def z1022 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0x33fffffb9fc0ff02 0x433fffffb9fc0ff0

def z1023 : W := mkw 0x010db400157b0004 0x1010db400157b000 0x981ffc00003f0003 0x1981ffc00003f000

def z1024 : W := mkw 0x20006020410a0420 0x820006020410a042 0xdc50e064633f0cff 0xbdc50e064633f0cf

def z1025 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfbffff801fffb007 0x1fbffff801fffb00

def z1026 : W := mkw 0x400b008294305041 0x1400b00829430504 0xbb9f01879c3c70cb 0x6bb9f01879c3c70c

def z1027 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0x801ffc07e02300f0 0x1801ffc07e02300f

def z1028 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xffffffe01fffff0f 0x1ffffffe01fffff0

def z1029 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x37e003f81fc0ff0f 0x437e003f81fc0ff0

def z1030 : W := mkw 0x401b42a6d434d0c3 0x9401b42a6d434d0c 0xffdfe3e7fc3ff0ff 0xfffdfe3e7fc3ff0f

def z1031 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfafffffff0c04300 0xffafffffff0c0430

def z1032 : W := mkw 0x0013028604149083 0x1001302860414908 0x339f03838c1cb002 0x4339f03838c1cb00

def z1033 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfdfffc781fff4f0f 0xffdfffc781fff4f0

def z1034 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x939f03879c3cf0cb 0x0939f03879c3cf0c

def z1035 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffe601fff8c07 0x1f9fffe601fff8c0

def z1036 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xfb9f03879c3ff0cf 0x7fb9f03879c3ff0c

def z1037 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x819ffc000c3f0000 0x1819ffc000c3f000

def z1038 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfefffffff3c0cf0f 0xffefffffff3c0cf0

def z1039 : W := mkw 0x80f693d60a802a0f 0x280f693d60a802a0 0xffffffff9fc0ff0f 0xfffffffff9fc0ff0

def z1040 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xa3bffd981cff7300 0x5a3bffd981cff730

def z1041 : W := mkw 0x010db4001ffb0004 0x3010db4001ffb000 0x811ffc000f3f0002 0x1811ffc000f3f000

def z1042 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfeffffffe0c00304 0xffeffffffe0c0030

def z1043 : W := mkw 0x01edb550157b000c 0x101edb550157b000 0xfafffff8003f0000 0xffafffff8003f000

def z1044 : W := mkw 0x02e6d9fb6000000d 0xc02e6d9fb6000000 0xeaeffdffe0000000 0xfeaeffdffe000000

def z1045 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbb9f0387fc3ff0fb 0x7bb9f0387fc3ff0f

def z1046 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfeffffffe3c0ff0c 0xffeffffffe3c0ff0

def z1047 : W := mkw 0x501b02869434d1d3 0x1501b02869434d1d 0xbf9f03879c3cf3fb 0x6bf9f03879c3cf3f

def z1048 : W := mkw 0x201262a6410e94a3 0x8201262a6410e94a 0xde50e3e4633fbcff 0xbde50e3e4633fbcf

def z1049 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xd850e264633f8cf7 0x1d850e264633f8cf

def z1050 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xc03ffc0000ff0004 0x1c03ffc0000ff000

def z1051 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xa39f01879c3cf0cb 0x4a39f01879c3cf0c

def z1052 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xd1fffc000fff0006 0x1d1fffc000fff000

def z1053 : W := mkw 0x601b42a6d434d4e3 0x9601b42a6d434d4e 0xffdfe3e7fc3cfcfb 0xfffdfe3e7fc3cfcf

def z1054 : W := mkw 0x400b00829434d0c1 0x1400b00829434d0c 0x238f01839c1cf002 0x4238f01839c1cf00

def z1055 : W := mkw 0x401302868414d0c3 0x1401302868414d0c 0x3b9703879c1cf0cb 0x63b9703879c1cf0c

def z1056 : W := mkw 0x02f6dbff6004808f 0xc02f6dbff6004808 0xfaffffffe03c00c0 0xffaffffffe03c00c

def z1057 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x139f03838c1cb002 0x0139f03838c1cb00

def z1058 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xffffffffefc0bf06 0xfffffffffefc0bf0

def z1059 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0x929fff87e0000000 0x1929fff87e000000

def z1060 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xec281c1ff0e303f5 0x9ec281c1ff0e303f

def z1061 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xc47ffc7803ff0f04 0x9c47ffc7803ff0f0

def z1062 : W := mkw 0x010db4001ffb0004 0x3010db4001ffb000 0xe93ffc001fff0007 0x1e93ffc001fff000

def z1063 : W := mkw 0x80ed91501eb02a0c 0x380ed91501eb02a0 0xfffffff81ffcff0f 0xffffffff81ffcff0

def z1064 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0x93dfffe00f3fbc02 0x193dfffe00f3fbc0

def z1065 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xa3bffd9ffcc07300 0x5a3bffd9ffcc0730

def z1066 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfbffffffffc07307 0xffbffffffffc0730

def z1067 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x803ffc1fe0000000 0x1803ffc1fe000000

def z1068 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffc181fff0307 0x9fdfffc181fff030

def z1069 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xec3ffc1810ff430d 0xfec3ffc1810ff430

def z1070 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfaffffffe3008c02 0xffaffffffe3008c0

def z1071 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf8fffc0003ff0004 0x1f8fffc0003ff000

def z1072 : W := mkw 0x02f6dbff6a80000f 0xe02f6dbff6a80000 0xfbfffffffcc00000 0xffbfffffffcc0000

def z1073 : W := mkw 0x01edb400157b000c 0x101edb400157b000 0x90dffc00003f0000 0x190dffc00003f000

def z1074 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfaffffffe3000007 0xffaffffffe300000

def z1075 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xfda81c1ffce343ff 0xffda81c1ffce343f

def z1076 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc047fff0007 0xbf9fffc047fff000

def z1077 : W := mkw 0x010db400157b0004 0x1010db400157b000 0x905ffc00033f0002 0x1905ffc00033f000

def z1078 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xfbdf03e79c3cf0cb 0xefbdf03e79c3cf0c

def z1079 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffc001fff8c0f 0x1fdfffc001fff8c0

def z1080 : W := mkw 0x02f6dbff6004808f 0xc02f6dbff6004808 0xfeffffffe33c8ccf 0xffeffffffe33c8cc

def z1081 : W := mkw 0xa2124bff6004aea3 0xca2124bff6004aea 0x060003ffe000fff8 0xe060003ffe000fff

def z1082 : W := mkw 0x501b06869475d1d3 0x1501b06869475d1d 0xbb9f03879cfcf3cb 0x6bb9f03879cfcf3c

def z1083 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xc05ffc00033f0004 0x1c05ffc00033f000

def z1084 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfffffd981fffff0f 0x5fffffd981fffff0

def z1085 : W := mkw 0x02f6d3f64000000f 0x802f6d3f64000000 0xfaffffe780000000 0x7faffffe78000000

def z1086 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xfed0e3e4633f8cff 0xffed0e3e4633f8cf

def z1087 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfaffffffe02000c9 0xffaffffffe02000c

def z1088 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xeabffd9fe0000000 0xfeabffd9fe000000

def z1089 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbbdf03e79f3cfccb 0x6bbdf03e79f3cfcc

def z1090 : W := mkw 0x2216daaf600484a7 0xc2216daaf600484a 0x841ffe67e0008cf8 0xb841ffe67e0008cf

def z1091 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xdc50e27c633fcfff 0xfdc50e27c633fcff

def z1092 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfbffffffffc0ff02 0xffbffffffffc0ff0

def z1093 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xf87ffc0013ff0007 0x1f87ffc0013ff000

def z1094 : W := mkw 0x0216dbff60000007 0xc0216dbff6000000 0xba9fffffe0000000 0xfba9fffffe000000

def z1095 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7fe003f81fe3ffff 0xe7fe003f81fe3fff

def z1096 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbb9f03878c3cb0c2 0x6bb9f03878c3cb0c

def z1097 : W := mkw 0x0216daaf60048087 0xc0216daaf6004808 0x801ffc07e03c00c0 0x1801ffc07e03c00c

def z1098 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xfc70e26473ff8cff 0xbfc70e26473ff8cf

def z1099 : W := mkw 0x41092400957fd0c0 0x141092400957fd0c 0x010000001c3ff0cb 0x0010000001c3ff0c

def z1100 : W := mkw 0x20006020410e84a0 0x820006020410e84a 0x5c40e260633f8cff 0xb5c40e260633f8cf

def z1101 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xfc281e1ff0e3c3ff 0xffc281e1ff0e3c3f

def z1102 : W := mkw 0x02f6dbff6004908f 0xc02f6dbff6004908 0xfaffffffe000b000 0xffaffffffe000b00

def z1103 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x72fffffbe0000000 0xd72fffffbe000000

def z1104 : W := mkw 0x01edb5501ffb000c 0x301edb5501ffb000 0xfbfffd981fff0007 0x5fbfffd981fff000

def z1105 : W := mkw 0x0216dbff60000007 0xc0216dbff6000000 0xea3fffffe0000000 0xfea3fffffe000000

def z1106 : W := mkw 0x00e4b000010a000c 0x000e4b000010a000 0xf8fffc00031c0002 0x1f8fffc00031c000

def z1107 : W := mkw 0x10000c0920410110 0x410000c092041011 0xec281c1fe0e303fd 0xfec281c1fe0e303f

def z1108 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xa03ffc0010ff0000 0x1a03ffc0010ff000

def z1109 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x5450e260633f8cff 0x95450e260633f8cf

def z1110 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xb1fffc001fff0002 0x1b1fffc001fff000

def z1111 : W := mkw 0x02e699db2000000d 0x402e699db2000000 0x62effd9b80000000 0x562effd9b8000000

def z1112 : W := mkw 0x82e699db2a802a0d 0x682e699db2a802a0 0xfffffffb9fc0ff0f 0xffffffffb9fc0ff0

def z1113 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xb89ffc07e0000000 0x1b89ffc07e000000

def z1114 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfeffffffe3000c04 0xffeffffffe3000c0

def z1115 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xa03ffc1fe0000000 0x5a03ffc1fe000000

def z1116 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xe1fffc001fff0004 0x1e1fffc001fff000

def z1117 : W := mkw 0x22124bff600484a3 0xc22124bff600484a 0x020003ffe00000f0 0xe020003ffe00000f

def z1118 : W := mkw 0xc10924009ffffac0 0x3c10924009ffffac 0x050000001fffffcf 0x0050000001fffffc

def z1119 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0x7ffffffb9fc0ff0f 0xe7ffffffb9fc0ff0

def z1120 : W := mkw 0x81edb4001ffb2a0c 0x381edb4001ffb2a0 0xf9fffc001fffbc07 0x1f9fffc001fffbc0

def z1121 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffe601fff0007 0xbf9fffe601fff000

def z1122 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xe83ffc07e0000000 0x1e83ffc07e000000

def z1123 : W := mkw 0x41edb4009ffb404c 0x341edb4009ffb404 0xfdfffc1f9fff43cf 0xffdfffc1f9fff43c

def z1124 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfbfffff81fffbc07 0xffbfffff81fffbc0

def z1125 : W := mkw 0x50090c09b4715150 0x550090c09b471515 0xed281c1ffce373fd 0xfed281c1ffce373f

def z1126 : W := mkw 0x02f6dbff6004808f 0xc02f6dbff6004808 0xfaffffffe00080c8 0xffaffffffe00080c

def z1127 : W := mkw 0x8216dbff60002a07 0xc8216dbff60002a0 0x861fffffe000ff08 0xf861fffffe000ff0

def z1128 : W := mkw 0x401b06869475d0c3 0x1401b06869475d0c 0xbb9f03879cfff0cf 0x6bb9f03879cfff0c

def z1129 : W := mkw 0xd1e925509ffb6b58 0x3d1e925509ffb6b5 0x7fe003f81fffffff 0xe7fe003f81ffffff

def z1130 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xc03ffc1fe0000000 0x9c03ffc1fe000000

def z1131 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfafffd9fe0000000 0x5fafffd9fe000000

def z1132 : W := mkw 0x42124aafe004d0c3 0xc42124aafe004d0c 0x00000007e00000c0 0x000000007e00000c

def z1133 : W := mkw 0x0013028604149083 0x1001302860414908 0x139703878c1cb002 0x6139703878c1cb00

def z1134 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfaffffffe000f008 0xffaffffffe000f00

def z1135 : W := mkw 0x02e699db2000000d 0x402e699db2000000 0xa2bffd9b80000000 0x5a2bffd9b8000000

def z1136 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xfbffffffffc0bc07 0xffbffffffffc0bc0

def z1137 : W := mkw 0x01edb400157b000c 0x101edb400157b000 0xf8fffc00033f0007 0x1f8fffc00033f000

def z1138 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xed281c1ffce3f3ff 0xfed281c1ffce3f3f

def z1139 : W := mkw 0x401b42a6d434d0c3 0x9401b42a6d434d0c 0xbb9f03e7fc3cf0cb 0xebb9f03e7fc3cf0c

def z1140 : W := mkw 0x400b00829434d0c1 0x1400b00829434d0c 0xab8f01879c3cf0cb 0x6ab8f01879c3cf0c

def z1141 : W := mkw 0x0216dbff60000007 0xc0216dbff6000000 0x821ffd9fe0000000 0x5821ffd9fe000000

def z1142 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x9b9f03878c3cb0cb 0x29b9f03878c3cb0c

def z1143 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x64281c1ff0c343fc 0xf64281c1ff0c343f

def z1144 : W := mkw 0x02e699db2000000d 0x402e699db2000000 0x32fffd9b80000000 0x432fffd9b8000000

def z1145 : W := mkw 0x00f692860a80000f 0x200f692860a80000 0xfbffff879fc0f00f 0x7fbffff879fc0f00

def z1146 : W := mkw 0x00e690820000000d 0x000e690820000000 0xfafffd8380000000 0x5fafffd838000000

def z1147 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbb9f03879c1cf002 0x6bb9f03879c1cf00

def z1148 : W := mkw 0x010db4001ffb0004 0x3010db4001ffb000 0xb99ffc001fff0007 0x1b99ffc001fff000

def z1149 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffc001fff000f 0xbfdfffc001fff000

def z1150 : W := mkw 0x01e5b4000fdb000c 0x301e5b4000fdb000 0x79f7fc001fdf0007 0x179f7fc001fdf000

def z1151 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xec681c7ff3e34ffd 0xfec681c7ff3e34ff

def z1152 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xc47ffc7fe3c00f04 0x9c47ffc7fe3c00f0

def z1153 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xfbbf1f879c3cf0cb 0x7fbbf1f879c3cf0c

def z1154 : W := mkw 0x01edb400157b000c 0x101edb400157b000 0xa0bffc00003f0000 0x1a0bffc00003f000

def z1155 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0x93dfffe7ef00bc02 0x193dfffe7ef00bc0

def z1156 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xe2fffdffe0000000 0xde2fffdffe000000

def z1157 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfdfffe781fff8f0f 0xbfdfffe781fff8f0

def z1158 : W := mkw 0x510924009fffd1d0 0x3510924009fffd1d 0x050000001ffff3ff 0x0050000001ffff3f

def z1159 : W := mkw 0x401b06869475d0c3 0x1401b06869475d0c 0xbbbf1f879cfcf0cb 0x6bbbf1f879cfcf0c

def z1160 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc181fff4307 0x5f9fffc181fff430

def z1161 : W := mkw 0x70124aafe004d5f3 0xc70124aafe004d5f 0x060003ffe000fff8 0xe060003ffe000fff

def z1162 : W := mkw 0x22124aaf600484a3 0xc22124aaf600484a 0x04000267e0008cf8 0xa04000267e0008cf

def z1163 : W := mkw 0x00ecb400116b000c 0x000ecb400116b000 0xf8fffc0013ff0007 0x1f8fffc0013ff000

def z1164 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xffff03ff9ffcffcf 0xeffff03ff9ffcffc

def z1165 : W := mkw 0x0013028604149083 0x1001302860414908 0x939f03878c1cb002 0x0939f03878c1cb00

def z1166 : W := mkw 0x82e6d9fb6a802a0d 0xe82e6d9fb6a802a0 0x67effdfbffc07f04 0xd67effdfbffc07f0

def z1167 : W := mkw 0x800001500a802a00 0x2800001500a802a0 0x5f4003f81fc0ff0f 0xe5f4003f81fc0ff0

def z1168 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x8050e064633f0cf0 0x18050e064633f0cf

def z1169 : W := mkw 0x80e491500a802a0c 0x280e491500a802a0 0x7fe0fff81fc0ff0f 0xf7fe0fff81fc0ff0

def z1170 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0xffe003fc7fc0ff0f 0xfffe003fc7fc0ff0

def z1171 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xec281c1fe0e303f4 0xfec281c1fe0e303f

def z1172 : W := mkw 0x400b008294305041 0x1400b00829430504 0xa39f01839c3c7000 0x4a39f01839c3c700

def z1173 : W := mkw 0x91e4bd592bcb2b1c 0x691e4bd592bcb2b1 0x4460fc7863c30f34 0x94460fc7863c30f3

def z1174 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc041fff00cf 0x3f9fffc041fff00c

def z1175 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0xffe803ff9fc0ff0f 0xeffe803ff9fc0ff0

def z1176 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xc17ffc001fff0007 0x1c17ffc001fff000

def z1177 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x339f03879c1cf0ca 0x6339f03879c1cf0c

def z1178 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xe8281c1ff0e343f5 0x5e8281c1ff0e343f

def z1179 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xd85ffc00003f0000 0x1d85ffc00003f000

def z1180 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffc007fff0037 0x9fdfffc007fff003

def z1181 : W := mkw 0x02f6daaf6000000f 0xc02f6daaf6000000 0xfaffff87e0000000 0x7faffff87e000000

def z1182 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xf87ffe7fe0000000 0xff87ffe7fe000000

def z1183 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xe87ffc0013ff0005 0x1e87ffc0013ff000

def z1184 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfffffd981fff730f 0xffffffd981fff730

def z1185 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x27a003f81fc0ff0f 0xe27a003f81fc0ff0

def z1186 : W := mkw 0x21edb4001ffb042c 0x321edb4001ffb042 0xfdfffc001fff0c37 0x1fdfffc001fff0c3

def z1187 : W := mkw 0x41e924009fffd0c8 0x341e924009fffd0c 0x7be003801ffff0cf 0x67be003801ffff0c

def z1188 : W := mkw 0x72124bffe004c5f3 0xc72124bffe004c5f 0x060003ffe000cff8 0xe060003ffe000cff

def z1189 : W := mkw 0x501b06869475d1d3 0x1501b06869475d1d 0xbb9f03879c3ff0fb 0x6bb9f03879c3ff0f

def z1190 : W := mkw 0x201262a6410e84a3 0x8201262a6410e84a 0xded7e3e4633f8cff 0xbded7e3e4633f8cf

def z1191 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xfc381c1ff0ff43ff 0xffc381c1ff0ff43f

def z1192 : W := mkw 0x02f6dbff6a80000f 0xe02f6dbff6a80000 0xfbffffffffc0f00f 0xffbffffffffc0f00

def z1193 : W := mkw 0x501b06869475d1d3 0x1501b06869475d1d 0xff9f0387fcfff3ff 0xfff9f0387fcfff3f

def z1194 : W := mkw 0x01e5b0000f9a000c 0x301e5b0000f9a000 0x91dffc000f1c0002 0x191dffc000f1c000

def z1195 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x67e003f81fc0ff0c 0xe67e003f81fc0ff0

def z1196 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x77e003f81fc0ff06 0xc77e003f81fc0ff0

def z1197 : W := mkw 0x41092400957fd0c0 0x141092400957fd0c 0x00000000003f00c0 0x000000000003f00c

def z1198 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0x821fff87e0000000 0x7821fff87e000000

def z1199 : W := mkw 0x000d900014300004 0x1000d90001430000 0x801ffc00003c0000 0x1801ffc00003c000

def z1200 : W := mkw 0x0105b400055b0004 0x10105b400055b000 0x0017fc00001f0000 0x10017fc00001f000

def z1201 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xfcdfe264633f8cff 0xbfcdfe264633f8cf

def z1202 : W := mkw 0x20006020410e84a0 0x820006020410e84a 0xdc50e060633f8cff 0x9dc50e060633f8cf

def z1203 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x11dffc000f1c0002 0x011dffc000f1c000

def z1204 : W := mkw 0x01e5b4000fdb000c 0x301e5b4000fdb000 0x11d7fc000f1f0002 0x111d7fc000f1f000

def z1205 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xe8281c1ff0e343f0 0xfe8281c1ff0e343f

def z1206 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xffbf039ffcfff3ff 0xfffbf039ffcfff3f

def z1207 : W := mkw 0x01edb400157b000c 0x101edb400157b000 0xf9fffc001c3f0003 0x1f9fffc001c3f000

def z1208 : W := mkw 0x401302868414d0c3 0x1401302868414d0c 0x139703838c1cf002 0x4139703838c1cf00

def z1209 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc001cff0000 0x1f9fffc001cff000

def z1210 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xd87ffc0003ff0007 0x1d87ffc0003ff000

def z1211 : W := mkw 0x01e4b4000bcb000c 0x201e4b4000bcb000 0xf8fffc0003ff0007 0x1f8fffc0003ff000

def z1212 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xcc1ffc07e02300fd 0xbcc1ffc07e02300f

def z1213 : W := mkw 0x02124bff60048083 0xc02124bff6004808 0x020003ffe00080c8 0xe020003ffe00080c

def z1214 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xfc681c1ff3e343ff 0xffc681c1ff3e343f

def z1215 : W := mkw 0x01e5b0000f9a000c 0x301e5b0000f9a000 0x51f7fc000f1c0002 0x151f7fc000f1c000

def z1216 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xbaffffff80000000 0x6baffffff8000000

def z1217 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x79fffc001fdc0007 0x079fffc001fdc000

def z1218 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7be003f81fc0ff07 0x47be003f81fc0ff0

def z1219 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfffffdf81fff7f07 0xdfffffdf81fff7f0

def z1220 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xd87ffe7fe0000000 0xbd87ffe7fe000000

def z1221 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc001ffff00f 0x1f9fffc001ffff00

def z1222 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffc601fff0c07 0x9fdfffc601fff0c0

def z1223 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xa8281c1ff0e343f9 0x7a8281c1ff0e343f

def z1224 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x80281c1fe0e303f0 0x180281c1fe0e303f

def z1225 : W := mkw 0x410db400957b4044 0x1410db400957b404 0xa81ffc07903f40c9 0x7a81ffc07903f40c

def z1226 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x803ffc0000ff0000 0x1803ffc0000ff000

def z1227 : W := mkw 0x00f692860000000f 0x000f692860000000 0xf8fffc0780000000 0x1f8fffc078000000

def z1228 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x62efffffe0000000 0xf62efffffe000000

def z1229 : W := mkw 0x0004980920000004 0x4000498092000000 0x801ffc07e0000000 0x1801ffc07e000000

def z1230 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0x24281c1ff0e343fd 0xe24281c1ff0e343f

def z1231 : W := mkw 0x810db4001ffb2a04 0x3810db4001ffb2a0 0x851ffc001fffff0f 0x1851ffc001fffff0

def z1232 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x21bffc001cdc0000 0x021bffc001cdc000

def z1233 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xfdd0e2647f3f8cff 0xbfdd0e2647f3f8cf

def z1234 : W := mkw 0x01edb5501ffb000c 0x301edb5501ffb000 0xf9fffc781fff0007 0x9f9fffc781fff000

def z1235 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xcc281c1fe0e303fd 0xbcc281c1fe0e303f

def z1236 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x12dfffe380000000 0x012dfffe38000000

def z1237 : W := mkw 0x42124bffe004d0c3 0xc42124bffe004d0c 0x020003ffe00000c0 0xe020003ffe00000c

def z1238 : W := mkw 0x00ed91501430000c 0x100ed91501430000 0xfbfffff81c3cf00b 0xffbfffff81c3cf00

def z1239 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xe4281c1ff0e343f4 0xde4281c1ff0e343f

def z1240 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x139703879c3cf0cb 0x6139703879c3cf0c

def z1241 : W := mkw 0x01e5b0000f9a000c 0x301e5b0000f9a000 0x31fffc000f1c0002 0x031fffc000f1c000

def z1242 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc001fff400f 0x7f9fffc001fff400

def z1243 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xdfd0e3e46f3fbcff 0xbdfd0e3e46f3fbcf

def z1244 : W := mkw 0x01e5b4000fdb000c 0x301e5b4000fdb000 0xd9f7fc000fff0007 0x1d9f7fc000fff000

def z1245 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0x4440e264633f8cff 0xb4440e264633f8cf

def z1246 : W := mkw 0x02f6daaf6000000f 0xc02f6daaf6000000 0xf8fffc1fe0000000 0xff8fffc1fe000000

def z1247 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xa81ffc07e0000000 0x7a81ffc07e000000

def z1248 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x805ffc00033f0000 0x1805ffc00033f000

def z1249 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xec281c1ff3e3cfff 0xfec281c1ff3e3cff

def z1250 : W := mkw 0x41edb4009ffb404c 0x341edb4009ffb404 0xf9fffc001fff40cf 0x1f9fffc001fff40c

def z1251 : W := mkw 0x81e5b5500fdb2a0c 0x381e5b5500fdb2a0 0x7ff7fff81fdfff0f 0xf7ff7fff81fdfff0

def z1252 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xdc50e26473ffcfff 0xbdc50e26473ffcff

def z1253 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfafffffff0c00005 0xffafffffff0c0000

def z1254 : W := mkw 0x62124bffe004d4e3 0xc62124bffe004d4e 0x060003ffe000fcf8 0xe060003ffe000fcf

def z1255 : W := mkw 0x0013028604149083 0x1001302860414908 0xbb9f03878c3cb0cb 0x6bb9f03878c3cb0c

def z1256 : W := mkw 0x50000c09a0414150 0x450000c09a041415 0x6c201c1ff0c343fd 0xf6c201c1ff0c343f

def z1257 : W := mkw 0x82f6dbff60002a0f 0xc82f6dbff60002a0 0xfeffffffe0000f00 0xffeffffffe0000f0

def z1258 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbb9f03879c3cb0c3 0x0bb9f03879c3cb0c

def z1259 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xfc50e264733fccff 0xffc50e264733fccf

def z1260 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xc81ffc07e0000000 0xbc81ffc07e000000

def z1261 : W := mkw 0x00f4da2d6000000e 0xc00f4da2d6000000 0xf8fffe7fe0000000 0xff8fffe7fe000000

def z1262 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0x801ffc1fe0000000 0xf801ffc1fe000000

def z1263 : W := mkw 0x01edb5501ffb000c 0x301edb5501ffb000 0xfbffffe01fff0007 0x1fbffffe01fff000

def z1264 : W := mkw 0x010db400157b0004 0x1010db400157b000 0x801ffc0010ff0005 0x1801ffc0010ff000

def z1265 : W := mkw 0x80e499592a802a0c 0x680e499592a802a0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z1266 : W := mkw 0x22f6dbff600484af 0xc22f6dbff600484a 0xfeffffffe0238cfd 0xffeffffffe0238cf

def z1267 : W := mkw 0x42f24bffe004d0cb 0xc42f24bffe004d0c 0x7be003fffc00f0cb 0xe7be003fffc00f0c

def z1268 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x91dffc001fff0007 0x191dffc001fff000

def z1269 : W := mkw 0x400b008294305041 0x1400b00829430504 0xbb9f03839c3cf00b 0x6bb9f03839c3cf00

def z1270 : W := mkw 0x0000000000000000 0x0000000000000000 0x7fe003f81fc0ff0f 0xe7fe003f81fc0ff0

def z1271 : W := mkw 0x0105b000051a0004 0x10105b000051a000 0x801ffc00001c0000 0x1801ffc00001c000

def z1272 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xfbbf039f9c3cf0cb 0xefbbf039f9c3cf0c

def z1273 : W := mkw 0x4009000094304040 0x1400900009430404 0xbb9f03879c3cf0cb 0x6bb9f03879c3cf0c

def z1274 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xfea81f9ff0e343fd 0xffea81f9ff0e343f

def z1275 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xffffffffef00bc0f 0xfffffffffef00bc0

def z1276 : W := mkw 0x410924009ffb5040 0x3410924009ffb504 0x010000001fff7007 0x0010000001fff700

def z1277 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xfeffffffe0004308 0xffeffffffe000430

def z1278 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xf9fffc601fff0c07 0x1f9fffc601fff0c0

def z1279 : W := mkw 0x00e590000410000c 0x100e590000410000 0xf9fffc000c1c0002 0x1f9fffc000c1c000

def z1280 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xfc78fe64633f8cff 0xbfc78fe64633f8cf

def z1281 : W := mkw 0x01edb5501ffb000c 0x301edb5501ffb000 0xfffffff81fff8c0f 0xffffffff81fff8c0

def z1282 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x805ffc67e0000000 0x1805ffc67e000000

def z1283 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xfc78fc1ff0e343fd 0xffc78fc1ff0e343f

def z1284 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xa4281c1ff0e343f8 0xfa4281c1ff0e343f

def z1285 : W := mkw 0x410db400957b4044 0x1410db400957b404 0x801ffc07803f00c0 0x1801ffc07803f00c

def z1286 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x51f7fc001fff0007 0x151f7fc001fff000

def z1287 : W := mkw 0xa2e4f9796b8a2e2c 0xea2e4f9796b8a2e2 0x4460fc7863c30f34 0x94460fc7863c30f3

def z1288 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xff9f03879c3cf0cf 0xeff9f03879c3cf0c

def z1289 : W := mkw 0x51edb4009ffb415c 0x351edb4009ffb415 0xfdfffc047fff43ff 0xbfdfffc047fff43f

def z1290 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xffffffe01fffbc0f 0xbffffffe01fffbc0

def z1291 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0xfbffffe01ffffc0f 0x7fbffffe01ffffc0

def z1292 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbb9f03839c3cf003 0x4bb9f03839c3cf00

def z1293 : W := mkw 0x401b42a6d434d0c3 0x9401b42a6d434d0c 0xffdfe3e7ff3cfccf 0xfffdfe3e7ff3cfcc

def z1294 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xb9fffc001ffc0003 0x0b9fffc001ffc000

def z1295 : W := mkw 0x601b42a6d434d4e3 0x9601b42a6d434d4e 0xbb9f03e79c3cfccb 0x6bb9f03e79c3cfcc

def z1296 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbf9f0387fc3cf0fb 0xebf9f0387fc3cf0f

def z1297 : W := mkw 0x02e6d9fb6000000d 0xc02e6d9fb6000000 0x22effdfb80000000 0x422effdfb8000000

def z1298 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0x33fffff81fdcff02 0x433fffff81fdcff0

def z1299 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffc001fff430f 0x1fdfffc001fff430

def z1300 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xf9fffc047fff00f7 0x1f9fffc047fff00f

def z1301 : W := mkw 0x81e5b1500f9a2a0c 0x381e5b1500f9a2a0 0xfbfffff80f1cbc02 0xffbfffff80f1cbc0

def z1302 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbf9f03879f3cfccf 0x6bf9f03879f3cfcc

def z1303 : W := mkw 0x401302868414d0c3 0x1401302868414d0c 0x9b9703878c3cf0cb 0x69b9703878c3cf0c

def z1304 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfdfffc001fff00ff 0x1fdfffc001fff00f

def z1305 : W := mkw 0x82f6dbff60002a0f 0xc82f6dbff60002a0 0xfffffffffc00ff0b 0xffffffffffc00ff0

def z1306 : W := mkw 0x501b06869475d1d3 0x1501b06869475d1d 0xffbf039f9cfff3ff 0xeffbf039f9cfff3f

def z1307 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xc450e264633f8cfc 0xbc450e264633f8cf

def z1308 : W := mkw 0x0216dbff60000007 0xc0216dbff6000000 0xda5fffffe0000000 0xfda5fffffe000000

def z1309 : W := mkw 0x00e4b000010a000c 0x000e4b000010a000 0xf8fffc00003f0000 0x1f8fffc00003f000

def z1310 : W := mkw 0x81edb5501ffb2a0c 0x381edb5501ffb2a0 0x7ffffff81fdcff0f 0xe7ffffff81fdcff0

def z1311 : W := mkw 0x82f6dbff6a802a0f 0xe82f6dbff6a802a0 0xffffffffef00ff0a 0xfffffffffef00ff0

def z1312 : W := mkw 0x00092400157b0000 0x100092400157b000 0xf9fffc001fff0007 0x1f9fffc001fff000

def z1313 : W := mkw 0x20106224410e84a2 0x820106224410e84a 0xcc50e064633f0cfd 0xbcc50e064633f0cf

def z1314 : W := mkw 0x50000c09a0414150 0x450000c09a041415 0xec281c1fe0c343fc 0xfec281c1fe0c343f

def z1315 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0x31fffc001fff0007 0x031fffc001fff000

def z1316 : W := mkw 0x01edb4001ffb000c 0x301edb4001ffb000 0xfbfffd801fff7007 0x5fbfffd801fff700

def z1317 : W := mkw 0x50090c09b4714150 0x550090c09b471415 0xed281c1ffcff43ff 0xfed281c1ffcff43f

def z1318 : W := mkw 0x401302868414d0c3 0x1401302868414d0c 0xbb9f03878c1cf0ca 0x6bb9f03878c1cf0c

def z1319 : W := mkw 0xa2f6dbff6004aeaf 0xca2f6dbff6004aea 0xfeffffffe000fff8 0xffeffffffe000fff

def z1320 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x7fe003f87fc3ff3f 0xf7fe003f87fc3ff3

def z1321 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xb2ffffffe0000000 0x5b2ffffffe000000

def z1322 : W := mkw 0x02e6988b2000000d 0x402e6988b2000000 0xf8fffc0380000000 0x1f8fffc038000000

def z1323 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0xbabfff9fe0000000 0x7babfff9fe000000

def z1324 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0xfff003f81ffcff0f 0xefff003f81ffcff0

def z1325 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xbf9f039f9c3cf3cb 0xebf9f039f9c3cf3c

def z1326 : W := mkw 0x201262a6410e84a3 0x8201262a6410e84a 0xde50e3e7e33f8cff 0xfde50e3e7e33f8cf

def z1327 : W := mkw 0x010db400157b0004 0x1010db400157b000 0xbb9fff801c3ff00b 0x7bb9fff801c3ff00

def z1328 : W := mkw 0x0216daaf60000007 0xc0216daaf6000000 0xd85ffc07e0000000 0x1d85ffc07e000000

def z1329 : W := mkw 0x410924009fffd0c0 0x3410924009fffd0c 0x010000001fff00c7 0x0010000001fff00c

def z1330 : W := mkw 0x80e001500a802a08 0x280e001500a802a0 0x37e003f81fc0ff0a 0xe37e003f81fc0ff0

def z1331 : W := mkw 0x401b42a6d434d0c3 0x9401b42a6d434d0c 0xbbdfe3e79c3cf0cb 0x6bbdfe3e79c3cf0c

def z1332 : W := mkw 0x50080c09b0614150 0x450080c09b061415 0xefa81d9ffce373fd 0xfefa81d9ffce373f

def z1333 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0xfbbf03879cfcf0cf 0x6fbbf03879cfcf0c

def z1334 : W := mkw 0x401b02869434d0c3 0x1401b02869434d0c 0x339f03839c3cf0cb 0x4339f03839c3cf0c

def z1335 : W := mkw 0x02f6dbff6000000f 0xc02f6dbff6000000 0x22bffd9b80000000 0x422bffd9b8000000

def z1336 : W := mkw 0x0206988b20000005 0x40206988b2000000 0x801ffc0380000000 0x1801ffc038000000

def z1337 : W := mkw 0x82e699db2a802a0d 0x682e699db2a802a0 0xfbfffd9b9fc07307 0x5fbfffd9b9fc0730

def z1338 : W := mkw 0x02e4d9796000000c 0xc02e4d9796000000 0xf8fffc7fe0000000 0xff8fffc7fe000000

def z1339 : W := mkw 0x400b008294305041 0x1400b00829430504 0x238f01839c3c7003 0x4238f01839c3c700

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z8,z6]),(1,[z9,z3,z4,z5,z6,z10]),(0,[z0,z3,z4,z5,z6,z10,z11])],[(0,[z0,z2,z3,z4,z5,z12,z6]),(0,[z0,z2,z3,z4,z5,z13,z6]),(0,[z2,z3,z14,z4,z15,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z16]),(0,[z9,z2,z3,z17,z4,z5,z6]),(0,[z0,z2,z18,z3,z4,z5,z6]),(0,[z0,z2,z3,z19,z4,z5,z6]),(0,[z20,z2,z3,z21,z4,z5,z6])],[(0,[z22,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z23,z6]),(0,[z24,z0,z2,z25,z4,z5,z6]),(0,[z0,z2,z3,z4,z26,z5,z6]),(0,[z27,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z28,z4,z5,z6]),(0,[z29,z0,z2,z3,z4,z30,z6]),(0,[z0,z31,z2,z3,z4,z5,z6])],[(1,[z32,z33,z3,z4,z5,z6]),(0,[z34,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z4,z5,z6]),(0,[z0,z2,z3,z4,z36,z5,z6])],[(0,[z37,z0,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z38,z4,z5,z6]),(0,[z39,z0,z40,z3,z4,z5,z6]),(0,[z2,z3,z41,z4,z5,z6,z42]),(0,[z0,z7,z3,z4,z5,z43,z6]),(0,[z0,z2,z3,z4,z5,z44,z6]),(0,[z0,z2,z45,z3,z4,z5,z6])],[(0,[z46,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z47,z3,z4,z48,z6]),(1,[z0,z40,z3,z4,z5,z6]),(0,[z0,z2,z49,z3,z4,z5,z6]),(0,[z50,z0,z2,z3,z4,z5,z6]),(0,[z51,z0,z2,z3,z4,z52,z6]),(0,[z0,z2,z3,z4,z53,z5,z6]),(0,[z0,z2,z3,z4,z54,z5,z6]),(0,[z55,z0,z2,z3,z4,z5,z6])],[(0,[z56,z0,z2,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z5,z57,z6]),(1,[z0,z58,z3,z4,z52,z6]),(0,[z0,z2,z3,z4,z5,z6,z59]),(0,[z60,z0,z2,z3,z61,z5,z6]),(0,[z62,z0,z2,z3,z4,z5,z6])],[(0,[z63,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z64,z5,z6]),(0,[z2,z3,z65,z4,z5,z6,z42]),(0,[z66,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z67,z6])]],
   [[(0,[z9,z2,z3,z4,z68,z5,z6]),(0,[z0,z2,z3,z69,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z70]),(0,[z71,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z72,z5,z6])],[(0,[z0,z2,z3,z73,z4,z5,z6]),(0,[z0,z2,z3,z4,z74,z5,z6]),(0,[z39,z0,z2,z3,z4,z5,z6]),(0,[z60,z9,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z75]),(0,[z0,z2,z3,z5,z76,z77,z6]),(0,[z78,z0,z2,z3,z5,z6,z11]),(0,[z0,z2,z3,z4,z5,z6,z79]),(0,[z0,z2,z3,z4,z80,z5,z81]),(0,[z0,z2,z3,z82,z4,z5,z6])],[(0,[z83,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z42,z84]),(0,[z27,z0,z2,z3,z85,z5,z6]),(0,[z0,z58,z2,z3,z4,z57,z6]),(0,[z86,z0,z2,z3,z4,z5,z6]),(0,[z87,z0,z7,z3,z4,z5,z6])],[(0,[z0,z2,z88,z3,z4,z5,z6]),(0,[z89,z0,z3,z4,z5,z8,z6]),(0,[z0,z90,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z91,z10]),(0,[z0,z2,z3,z4,z5,z92,z6]),(0,[z0,z2,z93,z3,z4,z5,z6]),(0,[z0,z2,z94,z4,z95,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z96,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z97])],[(0,[z98,z0,z2,z3,z4,z5,z6]),(0,[z58,z2,z3,z4,z5,z6,z42]),(0,[z99,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z100,z6])],[(0,[z101,z0,z2,z3,z4,z5,z6]),(1,[z27,z0,z3,z102,z5,z6]),(1,[z103,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z104,z6]),(0,[z0,z105,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z106,z6]),(0,[z9,z2,z3,z21,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z107])]],
   [[(0,[z0,z7,z3,z4,z102,z5,z6]),(0,[z0,z2,z3,z108,z4,z5,z6])],[(0,[z109,z9,z2,z3,z4,z5,z6]),(0,[z110,z0,z7,z3,z4,z5,z6]),(0,[z0,z111,z2,z3,z4,z5,z6]),(0,[z109,z0,z2,z47,z3,z4,z6]),(0,[z112,z0,z2,z3,z4,z5,z6])],[(0,[z113,z2,z3,z4,z5,z8,z6]),(0,[z113,z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z114]),(0,[z115,z0,z2,z3,z4,z5,z6]),(0,[z0,z116,z2,z3,z4,z5,z6]),(0,[z86,z2,z3,z4,z52,z5,z6])],[(0,[z0,z2,z117,z3,z4,z5,z6]),(0,[z37,z0,z2,z3,z41,z5,z6]),(0,[z0,z7,z3,z4,z15,z5,z6]),(0,[z0,z2,z47,z3,z4,z8,z6]),(0,[z2,z3,z4,z5,z6,z42,z118]),(0,[z0,z119,z2,z3,z4,z5,z6])],[(0,[z37,z120,z2,z3,z4,z5,z6]),(0,[z121,z2,z3,z4,z5,z6,z42]),(0,[z122,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z21,z4,z5,z6,z10])],[(0,[z121,z0,z2,z3,z5,z77,z6]),(0,[z0,z123,z2,z3,z4,z5,z6]),(1,[z124,z2,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z125,z6]),(1,[z112,z2,z3,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z6,z118])],[(0,[z0,z2,z3,z126,z4,z5,z6]),(0,[z127,z0,z3,z4,z5,z6,z10]),(0,[z128,z96,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z129,z6]),(0,[z78,z130,z2,z3,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z5,z118]),(0,[z0,z2,z3,z4,z5,z6,z131])],[(0,[z109,z0,z2,z3,z14,z5,z6]),(0,[z132,z0,z2,z3,z4,z5,z6]),(0,[z133,z0,z2,z3,z4,z5,z6]),(1,[z134,z2,z3,z4,z5,z6])]],
   [[(1,[z0,z2,z3,z4,z5,z135]),(0,[z37,z0,z2,z3,z15,z5,z6]),(0,[z136,z2,z3,z4,z5,z6,z42]),(1,[z9,z7,z3,z4,z5,z6]),(0,[z0,z2,z3,z137,z4,z5,z6]),(0,[z0,z7,z3,z41,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z6,z11]),(0,[z0,z2,z138,z3,z4,z5,z139])],[(0,[z0,z2,z3,z140,z4,z5,z6])],[(0,[z0,z2,z141,z3,z4,z5,z6]),(0,[z142,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z15,z5,z6,z42]),(0,[z143,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z144,z4,z5,z6])],[(0,[z145,z0,z2,z3,z4,z5,z6]),(0,[z146,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z147,z4,z5,z6]),(1,[z0,z2,z3,z4,z148,z6]),(0,[z0,z2,z3,z4,z5,z149,z6]),(0,[z0,z2,z3,z4,z5,z150,z6]),(0,[z0,z2,z3,z4,z5,z6,z151]),(0,[z0,z152,z2,z3,z5,z76,z6]),(0,[z0,z2,z3,z153,z4,z5,z6]),(0,[z0,z154,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z155,z5,z6]),(0,[z156,z0,z2,z3,z4,z5,z6])],[(0,[z9,z121,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z8,z6,z42]),(0,[z0,z157,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z17,z4,z5,z6]),(0,[z0,z2,z158,z3,z4,z5,z6]),(0,[z0,z159,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z77,z6,z10]),(1,[z96,z2,z3,z4,z5,z6]),(0,[z160,z0,z2,z3,z4,z5,z6])],[(0,[z161,z0,z2,z3,z4,z5,z6]),(0,[z162,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z163,z3,z4,z5,z6]),(0,[z164,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z165]),(0,[z0,z2,z3,z4,z5,z6,z166])],[(0,[z27,z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z167]),(0,[z0,z2,z3,z4,z5,z168,z6]),(0,[z0,z2,z3,z5,z77,z6,z11])],[(0,[z145,z0,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z169,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z170])]],
   [[(1,[z113,z2,z171,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z172,z42]),(0,[z0,z2,z3,z4,z5,z6,z173]),(0,[z0,z7,z174,z3,z4,z5,z6]),(0,[z103,z0,z2,z3,z4,z5,z6])],[(0,[z78,z9,z2,z3,z4,z5,z6]),(1,[z51,z0,z3,z4,z57,z6]),(0,[z0,z2,z3,z4,z5,z57,z6]),(0,[z175,z0,z2,z3,z4,z5,z6]),(1,[z176,z0,z2,z5,z77,z6]),(0,[z0,z2,z3,z4,z5,z6,z177])],[(0,[z0,z2,z3,z4,z5,z178,z6]),(0,[z179,z0,z2,z3,z4,z5,z6]),(0,[z56,z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z155,z5,z6]),(0,[z2,z3,z21,z4,z180,z5,z6]),(0,[z0,z181,z2,z3,z4,z5,z6]),(0,[z0,z2,z182,z3,z4,z5,z6]),(0,[z0,z2,z183,z3,z4,z5,z6]),(0,[z60,z0,z2,z3,z184,z5,z6])],[(0,[z0,z185,z2,z3,z4,z5,z6]),(0,[z0,z7,z3,z186,z4,z5,z6]),(0,[z136,z0,z2,z3,z4,z5,z6]),(0,[z87,z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z68,z5,z6]),(0,[z0,z2,z3,z4,z187,z5,z6]),(0,[z0,z2,z188,z3,z4,z5,z6]),(0,[z0,z2,z138,z4,z5,z77,z6]),(0,[z29,z0,z2,z3,z4,z5,z6])],[(0,[z143,z189,z2,z3,z4,z5,z6]),(0,[z9,z2,z190,z3,z4,z5,z6])],[(0,[z39,z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z191,z4,z5,z77,z6]),(0,[z0,z58,z3,z4,z5,z6,z10]),(0,[z0,z7,z3,z4,z95,z5,z6]),(0,[z192,z0,z2,z3,z4,z5,z6]),(0,[z193,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z194,z5,z6]),(0,[z0,z2,z3,z52,z5,z195,z6]),(1,[z0,z2,z196,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z197,z6]),(0,[z9,z2,z3,z4,z5,z6,z10]),(0,[z0,z2,z198,z191,z4,z5,z6])]],
   [[(0,[z199,z0,z2,z3,z4,z5,z6]),(0,[z32,z2,z3,z14,z4,z5,z6]),(0,[z0,z2,z3,z4,z200,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z201]),(0,[z0,z202,z2,z3,z4,z5,z6])],[(0,[z0,z203,z2,z191,z4,z5,z6]),(0,[z204,z0,z2,z3,z4,z5,z6]),(1,[z29,z0,z2,z4,z5,z205])],[(0,[z110,z9,z2,z3,z4,z5,z6]),(0,[z206,z0,z2,z3,z4,z5,z6]),(0,[z207,z0,z3,z4,z5,z6,z10]),(0,[z0,z7,z3,z4,z5,z208,z6]),(1,[z0,z7,z3,z4,z5,z209]),(0,[z0,z2,z3,z4,z5,z6,z210]),(0,[z0,z2,z3,z21,z4,z5,z6]),(0,[z0,z2,z3,z4,z80,z76,z6]),(0,[z0,z211,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z212]),(0,[z0,z2,z3,z4,z213,z5,z6]),(0,[z9,z2,z3,z4,z5,z76,z6]),(0,[z9,z0,z2,z3,z4,z5,z43])],[(0,[z51,z32,z0,z3,z4,z5,z6]),(0,[z0,z2,z214,z3,z4,z5,z6]),(0,[z215,z0,z2,z3,z4,z5,z6]),(0,[z216,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z217,z5,z6]),(0,[z0,z2,z3,z4,z218,z5,z6]),(0,[z0,z2,z3,z4,z5,z219,z6]),(0,[z0,z2,z3,z4,z5,z220,z6]),(0,[z0,z2,z221,z3,z4,z5,z6])],[(0,[z0,z3,z4,z48,z5,z6,z10]),(0,[z0,z2,z3,z4,z5,z222,z6]),(0,[z0,z2,z3,z4,z5,z6,z223]),(0,[z0,z2,z3,z4,z224,z5,z6])],[(0,[z0,z2,z3,z225,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z226]),(0,[z0,z3,z4,z5,z76,z6,z10]),(0,[z0,z116,z7,z3,z4,z5,z6]),(1,[z128,z0,z2,z4,z227,z6])],[(0,[z228,z0,z2,z3,z4,z5,z6]),(0,[z145,z120,z2,z3,z4,z5,z6]),(0,[z0,z2,z229,z3,z4,z5,z6]),(0,[z0,z7,z3,z28,z4,z5,z6]),(0,[z0,z2,z3,z4,z230,z5,z6]),(0,[z231,z0,z2,z3,z4,z5,z6]),(0,[z109,z0,z2,z3,z21,z5,z6])]],
   [[(0,[z232,z0,z2,z3,z4,z5,z6]),(0,[z122,z0,z7,z3,z4,z5,z6]),(0,[z233,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z234,z6]),(0,[z29,z134,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z235])],[(0,[z0,z2,z3,z236,z4,z5,z6])],[(0,[z237,z0,z2,z3,z4,z5,z6]),(0,[z121,z0,z2,z3,z41,z5,z6]),(0,[z9,z2,z3,z4,z5,z139,z6]),(0,[z0,z2,z3,z65,z4,z5,z208])],[(0,[z238,z0,z2,z3,z4,z5,z6]),(0,[z239,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z227,z6,z10]),(0,[z0,z3,z4,z5,z6,z10,z167]),(1,[z0,z240,z3,z4,z5,z6]),(0,[z0,z2,z47,z3,z5,z76,z6]),(0,[z60,z0,z2,z196,z4,z5,z6])],[(1,[z241,z2,z186,z4,z5,z6]),(0,[z2,z25,z3,z4,z5,z6,z42]),(0,[z242,z0,z2,z3,z4,z5,z6]),(0,[z29,z0,z2,z3,z155,z5,z6])],[(0,[z37,z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z243,z6]),(0,[z24,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z244,z3,z4,z5,z6])],[(0,[z51,z145,z0,z3,z4,z5,z6]),(0,[z143,z2,z3,z4,z5,z8,z6]),(0,[z143,z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z245,z3,z4,z5,z6]),(0,[z246,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z247,z5,z6]),(0,[z248,z0,z2,z3,z4,z5,z6])],[(0,[z145,z0,z7,z3,z4,z5,z6]),(0,[z121,z0,z2,z3,z15,z5,z6]),(0,[z27,z9,z2,z3,z4,z5,z6]),(0,[z0,z198,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z5,z6,z249])]],
   [[(0,[z250,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z251,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z172]),(0,[z0,z252,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z5,z195,z6]),(0,[z253,z0,z2,z3,z4,z5,z6]),(0,[z29,z0,z2,z3,z4,z5,z139]),(0,[z254,z2,z3,z4,z5,z139,z6])],[(0,[z255,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z256,z4,z5,z6]),(0,[z0,z3,z191,z4,z102,z5,z6]),(0,[z0,z2,z3,z4,z95,z6,z118])],[(1,[z0,z2,z3,z5,z257,z6]),(0,[z0,z2,z258,z3,z4,z5,z6]),(0,[z259,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z260,z3,z4,z5,z6])],[(0,[z37,z0,z2,z3,z14,z5,z6]),(0,[z0,z2,z3,z261,z4,z5,z6]),(0,[z56,z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z262,z5,z6]),(1,[z263,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z264,z5,z6]),(0,[z265,z0,z2,z3,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z5,z81])],[(1,[z0,z2,z3,z4,z251,z6]),(0,[z0,z266,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z218,z5,z6]),(0,[z2,z3,z4,z5,z208,z6,z165]),(1,[z0,z2,z3,z61,z5,z6])],[(0,[z0,z2,z3,z4,z5,z135,z6]),(0,[z189,z113,z2,z3,z4,z5,z6]),(0,[z267,z0,z2,z3,z4,z5,z6]),(0,[z189,z2,z3,z4,z5,z6,z42]),(0,[z9,z2,z3,z4,z5,z268,z6]),(0,[z0,z2,z269,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z270,z6])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z0,z2,z94,z3,z4,z227,z6])],[(0,[z0,z2,z271,z3,z4,z5,z6]),(0,[z83,z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z190,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z195,z6]),(0,[z29,z0,z7,z3,z4,z5,z6])]],
   [[(0,[z37,z32,z2,z3,z4,z5,z6]),(0,[z0,z272,z2,z3,z4,z5,z6]),(0,[z2,z94,z3,z4,z5,z6,z42])],[(0,[z0,z2,z3,z4,z5,z257,z6]),(1,[z24,z0,z191,z4,z5,z6]),(0,[z0,z2,z273,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z274,z6]),(0,[z0,z2,z3,z275,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z42,z276]),(0,[z2,z3,z4,z5,z6,z42,z11]),(0,[z51,z0,z2,z3,z4,z57,z6]),(0,[z0,z2,z3,z4,z5,z6,z10]),(0,[z130,z0,z2,z3,z4,z5,z6])],[(0,[z0,z277,z2,z3,z4,z5,z6]),(0,[z37,z0,z2,z3,z4,z5,z6]),(0,[z121,z2,z3,z14,z4,z5,z6])],[(0,[z0,z2,z3,z4,z278,z5,z6]),(0,[z9,z2,z25,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z80,z5,z6]),(0,[z0,z2,z3,z4,z5,z279,z6]),(0,[z0,z2,z3,z280,z4,z5,z6]),(0,[z0,z3,z4,z102,z5,z6,z10]),(0,[z0,z2,z3,z4,z281,z5,z6]),(0,[z0,z2,z4,z95,z5,z227,z6])],[(0,[z0,z33,z3,z4,z5,z6,z10]),(0,[z0,z2,z282,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z208,z6,z42]),(0,[z2,z3,z4,z218,z102,z5,z6]),(0,[z283,z0,z3,z4,z5,z6,z10]),(0,[z0,z3,z4,z5,z6,z173,z10]),(0,[z0,z2,z3,z4,z5,z6,z284]),(0,[z0,z2,z3,z65,z5,z76,z6]),(1,[z0,z2,z3,z4,z285,z6])],[(0,[z0,z2,z3,z286,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z287,z6]),(0,[z0,z2,z3,z4,z5,z288,z6]),(1,[z0,z2,z3,z289,z5,z6]),(0,[z290,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z76,z6])],[(0,[z32,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z42,z10]),(0,[z0,z2,z3,z4,z5,z209,z43]),(0,[z291,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z292,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z249])]],
   [[(0,[z0,z2,z3,z4,z48,z76,z6]),(0,[z0,z2,z3,z4,z293,z5,z6]),(0,[z0,z3,z41,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z5,z6,z294]),(1,[z0,z2,z295,z4,z5,z6])],[(0,[z296,z0,z2,z3,z4,z5,z6]),(0,[z297,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z52,z5,z6,z42]),(0,[z9,z58,z2,z3,z4,z5,z6]),(0,[z298,z0,z2,z3,z4,z5,z6]),(0,[z78,z0,z31,z3,z4,z5,z6])],[(0,[z0,z299,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z300,z15,z5,z6]),(0,[z0,z3,z4,z5,z139,z6,z10]),(0,[z0,z2,z3,z4,z5,z6,z301])],[(0,[z32,z0,z3,z4,z5,z6,z10]),(0,[z2,z3,z4,z5,z57,z6,z42]),(0,[z27,z109,z0,z2,z3,z5,z6]),(0,[z0,z3,z65,z4,z5,z6,z10]),(0,[z78,z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z302,z3,z4,z5,z6])],[(0,[z189,z0,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z5,z81,z205]),(0,[z0,z2,z3,z4,z5,z6,z303])],[(0,[z0,z2,z3,z4,z5,z304,z6]),(0,[z0,z2,z305,z3,z4,z5,z6]),(0,[z0,z2,z3,z306,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z307]),(1,[z0,z308,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z309,z6]),(0,[z0,z2,z3,z4,z5,z139,z6])],[(0,[z310,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z311,z4,z5,z6]),(0,[z9,z113,z2,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z312,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z57,z6]),(0,[z0,z3,z4,z5,z6,z10,z313]),(0,[z0,z2,z3,z4,z5,z6,z314])],[(0,[z27,z32,z0,z3,z4,z5,z6]),(0,[z0,z2,z315,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z316,z6]),(0,[z0,z2,z171,z3,z317,z5,z6]),(0,[z143,z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z318,z4,z5,z6]),(0,[z0,z319,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z320])]],
   [[(0,[z32,z2,z33,z3,z4,z5,z6]),(0,[z145,z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z321,z6]),(0,[z0,z2,z3,z4,z5,z322,z6]),(0,[z24,z0,z2,z3,z217,z5,z6]),(0,[z0,z2,z3,z4,z5,z323,z6]),(0,[z242,z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z198,z138,z4,z5,z6])],[(0,[z324,z0,z2,z3,z4,z5,z6]),(0,[z189,z2,z3,z4,z48,z5,z6]),(0,[z24,z0,z7,z3,z4,z5,z6]),(0,[z2,z3,z325,z191,z4,z5,z6]),(0,[z0,z2,z3,z326,z4,z5,z6]),(0,[z0,z2,z3,z4,z327,z5,z6]),(0,[z0,z3,z4,z328,z5,z6,z10]),(0,[z0,z2,z3,z4,z5,z329,z6])],[(0,[z0,z2,z3,z4,z330,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z331]),(0,[z2,z3,z4,z48,z5,z8,z6]),(0,[z0,z2,z3,z4,z5,z332,z6]),(0,[z0,z2,z3,z333,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z334])],[(0,[z335,z0,z2,z3,z4,z5,z6]),(0,[z9,z2,z171,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z336,z6]),(0,[z37,z0,z2,z3,z4,z148,z6]),(0,[z0,z2,z3,z337,z4,z5,z6]),(0,[z2,z3,z191,z4,z5,z6,z42]),(0,[z0,z2,z338,z3,z4,z5,z6])],[(0,[z0,z2,z3,z14,z4,z5,z6]),(0,[z2,z138,z3,z4,z5,z6,z42]),(0,[z127,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z339]),(0,[z340,z0,z2,z3,z4,z5,z6]),(0,[z60,z0,z2,z295,z4,z5,z6])],[(0,[z241,z0,z2,z171,z4,z5,z6]),(0,[z0,z2,z3,z341,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z342]),(0,[z0,z2,z3,z4,z80,z81,z6])],[(0,[z0,z2,z343,z3,z4,z5,z6]),(1,[z3,z4,z5,z6,z42,z10]),(0,[z9,z2,z3,z4,z5,z81,z6]),(0,[z0,z2,z344,z3,z4,z5,z6]),(0,[z345,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z10,z10]),(0,[z0,z7,z3,z21,z4,z5,z6]),(0,[z0,z2,z3,z346,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z347,z6]),(0,[z0,z3,z4,z5,z139,z6,z320]),(0,[z112,z2,z3,z4,z5,z208,z6])]],
   [[(0,[z348,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z349]),(0,[z0,z2,z3,z4,z5,z350,z6]),(0,[z29,z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z268,z6]),(0,[z0,z2,z3,z4,z5,z351,z6]),(0,[z0,z2,z3,z4,z5,z352,z6]),(1,[z0,z2,z3,z184,z5,z6]),(0,[z353,z0,z2,z3,z4,z5,z6])],[(0,[z145,z0,z3,z4,z52,z5,z6]),(0,[z9,z2,z94,z3,z4,z5,z6]),(0,[z0,z2,z3,z354,z4,z5,z6]),(0,[z0,z3,z286,z4,z5,z6,z10]),(0,[z355,z0,z2,z3,z4,z5,z6]),(0,[z29,z0,z2,z4,z5,z6,z205]),(1,[z78,z0,z2,z3,z5,z11])],[(0,[z145,z0,z33,z3,z4,z5,z6]),(1,[z145,z120,z3,z4,z5,z6]),(1,[z356,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z30,z6]),(0,[z357,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z358,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z359,z6]),(0,[z360,z0,z2,z3,z4,z5,z6])],[(0,[z145,z0,z203,z3,z4,z5,z6]),(0,[z189,z120,z2,z3,z4,z5,z6]),(1,[z143,z2,z3,z4,z8,z6])],[(0,[z9,z0,z3,z4,z5,z6,z10]),(0,[z355,z0,z3,z4,z5,z6,z10]),(0,[z78,z0,z2,z3,z4,z5,z11])],[(0,[z0,z3,z4,z15,z5,z6,z10]),(1,[z189,z2,z3,z4,z48,z6]),(0,[z9,z2,z361,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z362,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z363]),(0,[z0,z2,z3,z4,z5,z364,z6]),(0,[z0,z240,z2,z3,z4,z5,z6])],[(0,[z0,z365,z2,z3,z4,z5,z6]),(1,[z0,z3,z366,z4,z5,z6]),(0,[z37,z0,z7,z3,z4,z5,z6]),(0,[z367,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z80,z5,z6,z42]),(0,[z9,z2,z3,z4,z5,z6,z6]),(0,[z0,z2,z25,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z368]),(0,[z0,z2,z3,z369,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z370]),(0,[z0,z2,z3,z4,z184,z5,z6]),(0,[z0,z2,z3,z4,z80,z5,z6])]],
   [[(0,[z0,z3,z4,z5,z8,z6,z10]),(0,[z0,z2,z3,z4,z371,z5,z6])],[(0,[z241,z113,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z241,z2,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z372,z4,z5,z6])],[(0,[z9,z2,z33,z3,z4,z5,z6]),(0,[z145,z0,z3,z191,z4,z5,z6]),(0,[z120,z2,z3,z4,z5,z6,z42]),(0,[z2,z171,z3,z4,z5,z6,z42]),(0,[z121,z0,z2,z3,z4,z5,z6]),(0,[z373,z0,z2,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z48,z5,z6]),(0,[z0,z2,z374,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z375,z6]),(0,[z0,z376,z2,z3,z4,z5,z6])],[(0,[z32,z0,z7,z3,z4,z5,z6]),(0,[z377,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z41,z5,z76,z6])],[(0,[z143,z0,z2,z3,z4,z48,z6]),(0,[z176,z2,z3,z4,z5,z6,z42]),(0,[z27,z0,z3,z4,z102,z5,z6]),(0,[z0,z58,z2,z3,z4,z5,z6]),(0,[z378,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z379,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z380]),(0,[z0,z2,z381,z3,z4,z5,z6]),(0,[z176,z0,z2,z3,z5,z77,z6])],[(0,[z121,z0,z3,z4,z5,z6,z10]),(0,[z382,z0,z2,z3,z4,z5,z6]),(0,[z0,z383,z3,z4,z5,z208,z6])],[(0,[z0,z203,z3,z4,z102,z5,z6])]],
   [[(0,[z120,z2,z171,z3,z4,z5,z6]),(0,[z0,z2,z3,z384,z4,z5,z6]),(0,[z0,z2,z385,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z386])],[(0,[z0,z2,z3,z387,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z42]),(0,[z207,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z76,z6,z118])],[(0,[z0,z2,z3,z4,z388,z5,z6]),(0,[z0,z2,z3,z4,z5,z42,z10]),(0,[z24,z9,z2,z3,z4,z5,z6]),(0,[z78,z0,z2,z3,z4,z285,z6])],[(0,[z113,z2,z171,z3,z4,z5,z6]),(0,[z0,z319,z7,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z389,z5,z6]),(0,[z145,z0,z3,z85,z4,z5,z6]),(0,[z121,z189,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z95,z5,z6,z42]),(0,[z0,z3,z4,z52,z5,z57,z6]),(0,[z0,z308,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z80,z227,z6]),(1,[z0,z2,z138,z4,z5,z139]),(0,[z0,z2,z3,z4,z5,z6,z390]),(0,[z0,z391,z2,z3,z4,z5,z6])],[(0,[z392,z0,z2,z3,z4,z5,z6]),(0,[z9,z120,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z151,z42]),(0,[z9,z2,z3,z4,z5,z227,z6]),(0,[z0,z2,z3,z393,z4,z5,z6]),(0,[z0,z2,z394,z3,z4,z5,z6])],[(0,[z395,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z396,z6]),(0,[z0,z2,z3,z4,z227,z6,z118])],[(0,[z0,z2,z171,z3,z4,z5,z6]),(0,[z0,z397,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z398]),(0,[z0,z3,z85,z4,z102,z5,z6]),(0,[z0,z7,z3,z4,z5,z6,z10]),(1,[z2,z3,z4,z5,z6,z368]),(0,[z0,z2,z94,z3,z4,z95,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z399,z6]),(0,[z0,z2,z3,z4,z400,z5,z6]),(0,[z0,z3,z4,z5,z43,z6,z75]),(0,[z2,z3,z4,z52,z5,z401,z6]),(0,[z0,z2,z3,z402,z4,z5,z6]),(0,[z29,z0,z2,z138,z4,z5,z6]),(0,[z0,z403,z2,z3,z4,z5,z6]),(0,[z0,z2,z47,z3,z4,z80,z6]),(1,[z2,z3,z4,z5,z6,z165]),(0,[z0,z2,z404,z3,z4,z5,z6])],[(0,[z405,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z186,z4,z5,z6,z42]),(0,[z0,z2,z3,z4,z5,z6,z406]),(0,[z128,z0,z2,z3,z4,z5,z210]),(0,[z0,z2,z3,z4,z5,z407,z6])],[(0,[z37,z2,z3,z4,z15,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z408]),(0,[z143,z0,z2,z3,z4,z8,z6]),(0,[z267,z9,z2,z3,z4,z5,z6]),(1,[z376,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z81,z6])],[(0,[z0,z2,z409,z3,z4,z5,z6]),(0,[z128,z2,z3,z4,z5,z6,z42]),(0,[z410,z0,z2,z3,z4,z5,z6]),(0,[z176,z0,z3,z4,z5,z6,z10]),(0,[z0,z7,z3,z4,z5,z76,z6]),(0,[z0,z2,z198,z3,z5,z77,z6]),(0,[z128,z0,z2,z3,z4,z5,z220]),(0,[z0,z2,z3,z5,z76,z6,z11])],[(0,[z0,z2,z94,z3,z4,z5,z6])],[(0,[z411,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z412,z5,z6]),(0,[z128,z0,z2,z3,z346,z5,z6]),(0,[z0,z2,z3,z4,z5,z413,z6]),(0,[z0,z2,z3,z4,z5,z6,z414])],[(0,[z120,z2,z33,z3,z4,z5,z6]),(0,[z415,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z416,z6]),(0,[z24,z0,z203,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z417,z5,z6]),(0,[z0,z2,z3,z4,z5,z418,z6])],[(0,[z0,z2,z3,z4,z419,z5,z6]),(0,[z420,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z421,z6]),(0,[z0,z3,z191,z4,z5,z57,z6]),(1,[z0,z422,z3,z4,z5,z6])]],
   [[(1,[z0,z2,z3,z4,z5,z212]),(0,[z0,z2,z3,z4,z5,z423,z6]),(0,[z0,z25,z3,z4,z5,z6,z10]),(0,[z0,z424,z2,z3,z4,z5,z6]),(0,[z0,z425,z2,z3,z4,z5,z6])],[(0,[z426,z0,z2,z3,z4,z5,z6]),(0,[z427,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z428,z5,z6]),(1,[z2,z3,z4,z5,z6,z42]),(0,[z0,z2,z361,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z220]),(1,[z0,z2,z3,z4,z379,z6])],[(0,[z0,z429,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z27,z0,z2,z3,z5,z76,z6]),(0,[z430,z0,z2,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z139,z6]),(0,[z0,z2,z3,z4,z5,z431,z6]),(0,[z432,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z433,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z434,z3,z4,z5,z6]),(0,[z435,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z436,z6]),(1,[z0,z2,z3,z346,z5,z6]),(0,[z0,z2,z3,z4,z5,z437,z6])],[(0,[z32,z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z40,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z81,z6,z42]),(0,[z9,z2,z3,z4,z5,z6,z205]),(0,[z24,z0,z3,z191,z4,z5,z6]),(0,[z0,z2,z25,z198,z4,z5,z6]),(0,[z0,z2,z3,z4,z438,z5,z6]),(0,[z0,z2,z4,z5,z77,z6,z205]),(0,[z0,z2,z3,z4,z5,z6,z439]),(1,[z391,z2,z3,z4,z5,z6])],[(0,[z0,z2,z33,z3,z4,z5,z6]),(0,[z0,z171,z3,z366,z4,z5,z6]),(0,[z9,z2,z3,z14,z4,z5,z6]),(0,[z0,z2,z3,z4,z48,z5,z6]),(0,[z0,z440,z2,z3,z4,z5,z6]),(0,[z109,z0,z152,z2,z3,z5,z6]),(0,[z0,z2,z441,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z328,z5,z6]),(0,[z0,z2,z3,z4,z5,z442,z6]),(0,[z109,z0,z2,z47,z3,z5,z6])],[(0,[z0,z2,z3,z443,z4,z5,z6]),(0,[z121,z2,z3,z4,z5,z8,z6]),(0,[z121,z0,z7,z3,z4,z5,z6]),(0,[z444,z2,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z4,z5,z445,z6]),(0,[z446,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z447,z6]),(0,[z9,z448,z2,z3,z4,z5,z6]),(0,[z51,z0,z3,z4,z5,z57,z6]),(0,[z0,z2,z449,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z450,z6]),(1,[z0,z451,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z452]),(0,[z241,z120,z2,z3,z4,z5,z6]),(0,[z37,z121,z2,z3,z4,z5,z6]),(1,[z373,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z76,z8,z6]),(0,[z0,z2,z3,z4,z5,z6,z75]),(0,[z0,z2,z3,z65,z5,z77,z6]),(0,[z0,z2,z3,z4,z5,z6,z453])],[(0,[z0,z2,z3,z4,z5,z6,z454]),(0,[z0,z2,z3,z4,z5,z77,z6]),(0,[z455,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z456,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z457,z6]),(0,[z0,z2,z458,z3,z4,z5,z6])],[(0,[z0,z2,z459,z3,z4,z5,z6]),(1,[z121,z2,z3,z14,z5,z6]),(1,[z0,z2,z3,z460,z5,z6]),(0,[z128,z0,z3,z4,z5,z6,z10]),(0,[z176,z0,z2,z3,z41,z5,z6]),(0,[z461,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z462,z5,z6]),(0,[z463,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z464,z3,z4,z5,z6])],[(0,[z283,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z15,z5,z8,z6]),(0,[z2,z3,z14,z4,z5,z6,z42]),(1,[z0,z2,z3,z169,z5,z6]),(0,[z0,z2,z3,z325,z4,z5,z6]),(0,[z0,z7,z58,z3,z4,z5,z6]),(0,[z0,z94,z3,z4,z5,z6,z10]),(1,[z20,z2,z3,z4,z5,z6]),(1,[z109,z0,z2,z47,z3,z6])],[(0,[z32,z0,z3,z4,z52,z5,z6]),(0,[z465,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z300,z5,z6]),(0,[z0,z2,z466,z3,z4,z5,z6]),(0,[z0,z2,z3,z191,z4,z5,z6]),(0,[z0,z2,z3,z85,z5,z77,z6]),(0,[z0,z2,z3,z467,z4,z5,z6]),(0,[z468,z0,z2,z3,z4,z5,z6])],[(0,[z32,z0,z33,z3,z4,z5,z6]),(0,[z60,z2,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z4,z469,z5,z6]),(0,[z0,z2,z3,z4,z5,z470,z6]),(0,[z0,z2,z3,z471,z4,z5,z6]),(0,[z472,z0,z2,z3,z4,z5,z6])],[(0,[z241,z0,z2,z186,z4,z5,z6]),(0,[z0,z473,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z81,z139])]],
   [[(0,[z0,z120,z2,z3,z4,z5,z6]),(0,[z32,z0,z203,z3,z4,z5,z6]),(0,[z474,z0,z2,z3,z4,z5,z6]),(0,[z475,z0,z2,z3,z4,z5,z6]),(0,[z9,z152,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z476,z6]),(0,[z0,z2,z3,z4,z5,z227,z6])],[(0,[z0,z2,z3,z4,z460,z5,z6]),(0,[z477,z0,z2,z3,z4,z5,z6]),(1,[z86,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z208,z6,z10]),(0,[z109,z0,z2,z3,z65,z5,z6]),(0,[z0,z2,z3,z478,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z80,z6])],[(0,[z2,z3,z85,z4,z5,z6,z42]),(0,[z0,z58,z2,z3,z4,z52,z6]),(0,[z0,z2,z3,z479,z4,z5,z6])],[(0,[z113,z0,z2,z186,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z480]),(0,[z481,z0,z2,z3,z4,z5,z6]),(0,[z189,z0,z2,z3,z4,z5,z6]),(0,[z9,z0,z2,z3,z4,z5,z42]),(1,[z9,z2,z3,z4,z5,z43]),(0,[z0,z2,z3,z4,z5,z482,z6]),(0,[z128,z0,z2,z3,z4,z227,z6]),(0,[z483,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z484,z6])],[(0,[z485,z0,z2,z3,z4,z5,z6]),(0,[z0,z120,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z5,z6,z486]),(0,[z0,z7,z25,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z80,z5,z6]),(0,[z176,z0,z2,z198,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z487,z6]),(0,[z0,z3,z4,z52,z5,z6,z10]),(0,[z0,z2,z488,z3,z4,z5,z6]),(0,[z0,z2,z198,z41,z4,z5,z6])],[(0,[z32,z0,z3,z191,z4,z5,z6]),(0,[z109,z2,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z4,z5,z489,z6]),(0,[z128,z0,z93,z3,z4,z5,z6]),(0,[z0,z422,z2,z3,z4,z5,z6]),(0,[z20,z0,z2,z3,z4,z5,z6])],[(0,[z0,z203,z2,z25,z4,z5,z6]),(0,[z0,z2,z3,z85,z4,z5,z6]),(0,[z0,z3,z4,z5,z57,z6,z10]),(0,[z410,z0,z7,z3,z4,z5,z6]),(0,[z109,z0,z2,z3,z5,z77,z6]),(0,[z29,z0,z240,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z139,z118]),(0,[z0,z490,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z491,z6]),(0,[z0,z2,z3,z4,z5,z6,z492]),(0,[z493,z2,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z4,z5,z401,z6])],[(0,[z32,z145,z2,z3,z4,z5,z6]),(0,[z120,z2,z3,z14,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z494]),(0,[z51,z2,z3,z4,z5,z6,z42]),(0,[z495,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z139,z6,z249])],[(0,[z496,z0,z2,z3,z4,z5,z6]),(0,[z497,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z498,z3,z4,z5,z6]),(0,[z0,z2,z3,z61,z4,z5,z6])],[(0,[z9,z7,z2,z3,z4,z5,z6]),(0,[z0,z7,z152,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z499]),(0,[z0,z2,z3,z4,z5,z500,z6])],[(0,[z32,z189,z2,z3,z4,z5,z6]),(0,[z501,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z502,z3,z4,z5,z6]),(1,[z0,z93,z3,z4,z5,z6]),(0,[z78,z0,z2,z3,z4,z5,z208])],[(0,[z0,z2,z503,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z10,z452]),(0,[z60,z0,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z504,z5,z6])],[(0,[z0,z2,z505,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z6,z42]),(0,[z176,z0,z381,z3,z4,z5,z6]),(0,[z506,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z507,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z205]),(1,[z0,z2,z236,z4,z5,z6])]],
   [[(0,[z32,z0,z2,z3,z4,z5,z135]),(0,[z32,z0,z3,z85,z4,z5,z6]),(0,[z39,z0,z2,z3,z4,z5,z43]),(0,[z2,z3,z4,z5,z6,z6,z42]),(0,[z0,z3,z191,z4,z5,z6,z10]),(0,[z508,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z509,z5,z6]),(0,[z0,z2,z3,z4,z5,z510,z6]),(0,[z0,z2,z3,z41,z65,z5,z6])],[(0,[z0,z2,z3,z4,z5,z511,z6]),(0,[z0,z138,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z512,z5,z6])],[(0,[z0,z448,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z513,z6]),(0,[z2,z3,z4,z5,z6,z42,z16]),(0,[z0,z2,z3,z4,z5,z514,z6])],[(0,[z27,z145,z0,z3,z4,z5,z6]),(0,[z0,z7,z171,z3,z4,z5,z6]),(0,[z9,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z515]),(0,[z24,z0,z2,z191,z4,z5,z6]),(0,[z51,z0,z2,z3,z4,z5,z6])],[(0,[z113,z0,z2,z171,z4,z5,z6]),(0,[z121,z0,z2,z3,z14,z5,z6]),(0,[z9,z2,z3,z4,z5,z209,z6]),(0,[z0,z2,z3,z4,z5,z516,z6]),(0,[z0,z2,z3,z4,z5,z517,z6]),(0,[z0,z2,z3,z289,z4,z5,z6]),(0,[z0,z422,z3,z4,z5,z139,z6]),(0,[z0,z2,z3,z4,z5,z6,z518]),(0,[z0,z2,z3,z4,z5,z6,z519]),(1,[z2,z3,z4,z5,z6,z301])],[(0,[z520,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z521,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z522,z6]),(0,[z0,z2,z3,z4,z5,z523,z6])],[(0,[z0,z2,z171,z3,z5,z257,z6]),(0,[z0,z2,z524,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z43,z10]),(0,[z0,z2,z3,z525,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z81,z6]),(0,[z526,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z131])]],
   [[(0,[z87,z2,z3,z4,z5,z6,z42]),(0,[z9,z2,z47,z3,z4,z5,z6]),(0,[z51,z0,z3,z4,z5,z6,z10]),(1,[z2,z3,z4,z5,z401,z6]),(0,[z263,z0,z2,z3,z52,z5,z6]),(0,[z2,z3,z4,z5,z81,z6,z301])],[(0,[z9,z2,z3,z4,z5,z6,z118]),(0,[z0,z3,z4,z5,z6,z10,z486]),(0,[z0,z7,z94,z3,z4,z5,z6]),(0,[z128,z0,z154,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z205,z118]),(0,[z0,z2,z3,z4,z5,z6,z527]),(0,[z0,z2,z3,z4,z5,z6,z528]),(0,[z0,z2,z3,z4,z80,z5,z118])],[(0,[z2,z47,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z529,z4,z5,z6]),(0,[z0,z2,z3,z85,z41,z5,z6]),(0,[z0,z58,z3,z4,z52,z5,z6]),(0,[z530,z0,z2,z3,z4,z5,z6]),(0,[z531,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z532,z6]),(0,[z29,z0,z2,z3,z289,z5,z6]),(0,[z254,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z47,z3,z21,z4,z6]),(0,[z0,z2,z3,z21,z5,z76,z6]),(0,[z0,z2,z3,z4,z5,z533,z6])],[(0,[z0,z2,z3,z4,z5,z534,z6]),(0,[z0,z152,z2,z3,z4,z5,z6]),(0,[z124,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z80,z5,z6,z10]),(0,[z0,z7,z3,z4,z417,z5,z6]),(0,[z0,z2,z3,z535,z4,z5,z6])],[(0,[z0,z120,z7,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z52,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z536]),(0,[z78,z0,z451,z3,z4,z5,z6])],[(0,[z537,z0,z2,z3,z4,z5,z6]),(0,[z9,z2,z198,z3,z4,z5,z6]),(0,[z9,z2,z138,z3,z4,z5,z6]),(0,[z0,z203,z3,z4,z5,z57,z6]),(0,[z0,z538,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z539,z4,z5,z6])],[(0,[z32,z2,z3,z4,z5,z8,z6]),(0,[z0,z2,z540,z3,z4,z5,z6]),(0,[z0,z171,z3,z4,z5,z6,z10]),(1,[z37,z2,z3,z15,z5,z6]),(0,[z9,z189,z2,z3,z4,z5,z6]),(1,[z7,z3,z4,z5,z6,z42]),(0,[z27,z0,z2,z541,z4,z5,z6]),(0,[z128,z446,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z30,z6]),(0,[z542,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z166])],[(0,[z0,z2,z3,z4,z5,z543,z6]),(0,[z145,z0,z120,z3,z4,z5,z6]),(1,[z0,z2,z3,z317,z5,z6]),(0,[z189,z0,z7,z3,z4,z5,z6]),(0,[z110,z2,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z4,z5,z209,z42]),(0,[z0,z152,z3,z4,z5,z6,z10]),(0,[z0,z7,z3,z4,z5,z6,z6]),(1,[z0,z154,z3,z4,z5,z6]),(0,[z109,z0,z2,z3,z4,z76,z6]),(0,[z0,z3,z4,z5,z208,z6,z166])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z276]),(0,[z113,z2,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z4,z544,z5,z6])],[(0,[z545,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z546,z4,z5,z6,z42]),(0,[z9,z2,z3,z4,z5,z77,z6]),(0,[z2,z3,z4,z5,z209,z6,z368]),(0,[z0,z2,z3,z4,z5,z547,z6])],[(0,[z0,z7,z33,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z48,z5,z6]),(1,[z0,z2,z280,z4,z5,z6]),(0,[z0,z2,z94,z4,z5,z6,z205]),(0,[z0,z2,z4,z5,z139,z6,z205]),(0,[z548,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z549,z6]),(0,[z2,z3,z4,z5,z43,z6,z42]),(0,[z0,z58,z3,z191,z4,z5,z6]),(0,[z0,z152,z2,z3,z85,z5,z6]),(0,[z550,z0,z2,z3,z4,z5,z6]),(1,[z0,z7,z3,z4,z5,z10]),(1,[z0,z381,z3,z4,z5,z6]),(0,[z0,z2,z3,z551,z4,z5,z6])],[(0,[z0,z7,z203,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z10,z205]),(1,[z446,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z552,z6])],[(0,[z0,z2,z553,z3,z4,z5,z6]),(0,[z9,z2,z3,z191,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z554])],[(1,[z0,z2,z541,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z6]),(1,[z130,z2,z3,z4,z5,z6])],[(0,[z241,z0,z2,z3,z4,z5,z6]),(0,[z87,z0,z3,z4,z5,z6,z10]),(0,[z0,z2,z555,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z556,z6]),(0,[z557,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z197,z6]),(0,[z0,z3,z4,z95,z5,z6,z10])],[(0,[z558,z0,z2,z3,z4,z5,z6]),(0,[z134,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z559,z3,z4,z5,z6]),(0,[z0,z2,z295,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z560,z6]),(0,[z9,z2,z3,z65,z4,z5,z6]),(0,[z561,z0,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z209]),(0,[z176,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z562,z5,z6])],[(0,[z113,z0,z2,z3,z4,z5,z6]),(0,[z241,z0,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z5,z6,z84]),(0,[z2,z3,z4,z5,z209,z6,z42]),(0,[z0,z563,z3,z4,z5,z81,z6])],[(0,[z0,z2,z564,z3,z4,z5,z6]),(0,[z565,z0,z2,z3,z4,z5,z6]),(0,[z27,z2,z3,z4,z5,z6,z42]),(2,[z3,z4,z5,z42,z10]),(0,[z0,z2,z3,z4,z566,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z567]),(0,[z0,z2,z3,z4,z5,z568,z6]),(1,[z0,z2,z198,z41,z5,z6]),(0,[z0,z2,z569,z3,z4,z5,z6]),(0,[z570,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z571,z4,z5,z6]),(0,[z0,z3,z186,z4,z5,z6,z10]),(0,[z39,z0,z2,z3,z4,z5,z42]),(0,[z0,z2,z3,z412,z4,z5,z6]),(0,[z51,z0,z58,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z227,z6]),(1,[z0,z221,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z572,z6]),(0,[z573,z0,z2,z3,z4,z5,z6]),(0,[z110,z424,z2,z3,z4,z5,z6]),(0,[z110,z0,z3,z4,z5,z6,z10])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z113,z0,z3,z4,z5,z6,z10]),(0,[z203,z2,z3,z4,z5,z6,z42]),(1,[z2,z3,z4,z5,z209,z42]),(0,[z2,z574,z3,z4,z5,z6,z42]),(0,[z9,z2,z3,z85,z4,z5,z6]),(0,[z0,z7,z3,z479,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z575]),(0,[z576,z0,z2,z3,z4,z5,z6]),(0,[z37,z0,z2,z3,z4,z251,z6]),(0,[z9,z2,z3,z4,z5,z8,z6]),(0,[z9,z0,z7,z3,z4,z5,z6]),(0,[z0,z152,z2,z3,z102,z5,z6]),(0,[z0,z2,z3,z4,z5,z209,z6]),(0,[z0,z577,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z578]),(0,[z89,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z579,z5,z6]),(0,[z283,z9,z2,z3,z4,z5,z6]),(0,[z580,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z581,z5,z6]),(0,[z0,z2,z3,z65,z5,z208,z6])],[(0,[z189,z2,z3,z4,z15,z5,z6]),(0,[z0,z7,z488,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z210])],[(0,[z39,z2,z3,z4,z5,z6,z42]),(0,[z526,z0,z7,z3,z4,z5,z6]),(0,[z0,z582,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z180,z5,z6]),(0,[z0,z2,z47,z3,z4,z5,z6]),(0,[z78,z0,z2,z507,z4,z5,z6])],[(0,[z583,z0,z2,z3,z4,z5,z6]),(1,[z89,z0,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z5,z43,z6]),(0,[z128,z0,z2,z3,z4,z95,z6]),(0,[z0,z2,z3,z4,z5,z6,z118])],[(0,[z2,z3,z4,z102,z5,z6,z42]),(1,[z2,z3,z4,z5,z42,z10]),(0,[z0,z2,z3,z41,z102,z5,z6]),(0,[z110,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z584,z6])],[(0,[z2,z33,z3,z4,z5,z6,z42])],[(0,[z99,z2,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z585,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z586,z6]),(0,[z0,z2,z3,z4,z52,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z587,z5,z6]),(0,[z588,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z589,z5,z6]),(0,[z2,z3,z4,z5,z6,z42,z42]),(0,[z481,z9,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z81,z6,z10]),(0,[z0,z2,z198,z3,z4,z5,z6]),(0,[z0,z2,z138,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z590,z6]),(0,[z0,z2,z3,z196,z4,z5,z6])],[(0,[z591,z0,z2,z3,z4,z5,z6]),(0,[z0,z538,z7,z3,z4,z5,z6]),(0,[z128,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z94,z138,z4,z5,z6])],[(0,[z0,z203,z2,z3,z4,z5,z6]),(0,[z0,z2,z25,z4,z5,z77,z6]),(0,[z0,z2,z592,z3,z4,z5,z6]),(0,[z593,z0,z2,z3,z4,z5,z6]),(0,[z60,z0,z221,z3,z4,z5,z6]),(0,[z0,z563,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z139,z6,z42]),(0,[z27,z0,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z5,z594,z6])],[(0,[z0,z2,z3,z4,z5,z6,z595]),(0,[z0,z7,z3,z4,z5,z6,z205]),(0,[z596,z0,z2,z3,z4,z5,z6]),(0,[z597,z0,z2,z3,z4,z5,z6]),(1,[z0,z563,z3,z4,z5,z6])],[(0,[z0,z7,z3,z14,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z598]),(0,[z0,z2,z3,z41,z5,z6,z11]),(0,[z599,z0,z2,z3,z4,z5,z6])],[(0,[z600,z0,z2,z3,z4,z5,z6]),(0,[z0,z601,z2,z3,z4,z5,z6]),(0,[z0,z203,z3,z4,z5,z6,z10]),(0,[z0,z7,z3,z4,z512,z5,z6]),(0,[z0,z2,z3,z4,z602,z5,z6]),(1,[z248,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z603,z2,z3,z4,z5,z6]),(0,[z373,z0,z3,z4,z15,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z91]),(0,[z0,z2,z604,z3,z4,z5,z6]),(0,[z60,z605,z2,z3,z4,z5,z6])]],
   [[(0,[z606,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z14,z4,z5,z6,z10]),(1,[z39,z2,z3,z4,z5,z42]),(0,[z9,z2,z3,z4,z102,z5,z6]),(0,[z0,z2,z3,z4,z607,z5,z6]),(0,[z0,z2,z3,z608,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z609]),(1,[z0,z2,z3,z4,z610,z6]),(0,[z0,z2,z3,z4,z5,z611,z6])],[(0,[z0,z612,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z613]),(0,[z614,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z615,z4,z5,z6]),(1,[z0,z383,z3,z4,z5,z6])],[(0,[z189,z2,z3,z186,z4,z5,z6]),(0,[z39,z0,z3,z4,z5,z6,z10]),(0,[z0,z2,z616,z3,z4,z5,z6]),(0,[z0,z7,z7,z3,z4,z5,z6]),(0,[z617,z0,z2,z3,z4,z5,z6])],[(0,[z241,z0,z7,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z15,z5,z6]),(1,[z424,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z10]),(1,[z2,z3,z4,z180,z5,z6])],[(0,[z120,z2,z3,z4,z5,z8,z6]),(0,[z143,z2,z3,z4,z5,z6,z42]),(0,[z444,z0,z2,z3,z4,z5,z6])],[(0,[z145,z2,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z14,z5,z76,z6]),(0,[z0,z2,z618,z3,z4,z5,z6]),(0,[z619,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z65,z4,z5,z6])],[(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z356,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z85,z4,z5,z6,z10]),(0,[z0,z2,z3,z620,z4,z5,z6]),(0,[z176,z0,z7,z3,z4,z5,z6]),(0,[z29,z376,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z208,z6,z11]),(0,[z0,z2,z3,z4,z5,z6,z621])],[(0,[z0,z2,z3,z317,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z148,z6]),(0,[z0,z2,z3,z622,z4,z5,z6]),(0,[z2,z3,z4,z64,z5,z6,z42]),(0,[z124,z2,z3,z4,z102,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z623,z5,z6]),(0,[z2,z3,z21,z4,z5,z6,z42]),(0,[z9,z2,z3,z41,z4,z5,z6]),(0,[z9,z2,z3,z4,z5,z6,z11])],[(0,[z0,z2,z3,z4,z5,z624,z6]),(0,[z9,z9,z2,z3,z4,z5,z6]),(0,[z51,z9,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z10,z118])],[(0,[z0,z2,z625,z3,z4,z5,z6]),(0,[z39,z0,z397,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z626,z42]),(0,[z176,z0,z2,z4,z5,z77,z6])],[(0,[z32,z0,z120,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z8,z6]),(0,[z0,z2,z627,z3,z4,z5,z6]),(1,[z0,z397,z3,z4,z5,z6]),(0,[z520,z9,z2,z3,z4,z5,z6]),(0,[z0,z440,z3,z4,z5,z43,z6]),(0,[z0,z2,z198,z3,z41,z5,z6]),(0,[z0,z2,z3,z628,z4,z5,z6]),(0,[z0,z629,z2,z3,z4,z5,z6])],[(0,[z630,z0,z2,z3,z4,z5,z6]),(0,[z27,z0,z2,z3,z102,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z631]),(1,[z0,z302,z3,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z546,z4,z5,z6]),(0,[z143,z0,z2,z3,z460,z5,z6]),(0,[z189,z0,z2,z3,z4,z48,z6]),(0,[z0,z2,z3,z4,z632,z5,z6]),(0,[z29,z2,z3,z4,z5,z6,z42]),(1,[z0,z203,z25,z4,z5,z6]),(0,[z0,z2,z41,z4,z5,z77,z6]),(0,[z29,z0,z2,z3,z4,z379,z6]),(0,[z633,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z366,z4,z5,z6]),(0,[z0,z2,z4,z5,z227,z6,z205]),(1,[z60,z0,z2,z3,z4,z118])],[(0,[z143,z0,z2,z3,z169,z5,z6]),(0,[z0,z2,z3,z4,z5,z43,z6]),(0,[z2,z3,z4,z5,z6,z42,z452]),(1,[z0,z440,z3,z4,z5,z6]),(1,[z2,z3,z325,z4,z5,z6]),(0,[z0,z2,z634,z3,z4,z5,z6]),(0,[z635,z0,z2,z3,z4,z5,z6]),(0,[z0,z636,z2,z3,z4,z5,z6]),(0,[z637,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z81,z6,z131])]],
   [[(0,[z0,z2,z574,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z77,z6,z42]),(1,[z0,z3,z4,z5,z6,z320]),(0,[z0,z2,z3,z4,z5,z6,z638])],[],[(0,[z0,z2,z3,z4,z5,z639,z6]),(0,[z605,z0,z2,z3,z4,z5,z6])],[(0,[z2,z3,z186,z4,z5,z8,z6]),(0,[z9,z2,z3,z186,z4,z5,z6]),(0,[z143,z0,z3,z4,z5,z6,z10]),(0,[z0,z203,z58,z3,z4,z5,z6]),(0,[z640,z0,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z42,z10]),(0,[z641,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z102,z5,z77,z6]),(0,[z0,z3,z4,z5,z6,z6,z10]),(0,[z109,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z642,z4,z5,z6]),(0,[z78,z0,z2,z3,z65,z5,z6])],[(0,[z0,z2,z3,z643,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z644,z6]),(0,[z9,z2,z3,z4,z95,z5,z6]),(0,[z645,z0,z2,z3,z4,z5,z6]),(0,[z128,z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z138,z3,z4,z5,z205]),(0,[z646,z0,z2,z3,z4,z5,z6])],[(0,[z493,z0,z2,z3,z4,z5,z6]),(0,[z545,z9,z2,z3,z4,z5,z6]),(0,[z647,z0,z2,z3,z4,z5,z6]),(0,[z103,z2,z3,z4,z5,z209,z6])],[(0,[z603,z2,z3,z4,z5,z6,z42]),(0,[z356,z2,z3,z191,z4,z5,z6])]],
   [[(0,[z9,z2,z3,z4,z648,z5,z6]),(0,[z0,z649,z2,z3,z4,z5,z6]),(0,[z109,z0,z3,z4,z5,z6,z10])],[(0,[z650,z0,z2,z3,z4,z5,z6]),(0,[z651,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z652,z42]),(0,[z78,z2,z3,z4,z5,z6,z42]),(1,[z0,z31,z3,z4,z5,z6]),(0,[z0,z2,z653,z3,z4,z5,z6])],[(0,[z9,z2,z3,z4,z5,z208,z6]),(1,[z0,z2,z3,z217,z5,z6]),(0,[z175,z0,z3,z4,z5,z6,z10])],[(0,[z189,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z6,z652]),(0,[z24,z0,z2,z3,z412,z5,z6]),(0,[z0,z203,z25,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z102,z5,z6]),(0,[z110,z239,z2,z3,z4,z5,z6]),(1,[z0,z7,z3,z4,z5,z6]),(0,[z0,z603,z7,z3,z4,z5,z6]),(1,[z629,z2,z3,z4,z5,z6])],[(0,[z654,z0,z2,z3,z4,z5,z6]),(0,[z241,z9,z2,z3,z4,z5,z6]),(0,[z655,z0,z2,z3,z4,z5,z6]),(0,[z0,z152,z203,z3,z4,z5,z6]),(0,[z0,z2,z3,z656,z4,z5,z6]),(0,[z29,z0,z3,z4,z5,z6,z10]),(0,[z78,z391,z2,z3,z4,z5,z6])],[(1,[z0,z3,z4,z5,z43,z10]),(0,[z27,z0,z2,z280,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z209,z6]),(0,[z0,z2,z3,z4,z5,z657,z6]),(0,[z0,z658,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z21,z76,z6])],[(0,[z0,z2,z3,z4,z15,z5,z6]),(0,[z0,z3,z4,z5,z197,z8,z6]),(0,[z0,z47,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z5,z6,z659]),(1,[z0,z211,z3,z4,z5,z6])],[(0,[z660,z0,z2,z3,z4,z5,z6]),(0,[z24,z2,z3,z4,z5,z6,z42]),(0,[z176,z9,z2,z3,z4,z5,z6]),(0,[z27,z0,z152,z3,z4,z5,z6]),(0,[z0,z2,z541,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z339,z10]),(0,[z661,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z138,z4,z5,z227,z6])]],
   [[(0,[z0,z7,z47,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z125,z6]),(0,[z128,z0,z2,z4,z5,z227,z6])],[(0,[z2,z3,z4,z48,z5,z6,z42]),(0,[z0,z7,z3,z4,z5,z6,z118]),(0,[z662,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z663,z4,z5,z6]),(0,[z152,z2,z3,z4,z5,z6,z42]),(0,[z2,z3,z4,z5,z76,z6,z42]),(0,[z9,z203,z2,z3,z4,z5,z6]),(0,[z0,z152,z3,z191,z4,z5,z6]),(0,[z0,z383,z2,z3,z4,z5,z6])],[(1,[z9,z2,z3,z4,z5,z42]),(0,[z0,z2,z3,z664,z4,z5,z6]),(0,[z0,z2,z3,z41,z4,z5,z6]),(0,[z665,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z11])],[(0,[z666,z0,z2,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z52,z5,z6]),(0,[z667,z0,z2,z3,z4,z5,z6]),(0,[z78,z0,z2,z3,z4,z5,z6])],[(0,[z0,z7,z198,z3,z4,z5,z6]),(0,[z0,z7,z138,z3,z4,z5,z6]),(0,[z29,z0,z302,z3,z4,z5,z6]),(0,[z78,z0,z2,z3,z4,z610,z6])],[(0,[z87,z0,z2,z3,z4,z5,z6]),(0,[z241,z2,z3,z186,z4,z5,z6]),(0,[z0,z1,z171,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z42,z205])],[(0,[z241,z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z668,z4,z5,z6]),(0,[z2,z171,z3,z186,z4,z5,z6]),(0,[z0,z2,z3,z669,z4,z5,z6]),(0,[z2,z3,z4,z5,z227,z6,z42]),(0,[z0,z3,z4,z5,z43,z6,z10]),(0,[z670,z0,z2,z3,z4,z5,z6]),(0,[z109,z0,z2,z3,z41,z5,z6]),(0,[z0,z2,z138,z4,z5,z139,z6]),(1,[z254,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z671,z4,z5,z6])]],
   [[(0,[z78,z0,z3,z4,z5,z6,z10]),(0,[z60,z0,z7,z3,z4,z5,z6]),(0,[z128,z0,z2,z94,z4,z5,z6]),(0,[z0,z2,z3,z4,z95,z80,z6]),(0,[z0,z2,z3,z4,z610,z5,z6]),(0,[z60,z629,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z672,z5,z6]),(0,[z673,z0,z2,z3,z4,z5,z6]),(0,[z583,z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z674,z6]),(0,[z0,z7,z3,z4,z5,z77,z6]),(0,[z0,z2,z3,z675,z4,z5,z6]),(1,[z0,z2,z94,z4,z95,z6]),(0,[z248,z2,z3,z4,z5,z81,z6])],[(0,[z263,z0,z2,z3,z4,z5,z6])],[(0,[z2,z198,z3,z4,z5,z6,z42]),(1,[z0,z3,z4,z5,z42,z10]),(0,[z0,z2,z174,z3,z4,z5,z6]),(0,[z60,z0,z211,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z676,z6])],[(0,[z0,z2,z3,z4,z677,z5,z6]),(0,[z678,z0,z2,z3,z4,z5,z6]),(0,[z109,z0,z2,z3,z15,z5,z6]),(0,[z0,z2,z3,z679,z4,z5,z6]),(0,[z0,z680,z2,z3,z4,z5,z6]),(0,[z0,z152,z3,z85,z4,z5,z6]),(0,[z681,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z682,z6])],[(0,[z0,z2,z3,z683,z4,z5,z6]),(0,[z37,z2,z3,z4,z5,z6,z42]),(0,[z0,z7,z3,z191,z4,z5,z6]),(0,[z684,z0,z2,z3,z4,z5,z6]),(0,[z110,z0,z2,z3,z4,z5,z6]),(0,[z176,z0,z308,z3,z4,z5,z6]),(0,[z0,z2,z3,z21,z4,z76,z6])],[(0,[z0,z2,z3,z186,z4,z5,z6]),(0,[z0,z2,z3,z685,z4,z5,z6]),(0,[z37,z0,z2,z3,z5,z77,z6]),(0,[z0,z2,z3,z4,z5,z686,z6]),(0,[z128,z9,z2,z3,z4,z5,z6]),(0,[z24,z0,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z687,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z313]),(0,[z0,z2,z3,z4,z5,z688,z6]),(0,[z0,z2,z198,z4,z5,z6,z205]),(0,[z0,z2,z451,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z689,z6]),(0,[z690,z0,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z42]),(1,[z0,z152,z3,z85,z5,z6]),(0,[z0,z3,z4,z5,z209,z6,z10]),(0,[z0,z2,z3,z691,z4,z5,z6])]],
   [[(0,[z32,z0,z2,z3,z4,z5,z212]),(0,[z692,z0,z2,z3,z4,z5,z6]),(1,[z239,z2,z3,z4,z5,z6]),(0,[z109,z0,z7,z3,z4,z5,z6]),(0,[z128,z0,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z4,z95,z5,z6])],[(0,[z32,z2,z3,z4,z5,z6,z42]),(0,[z110,z0,z2,z3,z4,z5,z209]),(1,[z110,z0,z3,z4,z5,z10]),(0,[z109,z0,z2,z3,z5,z6,z11]),(0,[z0,z2,z3,z4,z5,z285,z6])],[(0,[z0,z693,z2,z3,z4,z5,z6]),(0,[z0,z7,z3,z65,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z694]),(0,[z695,z0,z2,z3,z4,z5,z6])],[(0,[z39,z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z648,z5,z6]),(0,[z51,z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z696,z6]),(0,[z0,z2,z3,z65,z4,z5,z11]),(0,[z0,z2,z3,z4,z81,z6,z118])],[(0,[z0,z2,z3,z4,z697,z5,z6]),(0,[z0,z2,z3,z4,z698,z5,z6]),(0,[z0,z2,z3,z4,z300,z5,z6]),(1,[z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z699,z6]),(0,[z0,z2,z47,z3,z4,z6,z118])],[(0,[z0,z2,z3,z700,z4,z5,z6]),(0,[z0,z503,z3,z4,z5,z6,z10]),(0,[z29,z0,z2,z3,z4,z5,z205]),(0,[z0,z2,z3,z4,z5,z208,z6]),(1,[z605,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z15,z5,z76,z6]),(0,[z0,z2,z701,z3,z4,z5,z6]),(0,[z9,z2,z3,z140,z4,z5,z6]),(0,[z0,z25,z3,z191,z4,z5,z6]),(0,[z702,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z363,z10]),(0,[z0,z2,z3,z703,z4,z5,z6]),(1,[z0,z2,z3,z54,z5,z6]),(0,[z0,z2,z3,z704,z4,z5,z6])],[(0,[z32,z2,z171,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z705,z6]),(0,[z0,z2,z3,z4,z5,z6,z626]),(0,[z0,z2,z3,z4,z706,z5,z6]),(0,[z0,z7,z3,z85,z4,z5,z6]),(0,[z78,z0,z2,z236,z4,z5,z6]),(0,[z0,z2,z507,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z7,z3,z4,z5,z560]),(0,[z2,z3,z679,z15,z5,z6]),(0,[z0,z25,z707,z4,z5,z6]),(0,[z708,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z709]),(0,[z710,z2,z3,z4,z5,z6]),(0,[z383,z3,z4,z5,z6,z165])],[(0,[z0,z2,z3,z4,z711,z6])],[(0,[z0,z2,z3,z712,z5,z6]),(0,[z0,z2,z3,z4,z713,z6]),(0,[z29,z0,z302,z4,z5,z205]),(0,[z29,z0,z2,z4,z379,z205])],[(0,[z113,z171,z366,z4,z5,z6]),(0,[z27,z9,z3,z102,z5,z6]),(0,[z0,z3,z4,z5,z6,z714])],[(0,[z0,z715,z3,z4,z5,z6]),(0,[z3,z4,z300,z5,z6,z42]),(0,[z96,z3,z4,z5,z6,z10]),(0,[z0,z2,z4,z5,z30,z205])],[(0,[z128,z0,z2,z4,z227,z210]),(0,[z376,z240,z3,z4,z5,z6])],[(0,[z0,z2,z716,z4,z5,z6]),(0,[z152,z3,z4,z5,z42,z10]),(0,[z9,z2,z280,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z717]),(0,[z60,z0,z2,z3,z184,z118])],[(0,[z9,z381,z3,z4,z5,z6])],[(0,[z0,z718,z3,z4,z5,z6]),(0,[z143,z2,z3,z4,z268,z6]),(0,[z134,z302,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z719])],[(0,[z383,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z217,z5,z6]),(0,[z0,z2,z720,z4,z5,z6]),(0,[z721,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z722]),(0,[z248,z7,z3,z4,z5,z6]),(0,[z0,z2,z3,z289,z30,z6])],[(0,[z0,z7,z3,z4,z5,z6]),(0,[z723,z2,z3,z4,z5,z6]),(0,[z0,z724,z3,z4,z5,z6]),(0,[z446,z2,z3,z54,z5,z6])],[(0,[z0,z725,z3,z4,z5,z6]),(0,[z39,z7,z3,z4,z5,z42]),(0,[z726,z0,z2,z3,z4,z6]),(0,[z727,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z728]),(0,[z0,z729,z3,z4,z5,z6]),(0,[z9,z3,z4,z5,z42,z10]),(0,[z3,z4,z5,z730,z6,z10]),(0,[z0,z2,z3,z21,z76,z6])],[(0,[z0,z2,z3,z731,z5,z6]),(0,[z732,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z733]),(0,[z0,z3,z5,z6,z10,z734]),(0,[z128,z0,z2,z4,z735,z6])],[(0,[z143,z3,z4,z197,z8,z6]),(0,[z736,z3,z4,z5,z6,z42]),(0,[z737,z0,z3,z4,z5,z6]),(0,[z0,z221,z3,z61,z5,z6])],[(0,[z0,z603,z3,z4,z5,z10]),(0,[z3,z4,z95,z5,z42,z10]),(1,[z0,z191,z217,z5,z6]),(0,[z0,z3,z4,z52,z6,z363])]],
   [[(0,[z9,z2,z198,z41,z5,z6]),(0,[z430,z0,z191,z4,z5,z6]),(0,[z2,z738,z3,z4,z5,z6]),(0,[z110,z424,z3,z4,z5,z10])],[(0,[z9,z221,z3,z4,z5,z6]),(0,[z739,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z740,z5,z6])],[(0,[z27,z0,z3,z587,z5,z6]),(0,[z0,z2,z3,z41,z148,z6]),(0,[z0,z741,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z421]),(0,[z176,z0,z381,z5,z77,z6]),(0,[z0,z2,z404,z4,z5,z139])],[(0,[z0,z1,z3,z317,z5,z6])],[(0,[z2,z171,z3,z4,z5,z212]),(0,[z0,z742,z3,z4,z5,z6]),(0,[z113,z2,z361,z4,z5,z6]),(0,[z0,z2,z743,z4,z5,z6]),(0,[z62,z0,z2,z47,z3,z6])],[(0,[z3,z4,z5,z172,z42,z10]),(0,[z3,z4,z5,z6,z42,z744]),(0,[z0,z203,z158,z4,z5,z6])],[(0,[z51,z9,z3,z4,z57,z6]),(0,[z176,z9,z2,z5,z77,z6]),(0,[z24,z0,z191,z412,z5,z6]),(0,[z745,z3,z4,z5,z6,z10])],[(0,[z32,z3,z4,z5,z42,z10]),(0,[z0,z2,z3,z15,z148,z6]),(0,[z2,z3,z4,z5,z674,z42]),(0,[z0,z2,z3,z746,z5,z6]),(0,[z134,z7,z3,z4,z5,z6])],[(0,[z56,z33,z3,z4,z5,z6]),(0,[z27,z0,z280,z102,z5,z6]),(0,[z2,z3,z180,z5,z76,z6]),(0,[z391,z451,z3,z4,z5,z6])],[(0,[z2,z3,z747,z15,z5,z6]),(0,[z2,z3,z21,z180,z76,z6]),(0,[z748,z2,z3,z4,z5,z6])],[(0,[z37,z3,z300,z15,z5,z6]),(0,[z0,z2,z749,z4,z5,z6]),(0,[z0,z2,z3,z5,z750,z6]),(0,[z355,z0,z3,z4,z57,z6]),(0,[z0,z3,z4,z5,z6,z751]),(0,[z0,z2,z138,z4,z30,z6])],[(0,[z0,z7,z3,z4,z148,z6]),(0,[z302,z3,z4,z5,z6,z42])],[],[(0,[z0,z752,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z753])],[(0,[z0,z3,z4,z5,z212,z10]),(0,[z9,z40,z3,z4,z5,z6]),(0,[z29,z9,z2,z4,z5,z205]),(0,[z283,z3,z4,z5,z6,z173])],[(0,[z373,z0,z3,z5,z76,z6]),(0,[z3,z4,z5,z81,z42,z10])]],
   [[(0,[z0,z2,z3,z5,z754,z6]),(0,[z110,z0,z3,z4,z5,z10]),(0,[z0,z2,z3,z61,z5,z6])],[(0,[z145,z3,z4,z5,z42,z10]),(0,[z0,z7,z3,z4,z5,z494]),(0,[z2,z3,z4,z5,z6,z755]),(0,[z635,z0,z2,z3,z5,z11]),(0,[z391,z2,z3,z4,z285,z6])],[(0,[z2,z171,z643,z4,z5,z6]),(0,[z203,z25,z4,z5,z6,z42]),(0,[z9,z3,z4,z5,z6,z75]),(0,[z2,z3,z4,z5,z6,z756]),(0,[z0,z757,z3,z4,z5,z6])],[(0,[z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z758,z6]),(0,[z96,z154,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z274,z42]),(0,[z759,z2,z4,z5,z6,z42]),(0,[z298,z0,z2,z4,z5,z205])],[(0,[z0,z3,z4,z5,z480,z10]),(0,[z3,z4,z5,z42,z363,z10]),(0,[z0,z7,z3,z217,z5,z6])],[],[(0,[z3,z14,z4,z5,z42,z10]),(0,[z60,z0,z3,z4,z10,z118]),(0,[z0,z3,z4,z5,z760,z6]),(1,[z0,z2,z761,z3,z6])],[(0,[z0,z2,z3,z4,z5,z762]),(0,[z56,z488,z3,z4,z5,z6]),(0,[z0,z7,z3,z21,z76,z6]),(0,[z2,z3,z4,z5,z6,z763]),(0,[z0,z764,z3,z4,z5,z6])],[],[(0,[z0,z2,z765,z4,z5,z6]),(0,[z603,z3,z4,z5,z42,z10]),(0,[z0,z2,z3,z4,z766,z6]),(0,[z0,z221,z3,z184,z5,z6])],[(0,[z0,z2,z3,z5,z767,z6]),(0,[z373,z3,z14,z4,z5,z6]),(0,[z3,z4,z5,z42,z42,z10]),(0,[z2,z3,z4,z768,z6,z42])],[(0,[z0,z40,z3,z4,z5,z6]),(0,[z2,z3,z15,z76,z8,z6]),(0,[z39,z3,z4,z5,z42,z10]),(0,[z110,z239,z3,z4,z5,z10]),(0,[z231,z0,z2,z3,z4,z118])],[(0,[z32,z3,z4,z5,z6,z452]),(0,[z39,z40,z3,z4,z5,z42]),(0,[z0,z2,z198,z292,z5,z6]),(0,[z769,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z15,z148,z6]),(0,[z37,z3,z15,z5,z6,z10]),(0,[z0,z3,z770,z4,z5,z6]),(0,[z9,z7,z3,z4,z5,z42]),(0,[z0,z3,z4,z5,z6,z771])],[(0,[z78,z3,z4,z5,z42,z10])]],
   [[(0,[z136,z3,z4,z5,z42,z10]),(0,[z2,z94,z4,z95,z6,z42])],[(0,[z32,z3,z325,z4,z5,z6]),(0,[z0,z3,z772,z4,z5,z6]),(0,[z29,z2,z4,z5,z42,z205]),(0,[z0,z308,z3,z4,z5,z6]),(0,[z0,z3,z155,z5,z6,z10]),(0,[z2,z3,z4,z5,z6,z773]),(0,[z0,z774,z3,z4,z5,z6])],[(0,[z146,z32,z3,z4,z5,z6]),(0,[z3,z4,z5,z42,z91,z10]),(0,[z3,z4,z5,z42,z10,z313]),(0,[z0,z25,z4,z5,z6,z91])],[(0,[z0,z3,z775,z4,z5,z6]),(0,[z9,z440,z3,z4,z5,z6]),(0,[z0,z2,z761,z3,z5,z6])],[(0,[z9,z2,z3,z4,z5,z480]),(0,[z9,z2,z3,z4,z148,z6]),(0,[z110,z3,z4,z5,z42,z10]),(0,[z0,z2,z3,z184,z80,z6])],[(0,[z27,z0,z3,z102,z5,z6]),(0,[z2,z3,z4,z5,z776,z6])],[(0,[z0,z3,z4,z5,z13,z10]),(0,[z24,z9,z191,z4,z5,z6]),(0,[z0,z58,z3,z52,z195,z6])],[(0,[z0,z777,z3,z4,z5,z6]),(0,[z0,z778,z3,z4,z5,z6]),(0,[z3,z4,z779,z180,z5,z6])],[(0,[z89,z3,z4,z5,z6,z42])],[(0,[z120,z3,z4,z5,z6,z575]),(0,[z0,z3,z4,z5,z6,z780]),(0,[z0,z781,z3,z4,z5,z6]),(0,[z0,z782,z3,z4,z5,z6]),(0,[z2,z3,z4,z80,z81,z42]),(0,[z0,z2,z783,z4,z5,z6]),(0,[z0,z240,z3,z4,z30,z6]),(0,[z0,z2,z4,z5,z6,z784])],[(0,[z2,z4,z5,z6,z42,z785]),(0,[z124,z203,z3,z4,z5,z6]),(0,[z786,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z787]),(0,[z145,z3,z325,z4,z5,z6]),(0,[z3,z4,z5,z6,z42,z10]),(0,[z0,z221,z196,z4,z5,z6])],[(0,[z0,z788,z3,z4,z5,z6]),(0,[z136,z2,z3,z4,z6,z84]),(0,[z789,z2,z3,z4,z5,z6]),(0,[z0,z7,z3,z61,z5,z6]),(0,[z0,z2,z3,z184,z5,z6]),(0,[z790,z2,z3,z4,z5,z6])],[(0,[z2,z3,z14,z4,z5,z212]),(0,[z32,z3,z4,z5,z401,z6]),(0,[z290,z2,z3,z15,z5,z6]),(0,[z3,z4,z5,z42,z10,z16]),(0,[z791,z2,z3,z4,z5,z6]),(0,[z27,z0,z3,z792,z5,z6]),(0,[z0,z2,z793,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z794]),(0,[z356,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z795]),(0,[z241,z2,z17,z4,z5,z6]),(0,[z143,z2,z3,z460,z8,z6]),(0,[z9,z2,z3,z217,z5,z6]),(0,[z2,z47,z3,z4,z180,z6])],[(0,[z32,z2,z3,z4,z148,z6]),(0,[z0,z3,z4,z5,z796,z6]),(0,[z9,z7,z3,z4,z5,z6]),(0,[z0,z94,z4,z95,z6,z10])]],
   [[],[(0,[z2,z3,z4,z797,z6,z42]),(0,[z9,z2,z3,z21,z76,z6]),(0,[z27,z124,z3,z4,z5,z6]),(0,[z619,z0,z2,z3,z4,z118])],[(0,[z189,z2,z3,z4,z48,z6]),(0,[z0,z295,z4,z5,z6,z10])],[(0,[z103,z2,z3,z4,z5,z135]),(0,[z0,z2,z798,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z799]),(0,[z0,z422,z138,z4,z5,z139])],[(0,[z0,z3,z4,z5,z106,z10]),(0,[z2,z3,z412,z5,z6,z42])],[(0,[z0,z800,z3,z4,z5,z6]),(0,[z47,z3,z4,z5,z42,z10]),(0,[z0,z801,z3,z4,z5,z6]),(0,[z0,z2,z196,z4,z80,z6])],[(0,[z0,z3,z4,z5,z6,z802]),(0,[z0,z2,z3,z803,z5,z6]),(0,[z3,z4,z218,z5,z6,z10])],[(0,[z0,z409,z191,z4,z5,z6]),(0,[z145,z3,z4,z5,z401,z6]),(0,[z113,z2,z171,z4,z5,z6]),(0,[z128,z446,z2,z4,z227,z6])],[(0,[z145,z3,z4,z5,z6,z494]),(0,[z381,z3,z4,z5,z6,z42]),(0,[z3,z4,z5,z6,z42,z320]),(0,[z78,z2,z3,z5,z42,z11]),(0,[z51,z0,z3,z4,z57,z6]),(0,[z176,z0,z2,z5,z77,z6]),(0,[z629,z2,z295,z4,z5,z6])],[(0,[z128,z0,z2,z54,z227,z6])],[(0,[z130,z451,z3,z4,z5,z6])],[(0,[z545,z2,z17,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z804]),(0,[z376,z2,z3,z4,z379,z6]),(0,[z0,z211,z295,z4,z5,z6])],[(0,[z2,z3,z387,z4,z5,z42]),(0,[z0,z2,z3,z4,z805,z6]),(0,[z0,z2,z138,z155,z5,z6]),(0,[z0,z3,z4,z5,z6,z806])],[(1,[z2,z3,z747,z5,z6]),(0,[z0,z2,z3,z5,z807,z6]),(0,[z0,z2,z196,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z808]),(0,[z9,z2,z3,z5,z750,z6]),(0,[z809,z0,z3,z5,z6,z10]),(0,[z0,z2,z810,z4,z5,z6]),(0,[z811,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z812,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z813]),(0,[z0,z2,z3,z814,z5,z6]),(1,[z2,z3,z460,z8,z6]),(0,[z0,z3,z191,z217,z5,z6]),(0,[z0,z280,z4,z5,z6,z10]),(0,[z29,z0,z2,z4,z5,z205])],[(0,[z0,z3,z184,z5,z6,z10]),(0,[z0,z2,z3,z815,z5,z6])],[(0,[z0,z2,z3,z4,z816,z6]),(0,[z0,z2,z3,z817,z5,z6]),(0,[z2,z3,z4,z5,z220,z42]),(0,[z3,z4,z5,z6,z42,z131]),(0,[z0,z2,z818,z4,z5,z6]),(0,[z0,z2,z3,z346,z5,z210])],[(0,[z130,z2,z3,z4,z285,z6])],[(0,[z2,z3,z4,z5,z6,z165]),(0,[z819,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z820])],[(0,[z9,z2,z3,z61,z5,z6]),(0,[z821,z2,z3,z4,z5,z6]),(0,[z0,z577,z3,z85,z5,z6]),(0,[z822,z3,z4,z5,z6,z10]),(0,[z0,z319,z3,z479,z5,z6]),(0,[z103,z7,z3,z4,z5,z209]),(0,[z0,z2,z3,z823,z5,z6])],[(0,[z2,z3,z4,z48,z824,z6]),(0,[z27,z124,z3,z102,z5,z6]),(0,[z605,z2,z3,z61,z5,z6])],[(0,[z109,z3,z4,z5,z42,z10])],[(0,[z0,z7,z3,z184,z5,z6]),(0,[z0,z2,z3,z4,z80,z442])],[(0,[z3,z4,z5,z6,z42,z166]),(0,[z825,z2,z3,z4,z5,z6]),(0,[z826,z2,z3,z4,z5,z6])],[(0,[z574,z3,z4,z5,z42,z10]),(0,[z3,z4,z5,z42,z10,z167]),(0,[z356,z7,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z827,z6])],[(0,[z241,z2,z186,z4,z5,z6]),(0,[z0,z828,z3,z4,z5,z6]),(0,[z78,z391,z2,z3,z5,z11]),(0,[z60,z0,z211,z3,z4,z118])],[(0,[z0,z2,z3,z829,z5,z6]),(0,[z136,z2,z3,z4,z8,z6]),(0,[z503,z3,z4,z5,z42,z10]),(0,[z0,z2,z198,z369,z5,z6]),(0,[z0,z830,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z831,z118])],[(0,[z2,z3,z4,z251,z6,z42]),(0,[z0,z3,z4,z5,z6,z832]),(0,[z0,z2,z3,z4,z797,z6]),(1,[z0,z381,z5,z77,z6])],[(0,[z2,z3,z317,z5,z6,z42]),(0,[z2,z3,z622,z4,z8,z6]),(0,[z189,z7,z3,z4,z48,z6]),(0,[z3,z833,z4,z5,z6,z42]),(0,[z834,z2,z3,z4,z5,z6])],[(0,[z128,z2,z4,z227,z6,z42]),(0,[z0,z2,z835,z4,z5,z6])]],
   [[],[(0,[z189,z2,z3,z4,z623,z6]),(0,[z3,z4,z5,z652,z42,z10]),(0,[z87,z3,z4,z5,z42,z10]),(0,[z0,z2,z3,z836,z5,z6]),(0,[z0,z3,z4,z5,z220,z10]),(0,[z837,z2,z3,z4,z5,z6]),(0,[z391,z2,z3,z4,z610,z6])],[(0,[z838,z0,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z776,z6])],[(0,[z2,z3,z4,z5,z135,z42]),(0,[z0,z3,z4,z5,z6,z839]),(0,[z113,z7,z171,z4,z5,z6]),(0,[z0,z2,z3,z5,z840,z6]),(0,[z0,z2,z3,z4,z251,z6]),(0,[z841,z2,z3,z4,z5,z6]),(0,[z376,z302,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z842]),(0,[z0,z3,z843,z4,z5,z6]),(0,[z635,z0,z2,z4,z5,z205]),(0,[z60,z0,z2,z3,z4,z831])],[(0,[z2,z33,z3,z4,z5,z212]),(0,[z0,z844,z3,z4,z5,z6]),(0,[z29,z0,z2,z4,z5,z784]),(0,[z0,z3,z4,z5,z845,z6])],[(0,[z0,z2,z3,z4,z846,z6]),(0,[z121,z2,z3,z14,z5,z6]),(0,[z9,z308,z3,z4,z5,z6])],[(0,[z0,z847,z4,z5,z6,z10])],[(0,[z20,z2,z3,z4,z5,z6]),(0,[z24,z0,z191,z4,z5,z6]),(0,[z0,z3,z4,z5,z848,z10]),(0,[z0,z849,z3,z4,z5,z6]),(0,[z0,z503,z4,z5,z6,z91])],[(0,[z0,z7,z196,z4,z5,z6]),(0,[z0,z7,z3,z4,z80,z81]),(0,[z0,z2,z4,z227,z6,z210])],[],[(0,[z0,z3,z4,z5,z6,z850]),(0,[z851,z2,z3,z5,z6,z42]),(0,[z0,z93,z3,z4,z5,z210]),(0,[z0,z240,z3,z155,z5,z6])],[(0,[z0,z2,z3,z852,z5,z6]),(0,[z0,z3,z4,z251,z6,z10]),(0,[z0,z2,z3,z4,z5,z853]),(0,[z3,z4,z5,z42,z173,z10])],[(0,[z0,z854,z3,z4,z5,z6]),(0,[z0,z2,z138,z4,z5,z784])],[(0,[z0,z855,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z856]),(0,[z51,z0,z3,z4,z857,z6]),(0,[z858,z0,z3,z5,z6,z10])],[(0,[z32,z49,z3,z4,z5,z6]),(0,[z0,z3,z4,z52,z12,z6]),(0,[z113,z171,z4,z5,z6,z10]),(0,[z2,z3,z4,z5,z6,z859])]],
   [[(0,[z176,z2,z5,z77,z6,z42])],[(0,[z0,z860,z3,z4,z5,z6]),(0,[z9,z2,z3,z184,z5,z6]),(0,[z86,z3,z4,z5,z6,z10])],[(0,[z221,z3,z4,z5,z6,z42]),(0,[z605,z2,z3,z184,z5,z6]),(0,[z3,z4,z5,z6,z301,z131])],[(0,[z32,z861,z3,z4,z5,z6]),(0,[z858,z0,z2,z3,z5,z6]),(0,[z0,z862,z3,z4,z5,z6]),(0,[z391,z2,z236,z4,z5,z6])],[(0,[z2,z3,z4,z5,z863,z6])],[(0,[z373,z9,z3,z4,z5,z6]),(0,[z864,z2,z3,z4,z5,z6]),(0,[z0,z865,z3,z4,z5,z6])],[(0,[z0,z861,z3,z4,z5,z6]),(0,[z373,z189,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z322,z42]),(0,[z2,z3,z546,z5,z6,z172])],[(0,[z241,z7,z186,z4,z5,z6]),(0,[z0,z203,z174,z4,z5,z6]),(0,[z0,z3,z4,z6,z10,z866])],[(0,[z0,z2,z867,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z868])],[(0,[z283,z448,z3,z4,z5,z6]),(0,[z869,z2,z3,z4,z5,z6]),(0,[z0,z870,z3,z4,z5,z6]),(0,[z0,z871,z3,z4,z5,z6])],[(0,[z0,z2,z507,z4,z5,z6]),(0,[z96,z2,z3,z54,z5,z6]),(0,[z872,z3,z4,z180,z5,z6])],[(0,[z32,z33,z3,z4,z5,z135]),(0,[z32,z159,z3,z4,z5,z6]),(0,[z2,z3,z15,z5,z148,z6]),(0,[z3,z4,z5,z77,z42,z10]),(0,[z0,z7,z3,z4,z5,z274]),(0,[z0,z2,z3,z873,z5,z6]),(0,[z422,z3,z4,z5,z6,z249]),(0,[z0,z2,z507,z4,z610,z6])],[(0,[z0,z874,z3,z4,z5,z6]),(0,[z2,z3,z875,z4,z5,z6]),(0,[z603,z3,z4,z5,z6,z626])],[(0,[z876,z2,z3,z4,z5,z6]),(0,[z0,z2,z877,z4,z5,z6]),(0,[z878,z2,z3,z4,z5,z210])],[(0,[z0,z3,z4,z5,z879,z6]),(0,[z121,z2,z3,z747,z5,z6]),(0,[z0,z3,z4,z5,z6,z880]),(0,[z39,z2,z3,z4,z5,z853]),(0,[z881,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z882]),(0,[z0,z3,z4,z5,z883,z6])],[(0,[z0,z7,z3,z4,z251,z6]),(0,[z0,z884,z3,z4,z5,z6]),(0,[z9,z3,z4,z5,z43,z75]),(0,[z0,z2,z885,z4,z5,z6])]],
   [[(0,[z0,z2,z4,z5,z6,z785]),(0,[z0,z154,z3,z4,z5,z220]),(0,[z886,z0,z3,z4,z5,z6])],[(0,[z887,z2,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z165]),(0,[z0,z2,z3,z551,z76,z6])],[(0,[z0,z888,z3,z4,z5,z6]),(0,[z121,z7,z3,z14,z5,z6]),(0,[z9,z2,z196,z4,z5,z6]),(0,[z889,z2,z3,z4,z5,z6]),(0,[z0,z2,z890,z4,z5,z6]),(0,[z726,z0,z3,z4,z6,z10]),(0,[z0,z891,z3,z4,z5,z6]),(0,[z0,z154,z3,z346,z5,z6])],[(0,[z32,z3,z366,z4,z5,z6]),(0,[z24,z0,z191,z217,z5,z6]),(0,[z0,z3,z4,z5,z6,z131]),(0,[z254,z422,z3,z4,z5,z6]),(0,[z605,z2,z196,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z892]),(0,[z0,z3,z318,z4,z5,z10]),(0,[z127,z0,z3,z102,z5,z6]),(0,[z0,z7,z3,z4,z5,z352])],[(0,[z283,z120,z3,z4,z5,z6]),(0,[z3,z4,z5,z42,z10,z486]),(0,[z893,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z323,z10]),(1,[z0,z280,z102,z5,z6]),(0,[z2,z3,z4,z5,z6,z894]),(0,[z0,z381,z3,z5,z77,z6]),(0,[z446,z2,z3,z4,z5,z220]),(0,[z78,z0,z31,z3,z5,z11])],[(0,[z0,z3,z366,z4,z5,z6]),(0,[z0,z2,z3,z895,z5,z6]),(0,[z0,z58,z3,z4,z469,z6]),(0,[z3,z4,z5,z401,z6,z10]),(0,[z0,z31,z3,z4,z285,z6])],[(0,[z2,z3,z4,z5,z694,z42]),(0,[z446,z2,z3,z346,z5,z6]),(0,[z896,z2,z3,z4,z5,z6])],[(0,[z0,z897,z3,z4,z5,z6]),(0,[z128,z0,z4,z227,z6,z10])],[(0,[z0,z3,z4,z5,z6,z744]),(0,[z898,z0,z3,z4,z5,z6])],[(0,[z899,z0,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z900,z6])],[(0,[z901,z0,z2,z3,z5,z6]),(0,[z122,z0,z3,z417,z5,z6]),(0,[z0,z902,z3,z4,z5,z6])],[(0,[z124,z3,z85,z4,z5,z6])],[(0,[z0,z2,z3,z679,z76,z6]),(0,[z128,z0,z7,z4,z227,z6]),(0,[z0,z903,z3,z4,z5,z6])],[(0,[z0,z904,z3,z4,z5,z6]),(0,[z905,z0,z3,z4,z5,z6]),(0,[z2,z3,z4,z906,z5,z6]),(0,[z2,z3,z4,z5,z6,z907]),(0,[z0,z3,z4,z5,z6,z908]),(0,[z0,z2,z196,z4,z5,z118])]],
   [[(0,[z0,z2,z3,z76,z6,z59])],[(0,[z9,z2,z3,z829,z5,z6]),(0,[z0,z909,z3,z4,z5,z6]),(0,[z0,z2,z3,z671,z76,z6])],[(0,[z0,z2,z3,z910,z5,z6]),(0,[z3,z4,z5,z227,z42,z10])],[(0,[z526,z120,z3,z4,z5,z6]),(0,[z911,z2,z3,z4,z5,z6]),(0,[z130,z2,z3,z4,z610,z6])],[(0,[z0,z3,z4,z5,z197,z6]),(0,[z0,z7,z3,z4,z5,z639]),(0,[z851,z0,z3,z5,z6,z10]),(0,[z160,z0,z2,z4,z5,z205])],[(0,[z0,z912,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z368]),(0,[z0,z2,z3,z913,z5,z6]),(0,[z198,z3,z4,z5,z42,z10]),(0,[z0,z3,z412,z5,z6,z10]),(0,[z0,z7,z507,z4,z5,z6]),(0,[z914,z2,z3,z4,z5,z6]),(0,[z915,z2,z3,z4,z5,z6])],[(0,[z809,z0,z2,z3,z5,z6]),(0,[z0,z3,z4,z5,z210,z916]),(0,[z0,z302,z3,z4,z30,z6]),(0,[z0,z2,z3,z4,z5,z831])],[(0,[z0,z917,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z251,z6]),(0,[z0,z918,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z730,z6]),(0,[z0,z2,z236,z5,z6,z11]),(0,[z919,z2,z3,z4,z5,z6])],[(0,[z851,z0,z2,z3,z5,z6]),(0,[z376,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z920,z5,z6]),(0,[z176,z0,z5,z77,z6,z10]),(0,[z2,z3,z4,z921,z5,z6])],[(0,[z0,z2,z3,z4,z5,z922]),(0,[z250,z2,z3,z4,z5,z42]),(0,[z189,z2,z3,z4,z824,z6]),(0,[z2,z3,z4,z5,z923,z6]),(0,[z924,z2,z3,z4,z5,z220])],[(0,[z0,z2,z3,z4,z581,z81]),(0,[z0,z2,z196,z184,z5,z6])],[(0,[z32,z3,z668,z4,z5,z6]),(0,[z2,z3,z14,z747,z5,z6]),(0,[z617,z0,z3,z102,z5,z6]),(1,[z0,z3,z4,z857,z6]),(1,[z0,z3,z4,z5,z848])],[(0,[z0,z2,z925,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z674]),(0,[z0,z3,z4,z857,z57,z6]),(0,[z926,z2,z3,z4,z5,z6]),(0,[z0,z927,z3,z4,z5,z6]),(1,[z0,z2,z4,z227,z210]),(0,[z0,z2,z3,z928,z5,z6]),(0,[z0,z929,z3,z4,z5,z6]),(0,[z0,z2,z3,z478,z76,z6])],[(0,[z2,z3,z4,z5,z423,z42]),(0,[z0,z422,z3,z4,z5,z6]),(0,[z3,z4,z5,z6,z301,z10]),(0,[z0,z2,z3,z4,z5,z210])],[(0,[z0,z2,z3,z4,z5,z212]),(0,[z0,z2,z3,z4,z5,z930]),(0,[z382,z0,z2,z5,z77,z6]),(0,[z0,z2,z4,z30,z6,z205])]],
   [[(0,[z2,z3,z4,z5,z6,z42]),(0,[z0,z3,z4,z5,z931,z6]),(0,[z446,z93,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z42,z10]),(0,[z9,z2,z3,z4,z5,z853])],[(0,[z2,z40,z3,z4,z5,z42]),(0,[z24,z0,z28,z4,z5,z6]),(0,[z0,z932,z3,z4,z5,z6])],[(0,[z391,z2,z3,z4,z5,z6]),(0,[z3,z4,z102,z5,z42,z10]),(0,[z526,z603,z3,z4,z5,z6]),(0,[z933,z2,z3,z4,z5,z6]),(0,[z60,z0,z2,z295,z4,z118])],[(0,[z33,z3,z4,z5,z42,z10]),(0,[z0,z3,z4,z5,z349,z10]),(0,[z496,z2,z3,z4,z5,z42]),(0,[z3,z4,z5,z6,z10,z907]),(0,[z2,z3,z4,z5,z6,z934])],[(0,[z0,z935,z3,z4,z5,z6]),(0,[z0,z2,z3,z936,z5,z6]),(0,[z0,z7,z3,z803,z5,z6]),(0,[z937,z2,z3,z4,z5,z6]),(0,[z924,z2,z3,z4,z5,z6]),(0,[z130,z2,z236,z4,z5,z6])],[(0,[z145,z2,z3,z4,z5,z212]),(0,[z0,z1,z3,z5,z257,z6]),(0,[z109,z373,z0,z3,z5,z6]),(0,[z938,z2,z3,z4,z5,z6]),(0,[z939,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z180,z76,z6])],[(0,[z37,z2,z3,z587,z5,z6]),(0,[z373,z0,z3,z4,z5,z6]),(0,[z3,z41,z4,z5,z42,z10]),(0,[z0,z2,z3,z4,z6,z866]),(0,[z0,z2,z3,z4,z5,z940])],[(0,[z0,z941,z3,z4,z5,z6]),(0,[z113,z2,z258,z4,z5,z6]),(0,[z2,z3,z4,z824,z8,z6]),(0,[z0,z2,z942,z4,z5,z6]),(0,[z0,z943,z3,z4,z5,z6]),(0,[z0,z944,z3,z4,z5,z6]),(0,[z176,z0,z2,z5,z945,z6])],[(0,[z0,z2,z3,z946,z5,z6]),(0,[z373,z3,z4,z5,z8,z6]),(0,[z0,z2,z3,z460,z5,z6]),(0,[z121,z2,z3,z38,z5,z6]),(0,[z3,z4,z5,z139,z42,z10]),(0,[z947,z3,z4,z5,z6,z42]),(0,[z2,z3,z948,z4,z5,z6])],[(0,[z0,z2,z3,z949,z5,z6]),(1,[z0,z3,z792,z5,z6]),(0,[z0,z3,z4,z5,z6,z950])],[(0,[z0,z3,z4,z5,z575,z10]),(0,[z46,z0,z2,z47,z3,z6]),(0,[z0,z2,z3,z4,z227,z210])],[(0,[z83,z2,z3,z4,z68,z6]),(0,[z0,z3,z951,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z952])],[(0,[z189,z2,z3,z4,z68,z6]),(0,[z2,z3,z4,z5,z6,z953]),(0,[z0,z383,z3,z4,z5,z6]),(0,[z0,z954,z3,z4,z5,z6])],[(0,[z0,z280,z4,z102,z5,z6])],[(0,[z0,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z5,z955]),(0,[z424,z2,z3,z4,z5,z6]),(0,[z241,z3,z4,z5,z42,z10]),(0,[z2,z3,z460,z5,z8,z6]),(0,[z9,z2,z507,z4,z5,z6]),(0,[z430,z0,z2,z5,z77,z6]),(0,[z0,z93,z3,z54,z5,z6])]],
   [[(0,[z485,z2,z3,z4,z5,z42]),(0,[z0,z3,z317,z5,z6,z10]),(0,[z3,z4,z328,z5,z42,z10]),(0,[z0,z3,z4,z5,z437,z10])],[(0,[z956,z2,z3,z4,z5,z6]),(0,[z0,z3,z957,z5,z6,z10]),(0,[z0,z2,z3,z155,z379,z6]),(0,[z0,z958,z3,z4,z5,z6]),(0,[z0,z959,z3,z4,z5,z6])],[(0,[z9,z2,z3,z4,z5,z43]),(0,[z2,z3,z960,z4,z5,z6]),(0,[z50,z0,z3,z4,z5,z10]),(0,[z2,z3,z4,z5,z961,z6])],[(0,[z9,z3,z4,z5,z883,z6]),(0,[z0,z538,z3,z4,z512,z6]),(0,[z2,z3,z4,z5,z6,z962])],[(0,[z0,z963,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z492,z10]),(0,[z0,z3,z4,z5,z6,z964])],[(0,[z0,z3,z4,z5,z135,z10]),(0,[z376,z7,z3,z4,z5,z6]),(0,[z965,z2,z3,z4,z5,z6]),(0,[z629,z221,z3,z4,z5,z6]),(0,[z966,z0,z3,z4,z5,z6])],[(0,[z583,z2,z3,z140,z5,z6]),(0,[z2,z3,z4,z5,z6,z967]),(0,[z0,z152,z280,z4,z5,z6])],[(0,[z0,z3,z833,z4,z5,z6]),(0,[z968,z0,z3,z4,z5,z6]),(0,[z2,z3,z54,z5,z6,z42]),(0,[z893,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z969]),(0,[z0,z3,z4,z5,z6,z970]),(0,[z0,z971,z3,z4,z5,z6])],[(0,[z2,z3,z972,z5,z6,z42]),(0,[z9,z3,z4,z5,z6,z131]),(0,[z410,z0,z3,z4,z125,z6])],[(0,[z9,z2,z3,z4,z5,z331]),(0,[z78,z0,z7,z3,z5,z11])],[(0,[z263,z32,z0,z3,z5,z6]),(0,[z109,z2,z47,z3,z6,z42]),(0,[z0,z7,z3,z4,z5,z210]),(0,[z973,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z8,z212]),(0,[z0,z7,z3,z4,z5,z212]),(0,[z2,z3,z325,z4,z5,z6]),(0,[z9,z3,z366,z4,z5,z6]),(0,[z189,z3,z4,z48,z6,z10]),(0,[z0,z40,z3,z4,z5,z43]),(0,[z78,z0,z2,z3,z285,z11])],[(0,[z0,z3,z4,z5,z974,z6]),(0,[z3,z4,z5,z42,z10,z452]),(0,[z29,z3,z4,z5,z42,z10]),(0,[z0,z3,z4,z5,z6,z320]),(0,[z0,z2,z138,z4,z5,z594]),(0,[z78,z0,z2,z507,z5,z11])],[(0,[z0,z2,z3,z4,z975,z6]),(0,[z3,z4,z15,z5,z42,z10]),(0,[z2,z3,z4,z5,z639,z42]),(0,[z2,z3,z4,z5,z6,z976]),(0,[z2,z3,z4,z180,z76,z6])],[],[(0,[z2,z3,z4,z5,z307,z42]),(0,[z2,z196,z4,z5,z6,z42]),(0,[z9,z2,z3,z4,z30,z6]),(0,[z9,z3,z4,z5,z6,z166]),(0,[z0,z3,z707,z4,z5,z6]),(0,[z933,z7,z3,z4,z5,z6]),(0,[z391,z7,z3,z4,z5,z6]),(0,[z60,z0,z2,z196,z4,z118])]],
   [[(0,[z145,z861,z3,z4,z5,z6]),(0,[z290,z2,z3,z4,z8,z6]),(0,[z2,z3,z4,z5,z644,z42]),(0,[z9,z154,z3,z4,z5,z6]),(0,[z977,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z978,z5,z6])],[(1,[z0,z707,z4,z5,z6]),(0,[z0,z7,z3,z936,z5,z6])],[(0,[z9,z440,z3,z4,z5,z43]),(0,[z0,z2,z3,z4,z979,z6]),(0,[z60,z605,z2,z3,z4,z118]),(0,[z0,z2,z196,z61,z5,z6]),(0,[z563,z3,z4,z5,z6,z301])],[(0,[z980,z2,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z368]),(0,[z0,z981,z3,z4,z5,z6])],[(0,[z0,z7,z942,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z982])],[(0,[z0,z7,z3,z460,z5,z6]),(0,[z983,z2,z3,z4,z5,z6]),(0,[z0,z984,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z227,z210]),(0,[z248,z3,z4,z5,z6,z131])],[(0,[z0,z440,z3,z4,z5,z10]),(0,[z0,z3,z280,z102,z5,z6]),(0,[z7,z3,z4,z921,z5,z6]),(0,[z128,z0,z2,z346,z227,z6]),(0,[z0,z31,z3,z4,z610,z6])],[(0,[z2,z3,z4,z5,z401,z6]),(0,[z0,z2,z3,z622,z76,z6]),(0,[z629,z2,z3,z4,z5,z6]),(0,[z20,z7,z3,z4,z5,z6]),(0,[z985,z381,z3,z4,z5,z6])],[(0,[z986,z2,z3,z4,z5,z6])],[(0,[z9,z3,z4,z5,z197,z6]),(0,[z0,z987,z3,z4,z5,z6]),(0,[z20,z2,z3,z21,z76,z6])],[(0,[z0,z211,z3,z4,z5,z6])],[(0,[z32,z2,z3,z317,z5,z6]),(0,[z0,z3,z4,z5,z6,z988]),(0,[z0,z788,z3,z4,z5,z43]),(0,[z424,z7,z3,z4,z5,z6]),(0,[z0,z989,z3,z4,z5,z6])],[(0,[z0,z2,z990,z4,z5,z6])],[(0,[z37,z2,z3,z15,z5,z6]),(0,[z143,z2,z3,z4,z824,z6]),(0,[z7,z3,z4,z5,z6,z42]),(0,[z0,z3,z4,z5,z6,z166]),(0,[z0,z3,z4,z328,z6,z363]),(0,[z0,z2,z94,z4,z5,z210]),(0,[z0,z2,z3,z4,z30,z6]),(0,[z991,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z317,z5,z6]),(0,[z2,z3,z4,z5,z42,z398]),(0,[z7,z3,z4,z5,z42,z10]),(0,[z9,z7,z3,z4,z5,z43]),(0,[z0,z154,z3,z4,z5,z6]),(0,[z0,z2,z3,z992,z5,z6]),(0,[z993,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z994,z6]),(0,[z0,z2,z3,z995,z5,z6])]],
   [[(0,[z0,z3,z4,z5,z513,z10]),(0,[z175,z3,z4,z5,z42,z10])],[(0,[z27,z0,z3,z4,z5,z212]),(0,[z128,z3,z4,z5,z42,z10]),(0,[z192,z0,z2,z5,z77,z6])],[(0,[z0,z996,z3,z4,z5,z6]),(0,[z2,z138,z4,z5,z139,z42]),(0,[z2,z3,z4,z610,z6,z42]),(0,[z997,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z516,z10]),(0,[z0,z3,z4,z5,z517,z10]),(0,[z0,z7,z3,z4,z5,z10]),(0,[z0,z2,z3,z998,z5,z6])],[(0,[z446,z2,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z5,z210]),(0,[z9,z422,z3,z4,z5,z6]),(0,[z0,z58,z3,z4,z857,z6])],[(0,[z9,z2,z3,z4,z5,z212]),(0,[z32,z3,z4,z5,z197,z6]),(0,[z999,z0,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z5,z13]),(0,[z143,z89,z3,z4,z8,z6]),(0,[z24,z356,z191,z4,z5,z6]),(0,[z29,z0,z4,z5,z10,z205]),(0,[z0,z3,z4,z5,z6,z1000]),(0,[z0,z2,z3,z4,z1001,z6])],[(0,[z130,z2,z3,z4,z5,z6]),(0,[z128,z0,z154,z4,z227,z6])],[(0,[z0,z1002,z3,z4,z5,z6]),(0,[z175,z2,z3,z4,z5,z42]),(0,[z0,z2,z25,z217,z5,z6]),(0,[z1003,z2,z3,z4,z5,z6]),(0,[z1004,z2,z3,z4,z5,z6]),(0,[z0,z1005,z3,z4,z5,z6])],[(0,[z145,z3,z4,z5,z6,z173]),(0,[z0,z1006,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z5,z406]),(0,[z0,z707,z191,z4,z5,z6]),(0,[z254,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z54,z5,z220])],[(0,[z565,z2,z3,z4,z8,z6]),(0,[z99,z3,z4,z5,z42,z10]),(0,[z0,z31,z236,z4,z5,z6])],[(0,[z485,z0,z3,z4,z5,z10]),(0,[z1007,z2,z3,z4,z5,z6]),(0,[z0,z1008,z3,z4,z5,z6]),(0,[z0,z240,z3,z289,z5,z6])],[(0,[z2,z3,z4,z5,z6,z1009]),(0,[z1010,z2,z3,z4,z5,z6]),(0,[z134,z2,z3,z4,z30,z6])],[(0,[z0,z2,z3,z1011,z5,z6]),(0,[z0,z152,z3,z85,z5,z6]),(0,[z2,z3,z4,z1012,z5,z6])],[(0,[z239,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1013]),(0,[z0,z2,z4,z5,z784,z205])],[(0,[z465,z2,z3,z4,z5,z42]),(0,[z109,z0,z2,z280,z5,z6]),(0,[z0,z2,z1014,z4,z5,z6])],[(0,[z37,z2,z3,z15,z148,z6]),(0,[z9,z2,z3,z460,z5,z6]),(0,[z2,z3,z4,z64,z6,z151]),(0,[z86,z2,z3,z5,z195,z6]),(0,[z263,z0,z7,z3,z5,z6])],[(0,[z0,z2,z3,z4,z1015,z6]),(1,[z2,z3,z4,z824,z6]),(0,[z2,z3,z4,z1016,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1017]),(0,[z0,z2,z3,z1018,z5,z6]),(0,[z128,z9,z2,z4,z227,z6]),(0,[z1019,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1020,z6]),(0,[z37,z3,z4,z5,z42,z10]),(0,[z103,z2,z3,z4,z5,z42]),(0,[z9,z3,z951,z4,z5,z6]),(0,[z983,z7,z3,z4,z5,z6]),(0,[z0,z1021,z3,z4,z5,z6]),(0,[z0,z451,z3,z4,z285,z6]),(1,[z0,z2,z196,z4,z118])],[(0,[z37,z2,z3,z648,z5,z6]),(0,[z9,z383,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1022]),(0,[z1023,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z5,z6]),(0,[z0,z2,z94,z4,z735,z6]),(0,[z0,z2,z3,z4,z30,z139]),(0,[z0,z2,z3,z5,z982,z11])],[(0,[z32,z245,z3,z4,z5,z6]),(0,[z0,z2,z1024,z4,z5,z6]),(0,[z94,z3,z4,z5,z42,z10]),(0,[z0,z2,z3,z262,z76,z6]),(0,[z109,z0,z47,z3,z6,z10]),(0,[z629,z7,z3,z4,z5,z6]),(0,[z985,z2,z3,z4,z5,z6])],[(0,[z9,z3,z4,z5,z6,z10]),(0,[z254,z3,z4,z5,z6,z320]),(0,[z1025,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1026,z5,z6]),(0,[z605,z3,z4,z5,z6,z10]),(0,[z0,z1027,z3,z4,z5,z6])],[(0,[z0,z3,z191,z4,z5,z212]),(0,[z2,z3,z346,z5,z6,z42]),(0,[z2,z3,z4,z5,z6,z1028]),(0,[z175,z3,z4,z5,z6,z452]),(0,[z661,z0,z2,z4,z227,z6])],[(0,[z0,z2,z3,z4,z5,z1029])],[(0,[z7,z3,z325,z4,z5,z6]),(1,[z0,z2,z4,z735,z6])],[(0,[z37,z7,z3,z15,z5,z6]),(0,[z9,z2,z3,z4,z5,z705]),(0,[z0,z2,z3,z1030,z5,z6]),(0,[z0,z7,z3,z4,z30,z6]),(0,[z128,z0,z93,z4,z227,z6])],[(0,[z0,z7,z3,z317,z5,z6]),(0,[z0,z1031,z3,z4,z5,z6]),(0,[z248,z563,z3,z4,z5,z6])],[(0,[z120,z3,z4,z5,z42,z10]),(0,[z0,z3,z4,z5,z572,z10]),(0,[z0,z563,z3,z4,z5,z6]),(0,[z78,z0,z3,z5,z10,z11])],[(0,[z32,z190,z3,z4,z5,z6]),(0,[z1032,z0,z2,z3,z5,z6]),(0,[z2,z3,z4,z5,z6,z1033])],[],[(0,[z99,z3,z4,z5,z6,z452]),(0,[z0,z3,z4,z5,z10,z59])],[(0,[z451,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z1034,z5,z6]),(0,[z86,z58,z3,z4,z52,z6]),(0,[z355,z0,z3,z4,z6,z313]),(0,[z446,z7,z3,z4,z5,z6]),(0,[z1035,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z196,z4,z118])]],
   [[(0,[z0,z152,z3,z792,z5,z6])],[(0,[z2,z3,z169,z5,z6,z42]),(0,[z263,z2,z3,z5,z6,z42]),(0,[z9,z3,z4,z5,z6,z320]),(0,[z248,z3,z4,z5,z6,z10]),(0,[z130,z7,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z209,z848])],[(0,[z103,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z180,z5,z6])],[(1,[z0,z2,z5,z945,z6]),(0,[z0,z3,z4,z779,z5,z6])],[(0,[z7,z3,z4,z5,z401,z6])],[(0,[z0,z2,z3,z1036,z5,z6]),(0,[z0,z3,z346,z5,z6,z10]),(0,[z96,z2,z3,z4,z5,z220])],[(0,[z0,z2,z3,z4,z735,z6]),(0,[z1037,z2,z3,z4,z5,z6])],[(0,[z3,z191,z4,z5,z42,z10]),(0,[z0,z3,z4,z5,z857,z6]),(0,[z0,z867,z4,z5,z6,z10]),(0,[z96,z2,z3,z346,z5,z6]),(0,[z0,z1038,z3,z4,z5,z6]),(0,[z0,z2,z196,z4,z5,z81])],[(0,[z0,z3,z4,z5,z6,z1039]),(0,[z138,z3,z4,z5,z42,z10]),(0,[z3,z4,z5,z42,z10,z118]),(0,[z2,z3,z4,z5,z6,z1040]),(0,[z1041,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z52,z857,z6]),(0,[z239,z7,z3,z4,z5,z6])],[(0,[z112,z2,z3,z4,z5,z6]),(0,[z0,z1042,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z408,z10]),(0,[z3,z4,z5,z151,z42,z10]),(0,[z1043,z2,z3,z4,z5,z209]),(0,[z0,z191,z4,z217,z5,z6])],[(0,[z0,z1044,z3,z4,z5,z6]),(0,[z0,z2,z3,z1045,z5,z6])],[(0,[z0,z2,z3,z4,z5,z135]),(0,[z2,z765,z186,z4,z5,z6]),(0,[z27,z3,z4,z5,z42,z10])],[(0,[z2,z861,z3,z4,z5,z6]),(0,[z143,z2,z3,z169,z8,z6]),(0,[z0,z2,z5,z77,z6,z694])],[(0,[z0,z3,z4,z5,z6,z1046]),(0,[z0,z2,z3,z747,z5,z6])],[(0,[z9,z211,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z398]),(0,[z134,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z155,z5,z6])]],
   [[(0,[z0,z2,z3,z5,z1047,z6]),(0,[z0,z2,z1048,z4,z5,z6]),(0,[z0,z3,z169,z5,z6,z10]),(0,[z0,z2,z1049,z4,z5,z6]),(0,[z1050,z2,z3,z4,z5,z6]),(0,[z605,z211,z3,z4,z5,z6])],[(0,[z3,z325,z366,z4,z5,z6]),(0,[z0,z2,z3,z460,z8,z6]),(0,[z0,z2,z3,z1051,z5,z6]),(0,[z0,z2,z3,z5,z945,z6]),(0,[z1052,z2,z3,z4,z5,z6])],[(0,[z241,z2,z765,z4,z5,z6]),(0,[z121,z2,z3,z5,z375,z6]),(0,[z3,z4,z80,z5,z42,z10]),(0,[z0,z440,z3,z4,z5,z209]),(0,[z127,z0,z3,z5,z6,z167])],[(0,[z0,z2,z3,z5,z1053,z6]),(0,[z9,z2,z3,z317,z5,z6]),(0,[z0,z2,z3,z1054,z5,z6])],[(0,[z0,z2,z3,z1055,z5,z6]),(0,[z0,z788,z3,z4,z5,z10]),(0,[z0,z1056,z3,z4,z5,z6]),(0,[z0,z2,z3,z1057,z5,z6]),(0,[z0,z3,z4,z5,z6,z1058]),(0,[z0,z1059,z3,z4,z5,z6])],[(0,[z171,z3,z4,z5,z42,z10]),(0,[z0,z2,z3,z4,z1060,z6]),(0,[z2,z3,z4,z5,z6,z1061]),(0,[z1062,z2,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z624,z10]),(0,[z493,z2,z186,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z423]),(0,[z2,z3,z4,z5,z6,z1063])],[(0,[z2,z3,z4,z5,z6,z1064]),(0,[z99,z0,z3,z4,z5,z10]),(0,[z9,z7,z3,z4,z5,z10]),(0,[z0,z3,z4,z5,z6,z1065]),(0,[z128,z0,z2,z4,z227,z220])],[(0,[z32,z358,z3,z4,z5,z6]),(0,[z3,z366,z4,z5,z6,z42]),(0,[z0,z3,z4,z5,z6,z1066]),(0,[z0,z31,z3,z4,z5,z6]),(0,[z0,z1067,z3,z4,z5,z6]),(0,[z1068,z2,z3,z4,z5,z6])],[(0,[z1069,z2,z3,z4,z5,z6]),(0,[z0,z3,z54,z5,z6,z10]),(0,[z0,z1070,z3,z4,z5,z6])],[(0,[z9,z2,z94,z4,z95,z6]),(0,[z231,z0,z2,z4,z5,z205])],[(0,[z115,z2,z3,z4,z5,z42]),(0,[z78,z9,z2,z3,z5,z11]),(0,[z1071,z2,z3,z4,z5,z6])],[(0,[z0,z1072,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z43,z10]),(0,[z2,z3,z4,z5,z42,z554]),(0,[z124,z2,z3,z41,z5,z6]),(0,[z1073,z2,z3,z4,z5,z6]),(0,[z0,z2,z182,z41,z5,z6]),(0,[z0,z302,z3,z155,z5,z6]),(0,[z0,z240,z3,z4,z379,z6])],[],[(0,[z405,z0,z3,z4,z5,z10]),(0,[z0,z1074,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1075,z6]),(0,[z3,z4,z5,z42,z339,z10]),(0,[z1076,z2,z3,z4,z5,z6]),(0,[z27,z0,z458,z3,z5,z6]),(0,[z0,z7,z3,z4,z5,z209]),(0,[z103,z7,z3,z4,z5,z6]),(0,[z1077,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1078,z5,z6]),(0,[z1079,z2,z3,z4,z5,z6]),(0,[z78,z0,z2,z236,z5,z11])]],
   [[(0,[z9,z152,z3,z85,z5,z6]),(0,[z96,z93,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z735,z6])],[(0,[z2,z3,z4,z48,z6,z151]),(0,[z0,z196,z4,z5,z6,z10]),(0,[z0,z1080,z3,z4,z5,z6])],[(0,[z128,z0,z2,z4,z227,z6]),(1,[z0,z2,z4,z5,z784]),(0,[z3,z4,z5,z6,z165,z166])],[(0,[z120,z2,z3,z4,z148,z6]),(0,[z2,z3,z4,z5,z42,z567]),(0,[z2,z3,z4,z5,z6,z1081])],[(0,[z3,z186,z4,z5,z42,z10]),(0,[z143,z3,z4,z5,z42,z10]),(0,[z9,z2,z3,z4,z1015,z6]),(0,[z0,z2,z3,z5,z1082,z6]),(0,[z1083,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z747,z5,z6]),(0,[z2,z3,z4,z5,z6,z1084]),(0,[z3,z4,z5,z6,z249,z10]),(0,[z112,z7,z3,z4,z5,z6]),(0,[z109,z0,z2,z761,z3,z6])],[(0,[z0,z1085,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z10,z226])],[(0,[z9,z2,z3,z54,z5,z6]),(0,[z0,z2,z1086,z4,z5,z6])],[(0,[z2,z3,z4,z5,z42,z578]),(0,[z2,z3,z4,z460,z8,z6]),(0,[z263,z2,z3,z5,z401,z6]),(0,[z0,z1087,z3,z4,z5,z6]),(0,[z0,z2,z94,z4,z95,z6]),(0,[z0,z1088,z3,z4,z5,z6]),(0,[z0,z2,z3,z1089,z5,z6]),(0,[z109,z2,z3,z180,z5,z6])],[(0,[z0,z3,z1090,z4,z5,z6]),(0,[z0,z3,z85,z792,z5,z6]),(0,[z0,z2,z3,z65,z285,z6])],[(0,[z0,z2,z1091,z4,z5,z6]),(0,[z263,z0,z3,z5,z6,z10]),(0,[z0,z3,z4,z5,z220,z1092]),(0,[z0,z221,z295,z4,z5,z6])],[(0,[z9,z2,z3,z4,z5,z408]),(0,[z2,z3,z4,z30,z6,z42]),(0,[z263,z86,z2,z3,z5,z6]),(0,[z0,z7,z3,z155,z5,z6]),(0,[z1093,z2,z3,z4,z5,z6])],[(0,[z2,z198,z41,z5,z6,z42]),(0,[z0,z2,z3,z5,z195,z6])],[(0,[z0,z1094,z3,z4,z5,z6])],[(0,[z9,z2,z3,z4,z5,z575]),(0,[z0,z2,z3,z5,z257,z6]),(0,[z176,z3,z4,z5,z42,z10]),(0,[z0,z2,z198,z5,z945,z6])],[(0,[z1,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z4,z5,z1095]),(0,[z0,z2,z3,z1096,z5,z6]),(0,[z7,z3,z4,z180,z5,z6]),(0,[z0,z2,z3,z289,z379,z6]),(0,[z665,z0,z2,z3,z4,z118])]],
   [[(0,[z9,z563,z3,z4,z5,z6]),(0,[z463,z0,z3,z102,z5,z6]),(0,[z0,z203,z707,z4,z5,z6]),(0,[z0,z1097,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z784])],[(0,[z0,z2,z1098,z4,z5,z6]),(0,[z31,z3,z4,z5,z6,z42]),(0,[z2,z3,z61,z5,z6,z42]),(0,[z0,z3,z4,z1099,z5,z6]),(0,[z0,z2,z1100,z4,z5,z6])],[(0,[z33,z3,z4,z5,z6,z212]),(0,[z0,z3,z85,z677,z5,z6]),(0,[z2,z3,z4,z148,z6,z42]),(0,[z0,z2,z3,z4,z1101,z6]),(0,[z3,z4,z5,z6,z249,z320])],[(0,[z0,z2,z3,z148,z77,z6]),(0,[z2,z3,z4,z5,z42,z595]),(0,[z0,z2,z94,z4,z330,z6])],[(0,[z0,z1102,z3,z4,z5,z6]),(0,[z189,z3,z4,z5,z42,z10]),(0,[z0,z138,z4,z5,z139,z10]),(0,[z0,z3,z4,z610,z6,z10]),(0,[z0,z1103,z3,z4,z5,z6])],[(0,[z203,z3,z4,z5,z42,z10]),(0,[z2,z3,z4,z285,z6,z42]),(0,[z1104,z2,z3,z4,z5,z6])],[(0,[z0,z1105,z3,z4,z5,z6]),(0,[z2,z541,z4,z5,z6,z42]),(0,[z2,z3,z949,z5,z6,z42]),(0,[z1106,z2,z3,z4,z5,z6])],[(0,[z113,z2,z171,z317,z5,z6]),(0,[z3,z4,z5,z42,z10,z11]),(0,[z0,z116,z174,z4,z5,z6]),(0,[z109,z0,z7,z47,z3,z6])],[(0,[z9,z2,z3,z4,z5,z513]),(0,[z2,z171,z4,z5,z6,z652]),(0,[z0,z2,z1107,z3,z4,z6]),(0,[z3,z4,z5,z6,z10,z1081]),(0,[z1108,z2,z3,z4,z5,z6])],[(0,[z0,z2,z1109,z4,z5,z6]),(0,[z1110,z2,z3,z4,z5,z6])],[(0,[z32,z33,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z44,z42]),(0,[z0,z3,z4,z30,z6,z10]),(0,[z0,z2,z3,z289,z5,z6])],[(0,[z241,z2,z73,z4,z5,z6]),(0,[z283,z2,z3,z4,z5,z42]),(0,[z2,z3,z4,z5,z6,z249]),(0,[z0,z1111,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z6,z1112]),(0,[z0,z2,z88,z5,z77,z6]),(0,[z2,z3,z289,z5,z6,z42]),(0,[z357,z0,z2,z5,z77,z6]),(0,[z0,z93,z3,z346,z5,z6]),(0,[z0,z2,z295,z4,z5,z6])],[(1,[z33,z3,z4,z5,z212]),(0,[z0,z1113,z3,z4,z5,z6]),(0,[z3,z85,z4,z5,z42,z10]),(0,[z0,z152,z3,z664,z5,z6]),(0,[z0,z58,z3,z4,z52,z6]),(0,[z0,z1114,z3,z4,z5,z6]),(0,[z0,z1115,z3,z4,z5,z6])],[],[(0,[z2,z3,z4,z5,z6,z853]),(0,[z1116,z2,z3,z4,z5,z6]),(0,[z29,z0,z2,z4,z30,z205]),(0,[z2,z3,z1117,z4,z5,z6]),(0,[z391,z2,z507,z4,z5,z6])]],
   [[(0,[z3,z4,z5,z6,z42,z1118]),(0,[z263,z9,z2,z3,z5,z6]),(0,[z0,z3,z4,z5,z696,z10]),(0,[z0,z3,z61,z5,z6,z10]),(0,[z0,z3,z4,z5,z6,z1119])],[(0,[z9,z2,z3,z4,z5,z135]),(0,[z0,z3,z4,z148,z6,z10]),(0,[z2,z3,z4,z5,z6,z1120]),(0,[z0,z138,z4,z5,z139,z320])],[],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z238,z0,z2,z5,z77,z6]),(0,[z0,z636,z25,z4,z5,z6]),(0,[z0,z451,z236,z4,z5,z6])],[(0,[z241,z2,z3,z4,z5,z212]),(0,[z9,z2,z3,z155,z5,z6]),(0,[z0,z7,z94,z4,z95,z6]),(0,[z128,z96,z2,z4,z227,z6])],[(0,[z1121,z2,z3,z4,z5,z6]),(0,[z24,z0,z707,z4,z5,z6]),(0,[z0,z541,z4,z5,z6,z10]),(0,[z0,z381,z4,z5,z77,z6]),(0,[z376,z2,z3,z4,z30,z6])],[(0,[z0,z1122,z3,z4,z5,z6]),(0,[z109,z9,z2,z47,z3,z6]),(0,[z109,z0,z2,z45,z3,z6]),(0,[z2,z3,z4,z1123,z5,z6])],[(0,[z2,z3,z4,z5,z336,z42]),(0,[z3,z4,z5,z6,z165,z10]),(0,[z0,z302,z3,z289,z5,z6])],[(0,[z37,z373,z3,z15,z5,z6]),(0,[z0,z7,z3,z5,z195,z6])],[(0,[z9,z2,z3,z4,z5,z492]),(0,[z9,z2,z3,z1055,z5,z6]),(0,[z60,z0,z221,z3,z4,z118])],[(0,[z32,z488,z3,z4,z5,z6]),(0,[z0,z7,z3,z5,z257,z6]),(0,[z0,z2,z3,z14,z148,z6]),(0,[z154,z3,z4,z5,z6,z42]),(0,[z24,z325,z191,z4,z5,z6]),(0,[z0,z3,z286,z5,z6,z339])],[(0,[z2,z3,z4,z5,z6,z1124])],[(0,[z124,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1125,z6]),(0,[z0,z2,z236,z4,z285,z6]),(0,[z629,z2,z3,z61,z5,z6])],[(0,[z120,z3,z4,z5,z6,z626]),(0,[z24,z191,z4,z5,z6,z42]),(0,[z838,z3,z4,z5,z6,z42]),(0,[z9,z31,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z554]),(0,[z0,z7,z1100,z4,z5,z6]),(0,[z78,z0,z2,z3,z5,z11])],[(0,[z0,z1126,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1127]),(0,[z2,z3,z5,z840,z6,z42]),(0,[z2,z507,z4,z5,z6,z42]),(0,[z0,z3,z4,z5,z10,z342]),(0,[z78,z0,z2,z3,z610,z11])],[(0,[z0,z2,z3,z1128,z5,z6]),(0,[z373,z3,z4,z5,z6,z42]),(0,[z0,z211,z3,z61,z5,z6])]],
   [[(0,[z143,z2,z3,z4,z8,z6])],[(0,[z0,z7,z3,z54,z5,z6])],[(0,[z0,z203,z141,z4,z5,z6]),(0,[z263,z145,z0,z3,z5,z6]),(0,[z37,z2,z3,z15,z251,z6]),(0,[z0,z3,z4,z5,z6,z1129]),(0,[z356,z3,z4,z5,z6,z10]),(0,[z0,z1130,z3,z4,z5,z6])],[(0,[z96,z2,z3,z4,z5,z6]),(0,[z9,z7,z3,z4,z5,z209]),(0,[z0,z2,z3,z275,z76,z6])],[(0,[z0,z1131,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z567]),(0,[z0,z2,z4,z735,z227,z6])],[(0,[z2,z3,z460,z5,z6,z42]),(1,[z424,z3,z4,z5,z10])],[(0,[z2,z3,z4,z379,z6,z42]),(0,[z0,z7,z3,z289,z5,z6]),(0,[z29,z134,z2,z4,z5,z205])],[(0,[z120,z861,z3,z4,z5,z6]),(0,[z142,z2,z3,z15,z5,z6]),(0,[z60,z3,z4,z5,z42,z10])],[(0,[z241,z186,z4,z5,z6,z10]),(0,[z2,z3,z4,z1132,z5,z6]),(0,[z51,z3,z4,z57,z6,z42])],[(0,[z1133,z0,z2,z3,z5,z6]),(0,[z0,z1134,z3,z4,z5,z6]),(0,[z0,z1135,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z43,z853]),(0,[z0,z2,z280,z5,z76,z6])],[(0,[z0,z3,z4,z5,z6,z1136]),(0,[z0,z203,z3,z217,z5,z6])],[(0,[z32,z521,z3,z4,z5,z6])],[(0,[z3,z546,z4,z5,z42,z10]),(0,[z1137,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1138,z6]),(0,[z0,z2,z3,z285,z6,z11])],[(0,[z0,z2,z3,z1139,z5,z6]),(0,[z3,z4,z5,z43,z42,z10])],[(0,[z0,z440,z3,z4,z5,z135]),(0,[z0,z2,z3,z1140,z5,z6]),(0,[z134,z2,z3,z155,z5,z6]),(0,[z0,z2,z4,z5,z139,z784])]],
   [[(0,[z0,z1141,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z107,z42]),(0,[z355,z3,z4,z5,z42,z10]),(0,[z0,z2,z3,z1142,z5,z6])],[(0,[z0,z2,z3,z4,z1143,z6]),(0,[z0,z1144,z3,z4,z5,z6]),(0,[z9,z2,z3,z5,z195,z6])],[(0,[z1145,z0,z3,z4,z5,z6]),(0,[z101,z0,z3,z4,z57,z6])],[(0,[z51,z0,z3,z4,z5,z212]),(0,[z9,z2,z3,z5,z257,z6]),(0,[z573,z0,z191,z4,z5,z6]),(0,[z1146,z0,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z824,z6]),(0,[z0,z2,z5,z945,z77,z6]),(0,[z0,z2,z3,z346,z5,z220])],[(0,[z0,z2,z3,z1147,z5,z6]),(0,[z745,z2,z3,z4,z5,z6]),(0,[z1148,z2,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z5,z70]),(0,[z1149,z2,z3,z4,z5,z6]),(0,[z1150,z2,z3,z4,z5,z6])],[(0,[z27,z3,z102,z5,z6,z42]),(0,[z3,z4,z5,z209,z42,z10]),(0,[z9,z3,z4,z1099,z5,z6]),(0,[z0,z2,z3,z4,z1151,z6])],[(0,[z120,z3,z366,z4,z5,z6]),(0,[z121,z3,z4,z5,z42,z10]),(0,[z2,z3,z4,z5,z210,z42]),(0,[z0,z3,z4,z5,z6,z1152])],[(0,[z0,z2,z3,z1153,z5,z6]),(0,[z207,z3,z4,z5,z42,z10]),(0,[z0,z3,z4,z792,z5,z6]),(0,[z124,z7,z3,z4,z5,z6]),(0,[z0,z943,z3,z4,z5,z210]),(0,[z629,z2,z3,z184,z5,z6])],[(0,[z2,z3,z4,z5,z416,z42]),(0,[z40,z3,z4,z5,z6,z42]),(0,[z1154,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1155])],[(0,[z493,z3,z4,z5,z42,z10]),(0,[z0,z240,z3,z4,z5,z6]),(0,[z376,z3,z4,z5,z6,z10]),(0,[z0,z1156,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1157])],[(0,[z0,z7,z3,z4,z5,z135]),(0,[z0,z211,z3,z184,z5,z6])],[(0,[z0,z7,z3,z4,z5,z107])],[(0,[z2,z3,z5,z257,z6,z42])],[(0,[z0,z3,z4,z5,z1158,z6])],[(0,[z0,z2,z3,z1159,z5,z6]),(0,[z9,z2,z3,z289,z5,z6]),(0,[z96,z7,z3,z4,z5,z6])]],
   [[(0,[z1160,z2,z3,z4,z5,z6])],[(0,[z32,z0,z280,z4,z5,z6]),(0,[z9,z2,z3,z4,z5,z624]),(0,[z9,z2,z295,z4,z5,z6]),(0,[z2,z3,z4,z5,z1161,z6]),(0,[z29,z0,z2,z155,z5,z205]),(0,[z130,z2,z507,z4,z5,z6])],[(0,[z9,z58,z3,z4,z52,z6]),(0,[z263,z0,z2,z3,z5,z6]),(0,[z2,z3,z1162,z4,z5,z6]),(0,[z605,z2,z295,z4,z5,z6])],[(0,[z2,z3,z4,z218,z5,z6]),(0,[z37,z373,z3,z4,z5,z6]),(0,[z0,z451,z3,z4,z5,z6]),(0,[z0,z2,z155,z5,z6,z205])],[(0,[z120,z3,z4,z194,z5,z6]),(0,[z1163,z2,z3,z4,z5,z6]),(0,[z109,z0,z2,z3,z706,z6]),(0,[z0,z451,z3,z4,z610,z6])],[(0,[z2,z190,z3,z4,z5,z42])],[(0,[z37,z2,z3,z4,z5,z212]),(0,[z0,z3,z366,z317,z5,z6]),(1,[z2,z3,z15,z148,z6]),(0,[z2,z3,z21,z76,z6,z42]),(0,[z0,z3,z4,z5,z210,z10]),(0,[z0,z2,z3,z1164,z5,z6])],[(0,[z110,z0,z3,z4,z5,z848]),(0,[z1165,z0,z7,z3,z5,z6]),(0,[z134,z240,z3,z4,z5,z6])],[(0,[z9,z1,z3,z4,z5,z6]),(0,[z0,z2,z3,z169,z5,z6]),(0,[z121,z2,z3,z140,z5,z6]),(0,[z283,z3,z4,z5,z42,z10]),(0,[z0,z3,z4,z5,z6,z1166]),(0,[z0,z3,z4,z5,z6,z1092]),(0,[z109,z0,z2,z47,z3,z6])],[(0,[z0,z2,z3,z4,z5,z1167]),(0,[z0,z3,z4,z300,z5,z6]),(1,[z3,z4,z5,z42,z10]),(0,[z0,z2,z1168,z4,z5,z6]),(0,[z629,z2,z196,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1169]),(1,[z40,z3,z4,z5,z42])],[(0,[z145,z0,z280,z4,z5,z6]),(0,[z0,z2,z236,z65,z5,z6])],[(0,[z0,z3,z792,z102,z5,z6]),(0,[z20,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z285,z6]),(0,[z0,z211,z196,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1170]),(0,[z3,z325,z4,z5,z6,z10]),(0,[z0,z93,z3,z4,z5,z220]),(0,[z0,z2,z47,z761,z3,z6])],[(0,[z89,z9,z3,z4,z5,z6]),(0,[z0,z198,z41,z5,z6,z10])],[]],
   [[(0,[z3,z4,z5,z197,z6,z42]),(0,[z0,z2,z191,z217,z5,z6]),(0,[z0,z2,z3,z4,z1171,z6]),(0,[z0,z2,z3,z5,z6,z982])],[(0,[z2,z3,z4,z5,z42,z114])],[(0,[z3,z4,z64,z5,z42,z10]),(0,[z0,z2,z3,z1172,z5,z6]),(0,[z378,z0,z191,z4,z5,z6])],[(0,[z3,z21,z4,z5,z42,z10])],[(0,[z51,z0,z3,z4,z304,z6]),(0,[z2,z3,z5,z6,z42,z1173]),(0,[z1174,z2,z3,z4,z5,z6])],[(0,[z145,z448,z3,z4,z5,z6]),(0,[z493,z2,z4,z5,z6,z276]),(0,[z0,z2,z3,z4,z5,z1175]),(0,[z1176,z2,z3,z4,z5,z6]),(0,[z0,z3,z21,z76,z6,z10])],[(0,[z0,z2,z3,z1177,z5,z6]),(0,[z736,z0,z3,z4,z5,z6])],[(0,[z113,z2,z171,z5,z257,z6]),(0,[z0,z3,z4,z5,z705,z10]),(0,[z2,z3,z217,z5,z6,z42]),(0,[z424,z2,z3,z4,z5,z10]),(0,[z0,z3,z4,z285,z6,z10])],[(0,[z0,z2,z3,z4,z1178,z6]),(0,[z3,z4,z180,z5,z6,z10]),(0,[z254,z2,z138,z4,z5,z139])],[(0,[z0,z2,z3,z972,z5,z6]),(0,[z1179,z2,z3,z4,z5,z6]),(0,[z60,z0,z7,z3,z4,z118])],[(0,[z1180,z2,z3,z4,z5,z6]),(0,[z134,z2,z3,z289,z5,z6])],[(0,[z0,z2,z381,z5,z77,z6])],[(0,[z0,z2,z236,z4,z610,z6])],[(0,[z240,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z184,z6,z118])],[(0,[z0,z1181,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z352,z42]),(0,[z51,z3,z4,z5,z42,z10]),(0,[z3,z4,z5,z42,z10,z10]),(0,[z9,z1135,z3,z4,z5,z6]),(0,[z0,z3,z289,z5,z6,z10]),(0,[z0,z154,z3,z4,z5,z210]),(0,[z0,z1182,z3,z4,z5,z6])],[(0,[z121,z2,z3,z4,z148,z6]),(0,[z1183,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z4,z5,z6,z1184])],[(0,[z145,z120,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1185]),(0,[z2,z358,z3,z4,z5,z42]),(0,[z2,z3,z4,z5,z6,z301]),(0,[z103,z2,z3,z4,z5,z43])],[(0,[z444,z2,z3,z15,z5,z6]),(0,[z2,z3,z1186,z4,z5,z6])],[(0,[z124,z3,z191,z4,z5,z6]),(0,[z0,z3,z85,z5,z6,z339]),(0,[z446,z2,z3,z4,z5,z210])],[(0,[z0,z3,z4,z1187,z5,z6]),(0,[z58,z3,z4,z52,z6,z42]),(0,[z58,z3,z4,z5,z42,z10]),(0,[z2,z3,z5,z6,z42,z734]),(0,[z60,z2,z3,z4,z42,z118]),(0,[z2,z3,z4,z5,z1188,z6]),(0,[z0,z3,z5,z1189,z6,z10]),(0,[z160,z0,z2,z4,z227,z6])],[(0,[z0,z3,z4,z5,z321,z10]),(0,[z570,z2,z3,z4,z48,z6]),(0,[z9,z2,z138,z4,z5,z139])],[(0,[z0,z2,z1190,z4,z5,z6]),(0,[z78,z0,z451,z3,z5,z11])],[(0,[z0,z2,z3,z4,z1191,z6]),(0,[z0,z1192,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z1193,z6]),(0,[z1194,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1195]),(0,[z0,z7,z3,z4,z285,z6]),(0,[z0,z2,z3,z4,z5,z1196])],[(0,[z113,z3,z4,z5,z42,z10]),(0,[z0,z3,z4,z1197,z5,z6])],[(0,[z0,z1198,z3,z4,z5,z6]),(0,[z1199,z2,z3,z4,z5,z6]),(0,[z1200,z2,z3,z4,z5,z6])],[(0,[z0,z2,z1201,z4,z5,z6]),(0,[z0,z2,z1202,z4,z5,z6]),(0,[z308,z3,z4,z5,z6,z42]),(0,[z0,z7,z295,z4,z5,z6]),(0,[z1203,z2,z3,z4,z5,z6]),(0,[z1204,z2,z3,z4,z5,z6])],[(0,[z113,z1,z171,z4,z5,z6]),(0,[z0,z3,z4,z5,z406,z10]),(0,[z3,z4,z48,z5,z42,z10]),(0,[z211,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z4,z1205,z6]),(0,[z29,z0,z2,z289,z5,z205]),(0,[z0,z2,z3,z1206,z5,z6])],[(0,[z3,z4,z5,z76,z42,z10]),(0,[z0,z2,z4,z95,z735,z6])],[(0,[z397,z3,z4,z5,z6,z42]),(0,[z127,z3,z4,z5,z42,z10]),(0,[z0,z2,z196,z4,z6,z118])],[(0,[z9,z240,z3,z4,z5,z6]),(0,[z7,z3,z1162,z4,z5,z6])]],
   [[(0,[z0,z358,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z824,z6]),(0,[z7,z3,z4,z218,z5,z6]),(0,[z0,z507,z4,z5,z6,z10]),(0,[z872,z0,z3,z4,z5,z6])],[(0,[z145,z603,z3,z4,z5,z6]),(0,[z2,z574,z4,z5,z6,z652]),(0,[z2,z3,z4,z5,z210,z1009]),(0,[z60,z629,z2,z3,z4,z118])],[(0,[z0,z2,z541,z4,z5,z6]),(0,[z1207,z2,z3,z4,z5,z6]),(0,[z29,z0,z240,z4,z5,z205])],[(0,[z0,z2,z138,z4,z5,z139])],[(0,[z0,z2,z3,z1208,z5,z6]),(0,[z9,z2,z3,z346,z5,z6]),(0,[z1209,z2,z3,z4,z5,z6]),(0,[z263,z0,z58,z3,z52,z6]),(0,[z822,z2,z3,z4,z5,z6]),(0,[z446,z3,z4,z5,z6,z10]),(0,[z1210,z2,z3,z4,z5,z6]),(0,[z0,z31,z507,z4,z5,z6])],[(0,[z32,z649,z3,z4,z5,z6]),(0,[z1211,z2,z3,z4,z5,z6]),(0,[z0,z1212,z3,z4,z5,z6]),(0,[z0,z2,z569,z41,z5,z6])],[(0,[z32,z214,z3,z4,z5,z6]),(0,[z444,z3,z4,z5,z42,z10]),(0,[z0,z152,z3,z479,z5,z6]),(0,[z130,z3,z4,z5,z6,z10]),(0,[z1213,z381,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z831])],[(0,[z0,z2,z3,z4,z1214,z6]),(0,[z0,z3,z460,z5,z6,z10]),(0,[z3,z4,z5,z197,z401,z6]),(0,[z1215,z2,z3,z4,z5,z6]),(0,[z0,z2,z653,z4,z95,z6])],[(0,[z9,z451,z3,z4,z5,z6]),(0,[z0,z3,z4,z379,z6,z10]),(0,[z0,z1216,z3,z4,z5,z6]),(0,[z1217,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1218]),(0,[z2,z236,z4,z5,z6,z42]),(0,[z0,z2,z3,z4,z95,z210]),(1,[z0,z2,z4,z30,z205])],[(0,[z2,z3,z4,z5,z6,z1219])],[(0,[z0,z33,z3,z4,z5,z212]),(0,[z2,z3,z4,z5,z209,z42]),(0,[z204,z0,z3,z4,z5,z10]),(0,[z27,z3,z218,z102,z5,z6]),(0,[z0,z3,z4,z187,z5,z10]),(0,[z7,z3,z4,z5,z6,z249])],[(0,[z440,z3,z4,z5,z6,z42]),(0,[z0,z2,z3,z412,z5,z6]),(0,[z0,z1220,z3,z4,z5,z6])],[(0,[z0,z203,z3,z4,z5,z212]),(0,[z9,z2,z3,z169,z5,z6]),(0,[z2,z3,z4,z5,z421,z42]),(0,[z444,z2,z3,z5,z6,z16]),(0,[z1221,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z227,z205,z118])],[(0,[z9,z3,z4,z300,z5,z6]),(0,[z1222,z2,z3,z4,z5,z6]),(0,[z0,z2,z138,z4,z5,z514])],[(0,[z120,z2,z3,z317,z5,z6]),(0,[z143,z7,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z1223,z6])]],
   [[(0,[z89,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1224,z6]),(0,[z0,z2,z3,z4,z5,z220]),(0,[z0,z2,z3,z4,z379,z6]),(0,[z2,z138,z4,z5,z139,z249])],[(0,[z2,z3,z4,z1225,z5,z6]),(0,[z9,z2,z3,z4,z285,z6]),(0,[z1019,z3,z4,z5,z6,z10]),(0,[z1226,z2,z3,z4,z5,z6]),(0,[z1227,z0,z3,z4,z5,z6]),(0,[z0,z2,z295,z61,z5,z6])],[(0,[z1043,z2,z3,z4,z5,z42]),(0,[z0,z381,z3,z41,z5,z6]),(0,[z0,z2,z3,z346,z5,z6])],[(0,[z0,z1228,z3,z4,z5,z6]),(0,[z1229,z0,z3,z4,z5,z6]),(0,[z0,z2,z280,z102,z5,z6]),(0,[z1194,z7,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1230,z6]),(0,[z0,z3,z4,z5,z6,z1118]),(0,[z2,z3,z4,z5,z6,z1231]),(0,[z29,z376,z2,z4,z5,z205])],[(0,[z2,z3,z5,z195,z6,z42]),(0,[z1232,z2,z3,z4,z5,z6])],[(0,[z0,z2,z1233,z4,z5,z6])],[(0,[z9,z2,z3,z1172,z5,z6]),(0,[z207,z0,z4,z5,z6,z486]),(0,[z391,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z4,z30,z205])],[(0,[z120,z3,z4,z5,z197,z6])],[(0,[z189,z2,z3,z4,z5,z212]),(0,[z483,z2,z3,z14,z5,z6]),(0,[z9,z2,z3,z4,z5,z106]),(0,[z1234,z2,z3,z4,z5,z6])],[(0,[z3,z65,z4,z5,z42,z10]),(0,[z93,z3,z4,z5,z6,z42]),(0,[z376,z2,z3,z155,z5,z6])],[(0,[z109,z0,z2,z229,z3,z6]),(0,[z0,z2,z3,z4,z1235,z6]),(0,[z0,z1236,z3,z4,z5,z6]),(0,[z2,z3,z4,z1237,z5,z6])],[(0,[z1238,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z10,z454]),(0,[z0,z381,z198,z4,z5,z6]),(0,[z0,z2,z3,z4,z1239,z6]),(0,[z0,z2,z3,z4,z610,z6])],[(0,[z0,z2,z3,z1240,z5,z6]),(0,[z145,z3,z4,z687,z5,z6]),(0,[z9,z2,z3,z4,z5,z572]),(0,[z37,z2,z3,z602,z5,z6]),(0,[z422,z3,z4,z5,z6,z42]),(0,[z9,z93,z3,z4,z5,z6]),(0,[z1241,z2,z3,z4,z5,z6]),(0,[z134,z2,z3,z4,z379,z6]),(0,[z0,z302,z3,z4,z379,z6]),(0,[z1242,z2,z3,z4,z5,z6]),(0,[z0,z2,z1243,z4,z5,z6])],[(0,[z2,z3,z4,z5,z70,z42]),(0,[z0,z7,z541,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z301])],[(0,[z2,z3,z14,z672,z5,z6]),(0,[z0,z3,z5,z257,z6,z10]),(0,[z0,z7,z138,z4,z5,z139])]],
   [[(0,[z86,z2,z3,z4,z5,z6]),(0,[z297,z2,z186,z4,z5,z6])],[(0,[z0,z152,z3,z5,z552,z6]),(0,[z0,z2,z4,z5,z945,z6]),(0,[z1244,z2,z3,z4,z5,z6])],[(0,[z0,z2,z1245,z4,z5,z6]),(0,[z1213,z2,z3,z4,z5,z6])],[(0,[z189,z2,z3,z460,z5,z6]),(0,[z0,z1246,z3,z4,z5,z6]),(0,[z1043,z2,z3,z4,z5,z6]),(0,[z424,z3,z4,z5,z6,z10]),(0,[z446,z154,z3,z4,z5,z6]),(0,[z0,z1247,z3,z4,z5,z6])],[(0,[z109,z0,z2,z555,z3,z6])],[(0,[z1248,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z388,z8,z6]),(0,[z0,z3,z366,z5,z257,z6]),(0,[z121,z3,z14,z5,z6,z10]),(0,[z0,z2,z3,z4,z1249,z6]),(0,[z0,z58,z3,z4,z512,z6]),(0,[z3,z4,z5,z6,z368,z10])],[(0,[z2,z3,z4,z1250,z5,z6]),(0,[z2,z3,z4,z5,z6,z1251])],[(0,[z3,z286,z4,z5,z42,z10]),(0,[z0,z7,z3,z412,z5,z6]),(0,[z0,z302,z3,z4,z5,z6])],[(0,[z0,z203,z25,z4,z5,z6]),(0,[z0,z2,z1252,z4,z5,z6])],[(0,[z0,z1253,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1254,z6]),(0,[z0,z2,z3,z4,z857,z6]),(0,[z0,z2,z3,z4,z5,z848]),(0,[z665,z0,z2,z3,z5,z11])],[(1,[z2,z3,z4,z5,z853]),(0,[z0,z93,z3,z4,z5,z6]),(0,[z1255,z0,z2,z3,z5,z6]),(0,[z60,z0,z2,z3,z61,z118])],[(1,[z2,z765,z4,z5,z6]),(0,[z0,z2,z3,z4,z1256,z6]),(0,[z0,z3,z4,z5,z6,z1257]),(0,[z0,z2,z3,z5,z6,z1173]),(0,[z0,z2,z3,z1258,z5,z6]),(0,[z3,z4,z5,z6,z42,z75]),(0,[z0,z7,z3,z4,z5,z220]),(0,[z0,z7,z3,z4,z379,z6]),(0,[z0,z2,z1259,z4,z5,z6])],[(0,[z0,z2,z3,z4,z768,z6]),(0,[z0,z1260,z3,z4,z5,z220]),(0,[z391,z31,z3,z4,z5,z6]),(0,[z78,z130,z2,z3,z5,z11]),(0,[z0,z2,z295,z184,z5,z6])],[(0,[z861,z33,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z5,z349]),(0,[z1261,z0,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z5,z321]),(0,[z0,z7,z3,z346,z5,z6]),(0,[z7,z3,z4,z5,z209,z368]),(0,[z0,z2,z236,z4,z5,z6])],[(0,[z3,z4,z5,z8,z42,z10]),(0,[z759,z0,z2,z4,z5,z6]),(0,[z0,z1262,z3,z4,z5,z6])]],
   [[],[],[(0,[z0,z488,z3,z4,z5,z10]),(0,[z242,z0,z28,z4,z5,z6]),(0,[z0,z154,z3,z54,z5,z6])],[],[(0,[z1263,z2,z3,z4,z5,z6]),(0,[z1264,z2,z3,z4,z5,z6]),(0,[z176,z0,z7,z5,z77,z6])],[(1,[z861,z3,z4,z5,z6]),(0,[z37,z2,z3,z747,z5,z6]),(0,[z0,z3,z4,z5,z6,z1265]),(0,[z0,z3,z1266,z4,z5,z6]),(0,[z2,z3,z4,z1267,z5,z6]),(0,[z1268,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z957,z5,z6])],[(0,[z152,z3,z85,z5,z6,z42]),(0,[z2,z3,z1269,z5,z6,z42])],[(0,[z0,z7,z3,z169,z5,z6]),(0,[z9,z2,z541,z4,z5,z6]),(0,[z1270,z0,z2,z3,z4,z5]),(0,[z0,z2,z761,z3,z4,z6])],[(0,[z7,z3,z4,z5,z209,z42]),(0,[z0,z2,z3,z792,z5,z6]),(0,[z27,z0,z3,z417,z5,z6]),(0,[z0,z7,z3,z4,z610,z6]),(0,[z0,z1260,z3,z4,z5,z6])],[(0,[z0,z2,z3,z433,z76,z6]),(0,[z481,z2,z3,z648,z5,z6]),(0,[z1271,z2,z3,z4,z5,z6]),(0,[z0,z3,z217,z5,z6,z10]),(0,[z0,z2,z3,z1272,z5,z6])],[(0,[z2,z3,z1273,z5,z6,z42]),(0,[z0,z2,z3,z4,z1274,z6]),(0,[z0,z3,z4,z5,z6,z1275])],[(0,[z189,z2,z3,z4,z698,z6]),(0,[z143,z3,z4,z8,z6,z10]),(0,[z60,z9,z2,z3,z4,z118]),(0,[z629,z3,z4,z5,z6,z10]),(0,[z0,z3,z4,z1276,z5,z6])],[(0,[z2,z3,z4,z5,z212,z42]),(0,[z0,z2,z3,z5,z6,z734]),(0,[z51,z0,z3,z4,z125,z6]),(0,[z2,z3,z5,z195,z401,z6]),(0,[z86,z7,z3,z4,z5,z6]),(0,[z29,z0,z7,z4,z5,z205]),(0,[z619,z0,z2,z4,z227,z6])],[(0,[z189,z2,z3,z4,z589,z6]),(0,[z0,z1277,z3,z4,z5,z6]),(0,[z878,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1278])],[(0,[z2,z3,z4,z544,z5,z42]),(0,[z3,z4,z5,z626,z42,z10]),(0,[z291,z0,z2,z5,z77,z6]),(0,[z0,z2,z41,z5,z945,z6])],[(0,[z9,z2,z3,z4,z5,z42]),(0,[z1279,z2,z3,z4,z5,z6]),(0,[z605,z221,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z1280,z4,z5,z6]),(0,[z1281,z2,z3,z4,z5,z6]),(0,[z0,z1282,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1283,z6]),(0,[z9,z2,z3,z412,z5,z6]),(0,[z0,z2,z280,z4,z5,z6]),(0,[z695,z0,z2,z3,z4,z118])],[(0,[z0,z3,z4,z5,z331,z10]),(0,[z0,z381,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1284,z6]),(0,[z254,z2,z3,z4,z5,z6]),(0,[z3,z4,z5,z42,z10,z205]),(0,[z2,z3,z4,z1285,z5,z6])],[(0,[z2,z3,z765,z4,z5,z6])],[(0,[z9,z2,z3,z4,z5,z220]),(0,[z9,z2,z3,z4,z379,z6]),(0,[z1286,z2,z3,z4,z5,z6]),(0,[z0,z3,z5,z6,z10,z1287]),(0,[z0,z2,z3,z54,z5,z210]),(0,[z0,z2,z3,z1288,z5,z6]),(0,[z376,z2,z3,z289,z5,z6])],[(0,[z2,z3,z4,z5,z1289,z6]),(0,[z0,z7,z3,z4,z5,z848]),(0,[z2,z3,z4,z5,z6,z1290]),(0,[z2,z3,z4,z5,z6,z1291])],[(0,[z0,z2,z3,z1292,z5,z6]),(0,[z25,z3,z4,z5,z42,z10]),(0,[z0,z3,z4,z5,z42,z10]),(0,[z0,z2,z3,z5,z6,z1287])],[(0,[z2,z3,z4,z5,z560,z42]),(0,[z0,z40,z3,z4,z5,z42]),(0,[z0,z2,z3,z5,z1189,z6]),(0,[z112,z3,z4,z5,z6,z166])],[(0,[z0,z2,z280,z85,z5,z6]),(0,[z27,z0,z541,z102,z5,z6]),(0,[z0,z3,z1293,z5,z6,z10]),(0,[z1294,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z5,z1295,z6]),(0,[z0,z2,z459,z41,z5,z6]),(0,[z56,z190,z3,z4,z5,z6]),(0,[z0,z7,z236,z4,z5,z6])],[(0,[z32,z33,z3,z4,z5,z212]),(0,[z0,z2,z3,z1296,z5,z6]),(0,[z0,z2,z198,z41,z5,z6]),(0,[z0,z1297,z3,z4,z5,z6])],[(0,[z113,z2,z765,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1298]),(0,[z737,z9,z3,z4,z5,z6]),(0,[z0,z221,z3,z4,z5,z6]),(0,[z1299,z2,z3,z4,z5,z6]),(0,[z1300,z2,z3,z4,z5,z6])],[(0,[z0,z3,z4,z52,z5,z212]),(0,[z0,z947,z3,z4,z5,z6]),(0,[z24,z3,z4,z5,z42,z10]),(0,[z2,z3,z4,z5,z6,z1301]),(0,[z0,z7,z3,z4,z5,z307]),(0,[z291,z0,z3,z102,z5,z6])],[(0,[z0,z2,z3,z1302,z5,z6]),(0,[z0,z2,z3,z155,z30,z6])],[(0,[z2,z3,z155,z5,z6,z42]),(0,[z0,z2,z707,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z1303,z5,z6]),(0,[z1304,z2,z3,z4,z5,z6]),(0,[z239,z3,z4,z5,z6,z10]),(0,[z0,z3,z4,z5,z6,z916])],[(0,[z0,z3,z4,z5,z6,z1305]),(0,[z605,z2,z3,z4,z5,z6]),(0,[z563,z3,z4,z5,z6,z42]),(0,[z9,z2,z3,z4,z610,z6]),(0,[z0,z2,z3,z5,z1306,z6])],[(0,[z2,z171,z765,z4,z5,z6]),(0,[z0,z2,z1307,z4,z5,z6]),(0,[z0,z2,z3,z1273,z5,z6]),(0,[z2,z3,z4,z5,z853,z42])],[(0,[z175,z33,z3,z4,z5,z6]),(0,[z207,z0,z191,z4,z5,z6])],[(0,[z0,z1308,z3,z4,z5,z6]),(0,[z3,z4,z5,z42,z10,z276]),(0,[z1309,z2,z3,z4,z5,z6])],[(0,[z78,z0,z2,z3,z5,z982])],[(0,[z629,z211,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z1310])],[(0,[z0,z120,z3,z4,z5,z212]),(0,[z0,z3,z4,z5,z6,z1311]),(0,[z3,z4,z5,z208,z42,z10]),(0,[z1312,z2,z3,z4,z5,z6]),(0,[z0,z2,z1313,z4,z5,z6])],[(0,[z640,z0,z2,z5,z77,z6])],[],[(0,[z99,z33,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1314,z6]),(0,[z1315,z2,z3,z4,z5,z6]),(0,[z0,z236,z4,z5,z6,z10]),(0,[z1165,z0,z2,z3,z5,z6]),(0,[z1316,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1317,z6]),(0,[z0,z2,z3,z1318,z5,z6]),(0,[z9,z397,z3,z4,z5,z6]),(0,[z3,z4,z52,z5,z42,z10]),(0,[z176,z0,z308,z5,z77,z6]),(0,[z0,z3,z4,z5,z6,z1319])],[(0,[z283,z2,z3,z4,z5,z212]),(0,[z0,z3,z4,z5,z6,z75]),(0,[z248,z2,z3,z4,z5,z6]),(0,[z9,z302,z3,z4,z5,z6]),(0,[z0,z191,z102,z5,z77,z6]),(0,[z0,z7,z280,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1320]),(0,[z0,z1321,z3,z4,z5,z6]),(0,[z0,z1322,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z3,z4,z5,z57,z42,z10]),(0,[z9,z203,z25,z4,z5,z6]),(0,[z617,z0,z191,z4,z5,z6]),(0,[z58,z3,z4,z52,z401,z6]),(0,[z0,z1323,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1324]),(0,[z0,z2,z3,z1325,z5,z6]),(0,[z39,z2,z3,z4,z5,z42]),(0,[z3,z4,z5,z42,z10,z84]),(0,[z124,z2,z3,z5,z77,z6]),(0,[z254,z7,z3,z4,z5,z6]),(0,[z130,z31,z3,z4,z5,z6]),(0,[z0,z451,z507,z4,z5,z6])]],
   [[(0,[z0,z3,z85,z4,z5,z212]),(0,[z2,z3,z4,z5,z42,z494]),(0,[z2,z295,z4,z5,z6,z42]),(0,[z0,z2,z847,z4,z5,z6])],[(0,[z0,z2,z1326,z4,z5,z6]),(0,[z1327,z2,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z1256,z6])],[(0,[z561,z0,z3,z4,z5,z10])],[(0,[z0,z2,z3,z1269,z5,z6]),(0,[z0,z2,z3,z460,z48,z6]),(0,[z9,z2,z236,z4,z5,z6]),(0,[z96,z2,z3,z4,z5,z210])],[(0,[z0,z1328,z3,z4,z5,z6]),(0,[z0,z2,z441,z41,z5,z6]),(0,[z0,z3,z4,z1329,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1330]),(0,[z0,z2,z3,z1331,z5,z6]),(0,[z0,z2,z3,z4,z1332,z6]),(1,[z2,z3,z180,z76,z6])],[(0,[z2,z3,z14,z5,z6,z172]),(0,[z3,z4,z5,z212,z42,z10]),(0,[z0,z203,z449,z4,z5,z6]),(0,[z424,z2,z3,z4,z5,z209]),(0,[z0,z424,z3,z4,z5,z10]),(0,[z0,z3,z4,z5,z6,z848]),(0,[z103,z3,z4,z5,z6,z10])],[(0,[z0,z3,z5,z195,z6,z10]),(0,[z0,z7,z198,z41,z5,z6])],[(0,[z0,z603,z3,z4,z5,z212]),(0,[z0,z2,z3,z1333,z5,z6]),(0,[z0,z2,z3,z1334,z5,z6]),(0,[z0,z2,z507,z4,z285,z6]),(0,[z0,z1335,z3,z4,z5,z6])],[(0,[z0,z1336,z3,z4,z5,z6]),(0,[z520,z2,z361,z4,z5,z6]),(0,[z0,z2,z3,z1293,z5,z6])],[(0,[z0,z397,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1337])],[(0,[z134,z2,z3,z4,z5,z6]),(0,[z39,z397,z3,z4,z5,z42]),(0,[z267,z2,z3,z4,z268,z6]),(0,[z112,z383,z3,z4,z5,z6])],[(0,[z0,z1338,z3,z4,z5,z6]),(0,[z0,z2,z761,z3,z21,z6])],[(0,[z673,z2,z3,z4,z8,z6]),(0,[z124,z3,z4,z5,z6,z10]),(0,[z112,z3,z4,z5,z6,z10]),(0,[z0,z7,z3,z5,z1306,z6]),(0,[z605,z7,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z220,z804]),(0,[z60,z0,z2,z3,z4,z118])],[(0,[z0,z440,z3,z4,z5,z6]),(0,[z0,z2,z3,z1339,z5,z6]),(0,[z2,z280,z4,z5,z6,z42]),(0,[z0,z2,z761,z3,z76,z6])],[(0,[z0,z2,z3,z4,z148,z6]),(0,[z2,z3,z184,z5,z6,z42])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 501) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 501).take 502) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1003).take 434) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1437)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [501, 502, 434] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 91).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 186).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 278).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 386).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 493).take 19).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [91, 95, 92, 108, 107, 19] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

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

end PEqualNP.Outside.L_meta_36356

theorem PEqualNP.Outside.L_meta_36356 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4274585224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4274585224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36356.solve
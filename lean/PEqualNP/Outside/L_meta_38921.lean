import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38921

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
  Nat.testBit (4276809440 * 2 ^ 32 + 4242596064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0010d98718e2318a#64 ++ 0x20021b30e31c4631#64 ++ 0x9033fb8f38e2739f#64 ++ 0xd2067f71e71c4e73#64 : BitVec 256),
   (0x0045c1b1406e94a4#64 ++ 0x4008b836280dd294#64 ++ 0xf8cdc5f1c0ff9ce7#64 ++ 0xbf19b8be381ff39c#64 : BitVec 256),
   (0x030a0600a3014a50#64 ++ 0x806140c01460294a#64 ++ 0xcf0e0601ff03ffff#64 ++ 0x79e1c0c03fe07fff#64 : BitVec 256),
   (0x0db006da0db41f07#64 ++ 0x01b600db41b683e0#64 ++ 0xfff007fe0ffc1f06#64 ++ 0xfffe00ffc1ff83e0#64 : BitVec 256),
   (0x26ff68000edbe000#64 ++ 0x04dfed0001db7c00#64 ++ 0xaffff8000fffe005#64 ++ 0xf5ffff0001fffc00#64 : BitVec 256),
   (0x17efb76df0000000#64 ++ 0x02fdf6edbe000000#64 ++ 0xf7fffffff0000003#64 ++ 0xfefffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 3]⟩, ⟨.and, [10, 4]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x9033fb8f38e2739f 0xd2067f71e71c4e73

def z1 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8cdc5f1c0ff9ce7 0xbf19b8be381ff39c

def z2 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0xcf0e0601ff03ffff 0x79e1c0c03fe07fff

def z3 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff007fe0ffc1f06 0xfffe00ffc1ff83e0

def z4 : W := mkw 0x0db0c7db0df61f87 0x01b618fb61bec3f0 0xfff1c7ff0ffe1f87 0xfffe38ffe1ffc3f0

def z5 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fffffff0000003 0xfefffffffe000000

def z6 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffff8000fffe005 0xf5ffff0001fffc00

def z7 : W := mkw 0x0000d90510422088 0x20001b20a2084411 0x0003f80130026099 0x00007f0026004c13

def z8 : W := mkw 0x0db0dfdf1df63f8f 0x21b61bfbe3bec7f1 0xfff3ffff3ffe7f9f 0xfffe7fffe7ffcff3

def z9 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x30c1c1f000fc0000 0x8618383e001f8000

def z10 : W := mkw 0x130a976df3014a50 0x826152edbe60294a 0xdf0e07ffff03ffff 0x7be1c0ffffe07fff

def z11 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0xcf0e0601f7018c63 0x79e1c0c03ee0318c

def z12 : W := mkw 0x0010488208e2318a 0x20020910411c4631 0x0000000008e2739c 0x00000000011c4e73

def z13 : W := mkw 0x0045812140000000 0x0008b02428000000 0xf0cdc5f1c0000003 0xbe19b8be38000000

def z14 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x070202003f006318 0x40e0404007e00c63

def z15 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0x30f1f9fe00000000 0x861e3f3fc0000000

def z16 : W := mkw 0x0045c121404a80a0 0x4008b82428095014 0x000dc001c00380e1 0x0001b8003800701c

def z17 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xfffffffff7018c63 0xfffffffffee0318c

def z18 : W := mkw 0x004540b0406e94a4 0x4008a816080dd294 0x68cc0470c0ff9ce4 0x2d19808e181ff39c

def z19 : W := mkw 0x0000c1b1406614a4 0x40001836280cc294 0xd001c5f1c0e21ce7 0x9a0038be381c439c

def z20 : W := mkw 0x0000000003014a50 0x800000000060294a 0x080000000f03fffc 0x0100000001e07fff

def z21 : W := mkw 0x020a000002014000 0x0041400000402800 0x8f0e00000f03e005 0x71e1c00001e07c00

def z22 : W := mkw 0x27ff6e00afdbea50 0x84ffedc015fb7d4a 0xeffffe01ffffffff 0xfdffffc03fffffff

def z23 : W := mkw 0x0010488208e2318a 0x20020910411c4631 0x9030038e08e2739e 0xd2060071c11c4e73

def z24 : W := mkw 0x37efff6df24be000 0x06fdffedbe497c00 0xf7fffffff003e003 0xfefffffffe007c00

def z25 : W := mkw 0x00450030400c8424 0x4008a00608019084 0x68cc0470c01d8c60 0x2d19808e1803b18c

def z26 : W := mkw 0x26ba28000e916000 0x04d7450001d22c00 0x073238000f006000 0x40e6470001e00c00

def z27 : W := mkw 0x0000009000241404 0x0000001200048280 0xf8c005f000fc1c06 0xbf1800be001f8380

def z28 : W := mkw 0x0df5c7fb4dfe9fa7 0x41beb8ff69bfd3f4 0xfffdc7ffcfff9fe7 0xffffb8fff9fff3fc

def z29 : W := mkw 0x00450030400c8424 0x4008a00608019084 0x20c00070001c0000 0x0418000e00038000

def z30 : W := mkw 0x030a0600a0000000 0x006140c014000000 0xc70e0601f0000003 0x78e1c0c03e000000

def z31 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xffffffffff03ffff 0xffffffffffe07fff

def z32 : W := mkw 0x030a0600a2014000 0x006140c014402800 0xcf0e0601ff03e007 0x79e1c0c03fe07c00

def z33 : W := mkw 0x001018061880210a 0x20020300c3100421 0x00323a0e38006318 0x40064741c7000c63

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0xc80c0401c0039ce7 0x390180803800739c

def z35 : W := mkw 0x024fc1b1426fd4a4 0x4049f836284dfa94 0xffcfc5f1cffffce7 0xfff9f8be39ffff9c

def z36 : W := mkw 0x1db097fffdb41f07 0x03b612ffffb683e0 0xfff007fffffc1f06 0xfffe00ffffff83e0

def z37 : W := mkw 0x201048000edbe000 0x0402090001db7c00 0x8833f8000fffe005 0xd1067f0001fffc00

def z38 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xf7ffffffff00631b 0xfeffffffffe00c63

def z39 : W := mkw 0x1145d7fdf06e94a4 0x4228baffbe0dd294 0xf8cdc7fff0ff9ce7 0xbf19b8fffe1ff39c

def z40 : W := mkw 0x17ef366cf0000000 0x02fde6cd9e000000 0x67fe3e7ef0000000 0x6cffc7cfde000000

def z41 : W := mkw 0x035fdfb7fbeffffe 0xe06bfbf6ff7dffff 0xffffffffffffffff 0xffffffffffffffff

def z42 : W := mkw 0x14f5f9ef58e2318a 0x229ebf3deb1c4631 0xb0f3fbff38e2739f 0xd61e7f7fe71c4e73

def z43 : W := mkw 0x04b000000c900000 0x0096000001920000 0xaff000000ffc0004 0xf5fe000001ff8000

def z44 : W := mkw 0x06ef200000000000 0x00dde40000000000 0xa7fff80000000001 0xf4ffff0000000000

def z45 : W := mkw 0x034fc7b1e36fdef4 0xc069f8f63c6dfbde 0xffcdc5f1c7ff9ce7 0xbff9b8be38fff39c

def z46 : W := mkw 0x0900065801040e05 0x012000cb002081c0 0x4000047000000c00 0x0800008e00000180

def z47 : W := mkw 0x17ffff6df8c22000 0x02ffffedbf184400 0xf7fffffff8e26007 0xfeffffffff1c4c00

def z48 : W := mkw 0x04b0d9871cf2318a 0x20961b30e39e4631 0xbff3fb8f3ffe739f 0xf7fe7f71e7ffce73

def z49 : W := mkw 0x201048000edbe000 0x0402090001db7c00 0x080000000fffe004 0x0100000001fffc00

def z50 : W := mkw 0x0000c18100621080 0x00001830200c4210 0x9001c18100e21087 0x92003830201c4210

def z51 : W := mkw 0x0055d9b758eeb5ae 0x600abb36eb1dd6b5 0xf8fffffff8ffffff 0xff1fffffff1fffff

def z52 : W := mkw 0x0010008208a01102 0x0002001041140220 0x9030038e08e01306 0xd2060071c11c0260

def z53 : W := mkw 0x0da0065805140e05 0x01b400cb00a281c0 0x6fc00470071c0c00 0x2df8008e00e38180

def z54 : W := mkw 0x17ef2668e0000000 0x02fde4cd1c000000 0x67cc0470c0000000 0x2cf9808e18000000

def z55 : W := mkw 0x030a4690a36fdef4 0xc06148d2146dfbde 0xcf0e0601ffffffff 0x79e1c0c03fffffff

def z56 : W := mkw 0x26ffe9b14efff4a4 0x44dffd3629dffe94 0xfffffdf1cffffce7 0xffffffbe39ffff9c

def z57 : W := mkw 0x01000600a0000000 0x002000c014000000 0x40000601f0000002 0x080000c03e000000

def z58 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xb8cdc1f000ff8005 0xb719b83e001ff000

def z59 : W := mkw 0x0045d9b5506eb4ac 0x6008bb36aa0dd695 0xf8cffdf1f0fffcff 0xbf19ffbe3e1fff9f

def z60 : W := mkw 0x26ef20000619c000 0x04dde40000c33800 0x2fcc0000071d8000 0x25f9800000e3b000

def z61 : W := mkw 0x0010008208a01102 0x0002001041140220 0x9032038f38e2739f 0xd2064071e71c4e73

def z62 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x77fdfdfec0000000 0xaeffbfbfd8000000

def z63 : W := mkw 0x0000910510000000 0x00001220a2000000 0x9033fb8f30000003 0xd2067f71e6000000

def z64 : W := mkw 0x0de50678451c8e25 0x41bca0cf08a391c4 0x6fcc0470c71d8c60 0x2df9808e18e3b18c

def z65 : W := mkw 0x124fb125f0000000 0x0249f624be000000 0xf0cffdf1f0000003 0xbe19ffbe3e000000

def z66 : W := mkw 0x17baffcfb8e2318a 0x22f75ff9f71c4631 0x9733fb8f38e2739f 0xd2e67f71e71c4e73

def z67 : W := mkw 0x27ff6e00aedbe000 0x04ffedc015db7c00 0xeffffe01ffffe007 0xfdffffc03ffffc00

def z68 : W := mkw 0x24f568000cdaa000 0x049ead00019b5400 0x20f1f80000fc0000 0x841e3f00001f8000

def z69 : W := mkw 0x17fffffff8eeb5ae 0x62ffffffff1dd6b5 0xfffffffff8ffffff 0xffffffffff1fffff

def z70 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0xd83fff8ff8e3ffff 0xfb07fff1ff1c7fff

def z71 : W := mkw 0x26ff68304edfe424 0x44dfed0609dbfc84 0xeffffc70cfffec65 0xfdffff8e19fffd8c

def z72 : W := mkw 0x27ff6e00afdbea50 0x84ffedc015fb7d4a 0xaffffa003fffe31d 0xf5ffff4007fffc63

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0x800202013802739f 0x5000404027004e73

def z74 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x4f0c0400c7018c60 0x29e1808018e0318c

def z75 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffffa013ffff39f 0xf5ffff4027fffe73

def z76 : W := mkw 0x000091871020118a 0x20001230e2040231 0x1000018e00000000 0x02000031c0000000

def z77 : W := mkw 0x030a0600a0000000 0x006140c014000000 0x470c0400c0000000 0x28e1808018000000

def z78 : W := mkw 0x14a0304c10000000 0x0294060982000000 0x0030380e00000000 0x00060701c0000000

def z79 : W := mkw 0x024f200000000000 0x0049e40000000000 0x000ff80000000001 0x0001ff0000000000

def z80 : W := mkw 0x0010d90518c22088 0x20021b20a3184411 0x8033f80138e2609d 0xd0067f00271c4c13

def z81 : W := mkw 0x034fc7b1e36fdef4 0xc069f8f63c6dfbde 0xffcfc7f1ffffffff 0xfff9f8fe3fffffff

def z82 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x6fc004700ffc1f04 0x2df8008e01ff83e0

def z83 : W := mkw 0x081000920db41f07 0x0102001241b683e0 0x9830038e0ffc1f06 0xd3060071c1ff83e0

def z84 : W := mkw 0x0010480008c22000 0x0002090001184400 0x8033f80008e26005 0xd0067f00011c4c00

def z85 : W := mkw 0x0000c18100621080 0x00001830200c4210 0x9003c38138e2739f 0xd2007870271c4e73

def z86 : W := mkw 0x0db0064a0d900b03 0x01b600c941b20160 0x0730020e0f000300 0x40e60041c1e00060

def z87 : W := mkw 0x17aa364cb0000000 0x02f546c996000000 0xf7f23ffe30000002 0xfefe47ffc6000000

def z88 : W := mkw 0x37ef2668e619c000 0x06fde4cd1cc33800 0x6fcc0470c71d8000 0x2df9808e18e3b000

def z89 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x1031f98e00e00000 0x82063f31c01c0000

def z90 : W := mkw 0x0fba06daafb55f57 0x81f740db55f6abea 0xfffc07fecffd9f66 0xffff80ffd9ffb3ec

def z91 : W := mkw 0x26efe1b1467fd4a4 0x44ddfc3628cffa94 0xffcdc5f1c7ff9ce7 0xbff9b8be38fff39c

def z92 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x1033fb8e38e06318 0xc2067f71c71c0c63

def z93 : W := mkw 0x030a87b1e3255ef4 0xc06150f63c64abde 0xdf0e07f1ff03ffff 0x7be1c0fe3fe07fff

def z94 : W := mkw 0x0000910510000000 0x00001220a2000000 0x9033fb8f3802739f 0xd2067f71e7004e73

def z95 : W := mkw 0x1cf5b1ff5cb41507 0x039eb63feb9682a0 0x30f1f9fe00fc0000 0x861e3f3fc01f8000

def z96 : W := mkw 0x081000920db41f07 0x0102001241b683e0 0x080000000ffc1f04 0x0100000001ff83e0

def z97 : W := mkw 0x124fb125f0000000 0x0249f624be000000 0x000ff801f0000001 0x0001ff003e000000

def z98 : W := mkw 0x26ef6000065bc000 0x04ddec0000cb7800 0xafcdc00007ff8005 0xb5f9b80000fff000

def z99 : W := mkw 0x0db04eda0df63f07 0x01b609db41bec7e0 0xfff3fffe0ffe7f07 0xfffe7fffc1ffcfe0

def z100 : W := mkw 0x37ff7e4cbedbe000 0x06ffefc997db7c00 0xaffffa0e3fffe005 0xf5ffff41c7fffc00

def z101 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fffffff802739f 0xfeffffffff004e73

def z102 : W := mkw 0x01009787b1201bda 0xa02012f0f624037b 0x5000078ff0001ffa 0x0a0000f1fe0003ff

def z103 : W := mkw 0x0db01e4e1d902b0b 0x21b603c9c3b20561 0x07323a0e3f006318 0x40e64741c7e00c63

def z104 : W := mkw 0x26baf9871ef3718a 0x24d75f30e3de6e31 0x9733fb8f3fe2739f 0xd2e67f71e7fc4e73

def z105 : W := mkw 0x0000008200201102 0x0000001040040220 0x1000038e00001302 0x02000071c0000260

def z106 : W := mkw 0x06ef6000004a8000 0x00ddec0000095000 0xaffff80000ff8005 0xf5ffff00001ff000

def z107 : W := mkw 0x0010480008c22000 0x0002090001184400 0x8033fa0138e2739f 0xd0067f40271c4e73

def z108 : W := mkw 0x0cb000da0cb41507 0x0196001b419682a0 0xbff001fe0ffc0004 0xf7fe003fc1ff8000

def z109 : W := mkw 0x17ffbf6ff880210a 0x22fff7edff100421 0xf7fffffff800631b 0xfeffffffff000c63

def z110 : W := mkw 0x0da006da05341f07 0x01b400db40a683e0 0x7fc007fe071c1f02 0x2ff800ffc0e383e0

def z111 : W := mkw 0x024f4000024bc000 0x0049e80000497800 0xafcfc0000fffe005 0xf5f9f80001fffc00

def z112 : W := mkw 0x17ef364cb0000000 0x02fde6c996000000 0xa7fffa0e30000001 0xf4ffff41c6000000

def z113 : W := mkw 0x0100060000000000 0x002000c000000000 0xc700060000000002 0x78e000c000000000

def z114 : W := mkw 0x0145c7b1e16e9ef4 0xc028b8f63c2dd3de 0xf8cdc7f1f0ff9fff 0xbf19b8fe3e1ff3ff

def z115 : W := mkw 0x17ffffeff8e2318a 0x22fffffdff1c4631 0xf7fffffff8e2739f 0xfeffffffff1c4e73

def z116 : W := mkw 0x0000d90510422088 0x20001b20a2084411 0x0001f80000000000 0x00003f0000000000

def z117 : W := mkw 0x04b048000cd22000 0x00960900019a4400 0xaff3f8000ffe6005 0xf5fe7f0001ffcc00

def z118 : W := mkw 0x05e5876940000000 0x00bcb0ed28000000 0xf7fdc7ffc0000003 0xfeffb8fff8000000

def z119 : W := mkw 0x11000668e0000000 0x022000cd1c000000 0x40000470c0000000 0x0800008e18000000

def z120 : W := mkw 0x0100060001000a00 0x002000c000200140 0x4f00040007000c00 0x29e0008000e00180

def z121 : W := mkw 0x26ba28000e916000 0x04d7450001d22c00 0x8f3e38000f03e005 0x71e7c70001e07c00

def z122 : W := mkw 0x07ef264800000000 0x00fde4c900000000 0xf7fffffe00000003 0xfeffffffc0000000

def z123 : W := mkw 0x0045c121404a80a0 0x4008b82428095014 0xa8cdc001c0ff80e5 0xb519b800381ff01c

def z124 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8cfc7f1f8ffffff 0xff19f8fe3f1fffff

def z125 : W := mkw 0x021a48000ac36000 0x0043490001586c00 0x8f3ff8000fe3e005 0xf1e7ff0001fc7c00

def z126 : W := mkw 0x0cb0d9df1cf6358f 0x21961b3be39ec6b1 0x30f1f9fe00fc0000 0x861e3f3fc01f8000

def z127 : W := mkw 0x020a0000a2014050 0x804140001440280a 0x000e0001f003e0f9 0x0001c0003e007c1f

def z128 : W := mkw 0x0cb000da0cb41507 0x0196001b419682a0 0x30f001fe00fc0000 0x861e003fc01f8000

def z129 : W := mkw 0x324ff925f24be000 0x0649ff24be497c00 0x000ff801f003e001 0x0001ff003e007c00

def z130 : W := mkw 0x0045c131404e84a4 0x4008b8262809d094 0x68cdc471c01f8ce1 0x2d19b88e3803f19c

def z131 : W := mkw 0x224f6800024be000 0x0449ed0000497c00 0x000ff8000003e001 0x0001ff0000007c00

def z132 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0xb0f3fbff30000003 0xd61e7f7fe6000000

def z133 : W := mkw 0x26fff9051edbe088 0x24dfff20a3db7c11 0xaffff8013fffe09d 0xf5ffff0027fffc13

def z134 : W := mkw 0x0da0065805140e05 0x01b400cb00a281c0 0xfff007fe071c0c02 0xfffe00ffc0e38180

def z135 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0xf0fdfdffc0000003 0xbe1fbfbff8000000

def z136 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0c005f000000002 0xbe1800be00000000

def z137 : W := mkw 0x17aa364cb3014a50 0x82f546c99660294a 0xcf3e3e0fff03ffff 0x79e7c7c1ffe07fff

def z138 : W := mkw 0x0100060001000a00 0x002000c000200140 0xcf0006000f001f06 0x79e000c001e003e0

def z139 : W := mkw 0x124fb125f2014050 0x8249f624be40280a 0x000ff801f003e0f9 0x0001ff003e007c1f

def z140 : W := mkw 0x00004090006e94a4 0x40000812000dd294 0x0800000000ff9ce4 0x01000000001ff39c

def z141 : W := mkw 0x17aa364cb0000000 0x02f546c996000000 0x07323a0e30000000 0x40e64741c6000000

def z142 : W := mkw 0x05b006ca08a01102 0x00b600d941140220 0xf7f007fe08e01306 0xfefe00ffc11c0260

def z143 : W := mkw 0x000091871020118a 0x20001230e2040231 0x1000038f3000139a 0x02000071e6000273

def z144 : W := mkw 0x0045d1b7506e95ae 0x6008ba36ea0dd2b5 0xf8cdc7fff0ff9fff 0xbf19b8fffe1ff3ff

def z145 : W := mkw 0x0fba06daafb55f57 0x81f740db55f6abea 0xfffe07ffffffffff 0xffffc0ffffffffff

def z146 : W := mkw 0x01000600a1000a50 0x802000c01420014a 0x40000601f0001ffa 0x080000c03e0003ff

def z147 : W := mkw 0x06ff20000c900000 0x00dfe40001920000 0xaffff8000ffc0005 0xf5ffff0001ff8000

def z148 : W := mkw 0x1fffb7fffdb41f07 0x03fff6ffffb683e0 0xfffffffffffc1f07 0xffffffffffff83e0

def z149 : W := mkw 0x004500b0402c9424 0x4008a01608059284 0xf8cc05f0c0fd9c66 0xbf1980be181fb38c

def z150 : W := mkw 0x0000910510000000 0x00001220a2000000 0x0003f80130000001 0x00007f0026000000

def z151 : W := mkw 0x0010488208e2318a 0x20020910411c4631 0x8002020138e2739f 0x50004040271c4e73

def z152 : W := mkw 0x090006da01241f07 0x012000db402483e0 0x500007fe00001f02 0x0a0000ffc00003e0

def z153 : W := mkw 0x0855c1b34dfe9fa7 0x410ab83669bfd3f4 0xf8cdc5f1cfff9fe7 0xbf19b8be39fff3fc

def z154 : W := mkw 0x120a3004b0000000 0x0241460096000000 0x0002380030000000 0x0000470006000000

def z155 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x0f30020e0ffc1f04 0x41e60041c1ff83e0

def z156 : W := mkw 0x001099071880210a 0x20021320e3100421 0x9033fb8f3800631b 0xd2067f71e7000c63

def z157 : W := mkw 0x16efb125f0000000 0x02ddf624be000000 0xa7fff801f0000001 0xf4ffff003e000000

def z158 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xfffffffff0039ce7 0xfffffffffe00739c

def z159 : W := mkw 0x17efb76df2014000 0x02fdf6edbe402800 0xffffffffff03e007 0xffffffffffe07c00

def z160 : W := mkw 0x26ffe9b14efff4a4 0x44dffd3629dffe94 0xbffff9f00fffe005 0xf7ffff3e01fffc00

def z161 : W := mkw 0x24f568000cdaa000 0x049ead00019b5400 0xa8fdf80000ff8005 0xb51fbf00001ff000

def z162 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x4f0c0601f7019ffa 0x29e180c03ee033ff

def z163 : W := mkw 0x37ffff6dfcdaa000 0x06ffffedbf9b5400 0xf7fffffff0fc0003 0xfefffffffe1f8000

def z164 : W := mkw 0x2eff68920fffff07 0x05dfed1241ffffe0 0xaffff8000fffff05 0xf5ffff0001ffffe0

def z165 : W := mkw 0x134fb76df0000000 0x0269f6edbe000000 0x500ffffff0000003 0x0a01fffffe000000

def z166 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x78cdc5f0c0fd8c60 0xaf19b8be181fb18c

def z167 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0xcf0c0600cf019f66 0x79e180c019e033ec

def z168 : W := mkw 0x1100976df0000000 0x022012edbe000000 0xd033fffff0000003 0xda067ffffe000000

def z169 : W := mkw 0x06efa12140000000 0x00ddf42428000000 0xf7fffdf1c0000003 0xfeffffbe38000000

def z170 : W := mkw 0x031adf87bbe37bda 0xa0635bf0f77c6f7b 0xdf3fff8fffe3ffff 0xfbe7fff1fffc7fff

def z171 : W := mkw 0x17aa364cb3014a50 0x82f546c99660294a 0x07323a0e3f006318 0x40e64741c7e00c63

def z172 : W := mkw 0x0b0a06daa3255f57 0x816140db5464abea 0xdf0e07ffff03ffff 0x7be1c0ffffe07fff

def z173 : W := mkw 0x24b048000edbe000 0x0496090001db7c00 0xaff000000fffe004 0xf5fe000001fffc00

def z174 : W := mkw 0x1100976df0000000 0x022012edbe000000 0x500007fff0000002 0x0a0000fffe000000

def z175 : W := mkw 0x000091871020118a 0x20001230e2040231 0x9033fb8f3000139b 0xd2067f71e6000273

def z176 : W := mkw 0x0000000003014a50 0x800000000060294a 0x880202013f03ffff 0x5100404027e07fff

def z177 : W := mkw 0x1ffff7fffdfe9fa7 0x43fffeffffbfd3f4 0xffffffffffff9fe7 0xfffffffffffff3fc

def z178 : W := mkw 0x0010998718a0318a 0x20021330e3140631 0x10323b8f3800739a 0x42064771e7000e73

def z179 : W := mkw 0x37ffbf6dfe916000 0x06fff7edbfd22c00 0xf7ffffffff006003 0xfeffffffffe00c00

def z180 : W := mkw 0x17efb76df1000a50 0x82fdf6edbe20014a 0xf7fffffff0001ffb 0xfefffffffe0003ff

def z181 : W := mkw 0x0000c10100420080 0x0000182020084010 0x0001c00100020081 0x0000380020004010

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x0002020038006318 0x4000404007000c63

def z183 : W := mkw 0x0faa0658a7154e55 0x81f540cb14e2a9ca 0xefce0671ff1fffff 0x7df9c0ce3fe3ffff

def z184 : W := mkw 0x1fba36debdb41f07 0x03f746dbd7b683e0 0xfff23ffe3ffc1f06 0xfffe47ffc7ff83e0

def z185 : W := mkw 0x2055c9b14efff4a4 0x440ab93629dffe94 0xf8cdc5f1cffffce7 0xbf19b8be39ffff9c

def z186 : W := mkw 0x081048920df63f8f 0x2102091241bec7f1 0x080000000ffe7f9c 0x0100000001ffcff3

def z187 : W := mkw 0x090097df11241f8f 0x212012fbe22483f1 0x500007ff30001f9a 0x0a0000ffe60003f3

def z188 : W := mkw 0x04b000820cb01102 0x0096001041960220 0xbff0038e0ffc1306 0xf7fe0071c1ff8260

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x880c000000038005 0x3101800000007000

def z190 : W := mkw 0x04b000000c900000 0x0096000001920000 0x073000000f000000 0x40e6000001e00000

def z191 : W := mkw 0x205548000edbe000 0x040aa90001db7c00 0xa8cdc0000fffe005 0xb519b80001fffc00

def z192 : W := mkw 0x01000600a1000a50 0x802000c01420014a 0xc80c0601f0039fff 0x390180c03e0073ff

def z193 : W := mkw 0x27ff6e000fdbea00 0x04ffedc001fb7d40 0xeffffe000fffff07 0xfdffffc001ffffe0

def z194 : W := mkw 0x020a0000a0000000 0x0041400014000000 0x000e0001f0000001 0x0001c0003e000000

def z195 : W := mkw 0x24f568000cdaa000 0x049ead00019b5400 0xaff1f8000ffc0004 0xf5fe3f0001ff8000

def z196 : W := mkw 0x0010918718a0118a 0x20021230e3140231 0x9030038f38e0139e 0xd2060071e71c0273

def z197 : W := mkw 0x0000c1b1406e94a4 0x40001836280dd294 0x580005f1c0ff9ce6 0x0b0000be381ff39c

def z198 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x4f0e0600ff01ef78 0x69e1c0c01fe03def

def z199 : W := mkw 0x0000c19100661484 0x00001832200cc290 0xf8c1c5f100fe1c87 0xbf1838be201fc390

def z200 : W := mkw 0x0000910510000000 0x00001220a2000000 0x1031f98e00000000 0x82063f31c0000000

def z201 : W := mkw 0x26ef6800065be000 0x04dded0000cb7c00 0x2fcff800071fe001 0x25f9ff0000e3fc00

def z202 : W := mkw 0x17eff76df04a80a0 0x42fdfeedbe095014 0xf7fffffff00380e3 0xfefffffffe00701c

def z203 : W := mkw 0x00008121400000a0 0x4000102428000014 0x00000001c00000e0 0x000000003800001c

def z204 : W := mkw 0x2fff6e580fdfee05 0x05ffedcb01fbfdc0 0xeffffc700fffec05 0xfdffff8e01fffd80

def z205 : W := mkw 0x030a0600a0000000 0x006140c014000000 0xc70e0601f802739f 0x78e1c0c03f004e73

def z206 : W := mkw 0x225ff9871aebf18a 0x244bff30e35d7e31 0x903ffb8f38e3f39f 0xd207ff71e71c7e73

def z207 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfffc07ffcfff9fe7 0xffff80fff9fff3fc

def z208 : W := mkw 0x0010d99718eeb5ae 0x60021b32e31dd6b5 0x9833fb8f38ffffff 0xd3067f71e71fffff

def z209 : W := mkw 0x16efb16d50000000 0x02ddf62daa000000 0xb7fff9fe00000001 0xf6ffff3fc0000000

def z210 : W := mkw 0x000081b1402414a4 0x4000103628048294 0xf8c005f1c0fc1ce6 0xbf1800be381f839c

def z211 : W := mkw 0x17ef2668e3014a50 0x82fde4cd1c60294a 0x6fcc0470c7018c60 0x2df9808e18e0318c

def z212 : W := mkw 0x05b006480c900000 0x00b600c901920000 0xfff007fe0ffc0006 0xfffe00ffc1ff8000

def z213 : W := mkw 0x37ffff6dfedbe000 0x06ffffedbfdb7c00 0xffffffffffffe007 0xfffffffffffffc00

def z214 : W := mkw 0x020a000002014000 0x0041400000402800 0x0f0c000007018000 0x21e1800000e03000

def z215 : W := mkw 0x201048820efbf18a 0x2402091041df7e31 0x080000000ffff39c 0x0100000001fffe73

def z216 : W := mkw 0x26ff68000cdaa000 0x04dfed00019b5400 0xa7fff80000fc0001 0xf4ffff00001f8000

def z217 : W := mkw 0x281048920fffff07 0x0502091241ffffe0 0x080000000fffff04 0x0100000001ffffe0

def z218 : W := mkw 0x000010061000010a 0x20000200c2000021 0x0000020e30000318 0x00000041c6000063

def z219 : W := mkw 0x0000000003014a50 0x800000000060294a 0x000000000f006318 0x0000000001e00c63

def z220 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800000000039ce4 0x010000000000739c

def z221 : W := mkw 0x0045002040088020 0x4008a00408011004 0x000c0000c0018060 0x000180001800300c

def z222 : W := mkw 0x26fff9871efbf18a 0x24dfff30e3df7e31 0xbffffb8f3ffff39f 0xf7ffff71e7fffe73

def z223 : W := mkw 0x0010c98108e23080 0x00021930211c4610 0x9033f98108e27087 0xd2067f30211c4e10

def z224 : W := mkw 0x15e5b76d50000000 0x02bcb6edaa000000 0xf7f1fffe00000002 0xfefe3fffc0000000

def z225 : W := mkw 0x0000009000241404 0x0000001200048280 0x30c001f000fc0000 0x8618003e001f8000

def z226 : W := mkw 0x05a0064800000000 0x00b400c900000000 0x0730020e00000000 0x40e60041c0000000

def z227 : W := mkw 0x1000916d50000000 0x0200122daa000000 0x100001fe00000000 0x0200003fc0000000

def z228 : W := mkw 0x0045c121404a80a0 0x4008b82428095014 0xf0cdc5f1c00380e3 0xbe19b8be3800701c

def z229 : W := mkw 0x14e5f1fd506e94a4 0x429cbe3faa0dd294 0xf8fdfdffc0ff9ce7 0xbf1fbfbff81ff39c

def z230 : W := mkw 0x0800009201241f07 0x01000012402483e0 0x0000000000001f00 0x00000000000003e0

def z231 : W := mkw 0x0045d925504aa0a8 0x6008bb24aa095415 0x000ff801f003e0f9 0x0001ff003e007c1f

def z232 : W := mkw 0x000000820020118a 0x2000001040040231 0x0000000000001398 0x0000000000000273

def z233 : W := mkw 0x020a000000000000 0x0041400000000000 0x870e000000000001 0x70e1c00000000000

def z234 : W := mkw 0x0100060001000a00 0x002000c000200140 0x070002000f000300 0x40e0004001e00060

def z235 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x9033fb8f30e00003 0xd2067f71e61c0000

def z236 : W := mkw 0x00000010000c8424 0x4000000200019084 0x08000000001d8c60 0x010000000003b18c

def z237 : W := mkw 0x0100060001000a00 0x002000c000200140 0xcf0206013f027f9f 0x79e040c027e04ff3

def z238 : W := mkw 0x26ff20000e99c000 0x04dfe40001d33800 0xaffc00000ffd8004 0xf5ff800001ffb000

def z239 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x37f003fe0ffc0300 0xc6fe007fc1ff8060

def z240 : W := mkw 0x0055d98718eab18a 0x200abb30e31d5631 0xb8fffb8f38fff39f 0xf71fff71e71ffe73

def z241 : W := mkw 0x2fff6eda0fffff07 0x05ffeddb41ffffe0 0xfffffffe0fffff07 0xffffffffc1ffffe0

def z242 : W := mkw 0x0fff26da0db41f07 0x01ffe4db41b683e0 0xfffffffe0ffc1f07 0xffffffffc1ff83e0

def z243 : W := mkw 0x004581b1402414a4 0x4008b03628048294 0xf0cdc5f1c0001ce3 0xbe19b8be3800039c

def z244 : W := mkw 0x030ac781a3635ad0 0x806158f0346c6b5a 0xdf0fc781ffe3ffff 0xfbe1f8f03ffc7fff

def z245 : W := mkw 0x000091b7502415ae 0x60001236ea0482b5 0x500007fff0001ffa 0x0a0000fffe0003ff

def z246 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x37f3fbfe30000000 0xc6fe7f7fc6000000

def z247 : W := mkw 0x0010580618c2210a 0x20020b00c3184421 0x8033fa0e38e2631d 0xd0067f41c71c4c63

def z248 : W := mkw 0x224fe9b1426ff4a4 0x4449fd36284dfe94 0xf8cffdf1c0fffce7 0xbf19ffbe381fff9c

def z249 : W := mkw 0x26fff9871efbf18a 0x24dfff30e3df7e31 0xbffff98e0fffe005 0xf7ffff31c1fffc00

def z250 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x073ffa0ff0000001 0x40e7ff41fe000000

def z251 : W := mkw 0x224f6800024be000 0x0449ed0000497c00 0xa8cff80000ffe005 0xb519ff00001ffc00

def z252 : W := mkw 0x134fb725f3014a50 0x8269f6e4be60294a 0xcf0ffe01ff03ffff 0x79e1ffc03fe07fff

def z253 : W := mkw 0x200000000619c000 0x0400000000c33800 0x08000000071d8000 0x0100000000e3b000

def z254 : W := mkw 0x0045c1a140621080 0x0008b834280c4210 0xf0cdc5f1c0e21087 0xbe19b8be381c4210

def z255 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x4f0e0401f703ecf9 0x29e1c0803ee07d9f

def z256 : W := mkw 0x0000000001000a00 0x0000000000200140 0x080000000f001f04 0x0100000001e003e0

def z257 : W := mkw 0x0da006da01241f07 0x01b400db402483e0 0xf7f007fe00001f02 0xfefe00ffc00003e0

def z258 : W := mkw 0x0000000003014a50 0x800000000060294a 0xc80c0401cf03ffff 0x3901808039e07fff

def z259 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x1031fb8f30e0139a 0x82063f71e61c0273

def z260 : W := mkw 0x0110df87b9e23bda 0xa0221bf0f73c477b 0xd033ff8ff8e27fff 0xda067ff1ff1c4fff

def z261 : W := mkw 0x0045d1b5506e94a4 0x4008ba36aa0dd294 0xf8fffffff0ff9ce7 0xff1ffffffe1ff39c

def z262 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c0001c00380e1 0x000180003800701c

def z263 : W := mkw 0x000081b1402414a4 0x4000103628048294 0x500005f1c0001ce2 0x0a0000be3800039c

def z264 : W := mkw 0x0010489208eeb5ae 0x60020912411dd6b5 0x0800000008fffffc 0x01000000011fffff

def z265 : W := mkw 0x0db006da0fb55f57 0x81b600db41f6abea 0xfff007fe0ffffffe 0xfffe00ffc1ffffff

def z266 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xeffffc01cffffce7 0xfdffff8039ffff9c

def z267 : W := mkw 0x06aa200000000000 0x00d5440000000000 0x0732380000000000 0x40e6470000000000

def z268 : W := mkw 0x0000009000241404 0x0000001200048280 0xf8cc05f1c0ff9ce7 0xbf1980be381ff39c

def z269 : W := mkw 0x2fff6e4a0fdbeb03 0x05ffedc941fb7d60 0xaffffa0e0fffe305 0xf5ffff41c1fffc60

def z270 : W := mkw 0x081000920fb55f57 0x8102001241f6abea 0x080000000ffffffc 0x0100000001ffffff

def z271 : W := mkw 0x17efb76df2014050 0x82fdf6edbe40280a 0xf7fffffff003e0fb 0xfefffffffe007c1f

def z272 : W := mkw 0x00000000a0000050 0x800000001400000a 0x00000001f00000f8 0x000000003e00001f

def z273 : W := mkw 0x27ffefb1effffef4 0xc4fffdf63dffffde 0xfffffff1ffffffff 0xfffffffe3fffffff

def z274 : W := mkw 0x26ff68000fdbea50 0x84dfed0001fb7d4a 0xaffff8000ffffffd 0xf5ffff0001ffffff

def z275 : W := mkw 0x0000001000040404 0x0000000200008080 0x68c00470001c0c00 0x2d18008e00038180

def z276 : W := mkw 0x01000600a1000a50 0x802000c01420014a 0xcf000601ff001ffe 0x79e000c03fe003ff

def z277 : W := mkw 0x0010488208e2318a 0x20020910411c4631 0x0000000000e00000 0x00000000001c0000

def z278 : W := mkw 0x0db0064a0d900b03 0x01b600c941b20160 0xcf30060e0f001f06 0x79e600c1c1e003e0

def z279 : W := mkw 0x26ba28000e916000 0x04d7450001d22c00 0xaff238000ffc6004 0xf5fe470001ff8c00

def z280 : W := mkw 0x031a4e00abc36a50 0x806349c015786d4a 0xcf3ffe01ffe3ffff 0xf9e7ffc03ffc7fff

def z281 : W := mkw 0x0000000000000000 0x0000000000000000 0x8f0000000f000004 0x71e0000001e00000

def z282 : W := mkw 0x221a48000edbe000 0x0443490001db7c00 0x8f0e00000fffe005 0x71e1c00001fffc00

def z283 : W := mkw 0x224ff905124be088 0x2449ff20a2497c11 0x000ff8013003e099 0x0001ff0026007c13

def z284 : W := mkw 0x37fffffdfefff4a4 0x46ffffffbfdffe94 0xfffffffffffffce7 0xffffffffffffff9c

def z285 : W := mkw 0x05a0064800000000 0x00b400c900000000 0xf7f007fe00000002 0xfefe00ffc0000000

def z286 : W := mkw 0x030a9705b3014a50 0x806152e0b660294a 0xdf3fff8fff03ffff 0xfbe7fff1ffe07fff

def z287 : W := mkw 0x0fffc7fbefffdff7 0xc1fff8ff7dfffbfe 0xffffc7ffffffffff 0xfffff8ffffffffff

def z288 : W := mkw 0x26ff6800aedbe050 0x84dfed0015db7c0a 0xaffff801ffffe0fd 0xf5ffff003ffffc1f

def z289 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x0003f80138e2739d 0x00007f00271c4e73

def z290 : W := mkw 0x0000408000621080 0x00000810000c4210 0x0000000000e21084 0x00000000001c4210

def z291 : W := mkw 0x37ff6e68eedbe000 0x06ffedcd1ddb7c00 0xeffffc70cfffe005 0xfdffff8e19fffc00

def z292 : W := mkw 0x090006da01241f07 0x012000db402483e0 0xf8c007fe00fc1f06 0xbf1800ffc01f83e0

def z293 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x30cdc1f1c0ff80e1 0x8619b83e381ff01c

def z294 : W := mkw 0x034fc7b1e06e94a4 0x4069f8f63c0dd294 0xffcfc7f1f0ff9ce7 0xfff9f8fe3e1ff39c

def z295 : W := mkw 0x26ef20000619c000 0x04dde40000c33800 0xaffff800071d8001 0xf5ffff0000e3b000

def z296 : W := mkw 0x07aa0648a3014a50 0x80f540c91460294a 0xfffe07ffff03ffff 0xffffc0ffffe07fff

def z297 : W := mkw 0x0000000000000000 0x0000000000000000 0x8033f80000000001 0xd0067f0000000000

def z298 : W := mkw 0x17eff7fdf06e94a4 0x42fdfeffbe0dd294 0xf7fffffff0fc0003 0xfefffffffe1f8000

def z299 : W := mkw 0x0010080008802000 0x0002010001100400 0x0032380008006000 0x4006470001000c00

def z300 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x9033f98e08e26005 0xd2067f31c11c4c00

def z301 : W := mkw 0x0de5c7f9457e9ea5 0x41bcb8ff28afd3d4 0xffcdc5f1c7ff9ce7 0xbff9b8be38fff39c

def z302 : W := mkw 0x0010000008800000 0x0002000001100000 0x8030000008e00004 0xd0060000011c0000

def z303 : W := mkw 0x020a000002014000 0x0041400000402800 0x8f0e02013f03f39f 0x71e1c04027e07e73

def z304 : W := mkw 0x0fba064aaf914b53 0x81f740c955f2296a 0x0732020e3f006318 0x40e64041c7e00c63

def z305 : W := mkw 0x00004090006e94a4 0x40000812000dd294 0x0000000000fc0000 0x00000000001f8000

def z306 : W := mkw 0x0fba06daadb41f07 0x01f740db55b683e0 0xfffe07fffffc1f07 0xffffc0ffffff83e0

def z307 : W := mkw 0x17eff7fdf06e94a4 0x42fdfeffbe0dd294 0xfffffffff0ff9ce7 0xfffffffffe1ff39c

def z308 : W := mkw 0x00454000004a8000 0x0008a80000095000 0x000dc00000038001 0x0001b80000007000

def z309 : W := mkw 0x0010488208e23102 0x00020910411c4620 0x9033fb8e08e27307 0xd2067f71c11c4e60

def z310 : W := mkw 0x26ff28000e99e000 0x04dfe50001d33c00 0x2ffe38000f1de000 0x65ffc70001e3bc00

def z311 : W := mkw 0x0045000000088000 0x0008a00000011000 0x28cc0000001d8000 0x251980000003b000

def z312 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x7ff005fe07fc0c00 0xaffe00bfc0ff8180

def z313 : W := mkw 0x17aa364cb0000000 0x02f546c996000000 0xc73e3e0ff0000003 0x78e7c7c1fe000000

def z314 : W := mkw 0x0db087fb4db41fa7 0x41b610ff69b683f4 0xfff007ffcffc1fe6 0xfffe00fff9ff83fc

def z315 : W := mkw 0x110097fdf02414a4 0x422012ffbe048294 0x500007fff0001ce2 0x0a0000fffe00039c

def z316 : W := mkw 0x001018061880210a 0x20020300c3100421 0x0030380e00000000 0x00060701c0000000

def z317 : W := mkw 0x031a1e06bb816b5a 0xa06343c0d7702d6b 0x07323a0e3f006318 0x40e64741c7e00c63

def z318 : W := mkw 0x0db0dfcf1df23b8b 0x21b61bf9e3be4771 0x9733fb8f3fe2739f 0xd2e67f71e7fc4e73

def z319 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x1031f98e08e2739c 0x82063f31c11c4e73

def z320 : W := mkw 0x0800001005140e05 0x0100000200a281c0 0x08000000071c0c00 0x0100000000e38180

def z321 : W := mkw 0x021ad987bae371da 0xa0435b30f75c6e3b 0x903ffb8ff8e3f3ff 0xd207ff71ff1c7e7f

def z322 : W := mkw 0x0045812140000000 0x0008b02428000000 0xf8cdc5f1c0039ce7 0xbf19b8be3800739c

def z323 : W := mkw 0x17eff7edf0621080 0x02fdfefdbe0c4210 0xf7fffffff0e21087 0xfefffffffe1c4210

def z324 : W := mkw 0x26ffe9810efbf080 0x04dffd3021df7e10 0xbffff9810ffff087 0xf7ffff3021fffe10

def z325 : W := mkw 0x26aa200006114000 0x04d5440000c22800 0x0700000007000000 0x00e0000000e00000

def z326 : W := mkw 0x27ef2600a719ca50 0x84fde4c014e3394a 0xefce0601ff1fffff 0x7df9c0c03fe3ffff

def z327 : W := mkw 0x090087fb41241fa7 0x412010ff682483f4 0x500007ffc0001fe2 0x0a0000fff80003fc

def z328 : W := mkw 0x031a0682aba15b52 0x806340d055742b6a 0xdf3e078fffe3ffff 0xfbe7c0f1fffc7fff

def z329 : W := mkw 0x0db006580d940e05 0x01b600cb01b281c0 0xeff004700ffc0c04 0xfdfe008e01ff8180

def z330 : W := mkw 0x27ffff87bffbfbda 0xa4fffff0f7ff7f7b 0xffffff8fffffffff 0xfffffff1ffffffff

def z331 : W := mkw 0x0b1a0692afb55f57 0x816340d255f6abea 0xcf0e0601ffffffff 0x79e1c0c03fffffff

def z332 : W := mkw 0x030a060003014a00 0x006140c000602940 0xcf0e06000f03ff07 0x79e1c0c001e07fe0

def z333 : W := mkw 0x020a000002014000 0x0041400000402800 0xcf0e0401cf03fce7 0x79e1c08039e07f9c

def z334 : W := mkw 0x0faa0658a7154e55 0x81f540cb14e2a9ca 0x6fcc0470c71d8c60 0x2df9808e18e3b18c

def z335 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x1033f98f30e26099 0x82067f31e61c4c13

def z336 : W := mkw 0x0045912550000000 0x0008b224aa000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z337 : W := mkw 0x0000003040040424 0x4000000608008084 0x40000470c0000c60 0x0800008e1800018c

def z338 : W := mkw 0x00454000004a8000 0x0008a80000095000 0xa8cdc00000ff8005 0xb519b800001ff000

def z339 : W := mkw 0x00004090006e94a4 0x40000812000dd294 0xc80c0401c0ff9ce7 0x39018080381ff39c

def z340 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x70f007fe00fc1f02 0x8e1e00ffc01f83e0

def z341 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xb0c1c1f100fe1087 0x9618383e201fc210

def z342 : W := mkw 0x090006daa1241f57 0x812000db542483ea 0x500007fff0001ffa 0x0a0000fffe0003ff

def z343 : W := mkw 0x0000c18100621080 0x00001830200c4210 0x1001c18000e00000 0x82003830001c0000

def z344 : W := mkw 0x0000810100000000 0x0000102020000000 0x9001c18100000003 0x9200383020000000

def z345 : W := mkw 0x00454000004a8000 0x0008a80000095000 0x20c1c00000fc0000 0x84183800001f8000

def z346 : W := mkw 0x0cb0d9df1cf6358f 0x21961b3be39ec6b1 0xb0f3fbff38fe739f 0xd61e7f7fe71fce73

def z347 : W := mkw 0x0100060001000a00 0x002000c000200140 0x4000060000001f02 0x080000c0000003e0

def z348 : W := mkw 0x234f6e00a34bea50 0x8469edc014697d4a 0xcf0ffe01ff03ffff 0x79e1ffc03fe07fff

def z349 : W := mkw 0x24f5e9b14cfeb4a4 0x449ebd36299fd694 0x30f1f9f000fc0000 0x861e3f3e001f8000

def z350 : W := mkw 0x20004800024be000 0x0400090000497c00 0x000000000003e000 0x0000000000007c00

def z351 : W := mkw 0x17efa769e0000000 0x02fdf4ed3c000000 0xf7cdc5f1c0000003 0xbef9b8be38000000

def z352 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff207ff3ffe7f9f 0xfffe40ffe7ffcff3

def z353 : W := mkw 0x17eff7fdf36fdef4 0xc2fdfeffbe6dfbde 0xffffffffffffffff 0xffffffffffffffff

def z354 : W := mkw 0x0db046da0dfe9fa7 0x41b608db41bfd3f4 0xfff007fe0fff9fe6 0xfffe00ffc1fff3fc

def z355 : W := mkw 0x15e5b76df0000000 0x02bcb6edbe000000 0x70f1fffff0000002 0x8e1e3ffffe000000

def z356 : W := mkw 0x190097fff1241f07 0x032012fffe2483e0 0x500007fff0001f02 0x0a0000fffe0003e0

def z357 : W := mkw 0x0010480008c22000 0x0002090001184400 0x0031f80000e00000 0x80063f00001c0000

def z358 : W := mkw 0x05a0974d10000000 0x00b412e9a2000000 0xf7f3ffff30000003 0xfefe7fffe6000000

def z359 : W := mkw 0x17efb7eff020118a 0x22fdf6fdfe040231 0xf7fffffff000139b 0xfefffffffe000273

def z360 : W := mkw 0x37efb76df619c000 0x06fdf6edbec33800 0xfffffffff71d8003 0xfffffffffee3b000

def z361 : W := mkw 0x1145976df0000000 0x0228b2edbe000000 0xf0cdc7fff0000003 0xbe19b8fffe000000

def z362 : W := mkw 0x26ba68000ed36000 0x04d74d0001da6c00 0x8733f8000fe26005 0xd0e67f0001fc4c00

def z363 : W := mkw 0x05a0064800000000 0x00b400c900000000 0x67c0047000000000 0x2cf8008e00000000

def z364 : W := mkw 0x24f5e9b14cfeb4a4 0x449ebd36299fd694 0xf8fdfdf1c0ff9ce7 0xbf1fbfbe381ff39c

def z365 : W := mkw 0x000081b1402414a4 0x4000103628048294 0x100001f000000000 0x0200003e00000000

def z366 : W := mkw 0x0045812140000000 0x0008b02428000000 0x30c1c1f000000000 0x8618383e00000000

def z367 : W := mkw 0x0000000002014050 0x800000000040280a 0x000000000003e0f8 0x0000000000007c1f

def z368 : W := mkw 0x06ef200000000000 0x00dde40000000000 0x27cc000000000000 0x24f9800000000000

def z369 : W := mkw 0x201048900efff4a4 0x4402091201dffe94 0x080000000ffffce4 0x0100000001ffff9c

def z370 : W := mkw 0x26ef20000619c000 0x04dde40000c33800 0xafce00000f1fe005 0x75f9c00001e3fc00

def z371 : W := mkw 0x0055480008caa000 0x000aa90001195400 0xa8fff80008ffe005 0xf51fff00011ffc00

def z372 : W := mkw 0x26ff68900efff404 0x04dfed1201dffe80 0xfffffdf00ffffc07 0xffffffbe01ffff80

def z373 : W := mkw 0x26ef2030461dc424 0x44dde40608c3b884 0x6fcc0470c71d8c60 0x2df9808e18e3b18c

def z374 : W := mkw 0x27ef2600a719ca50 0x84fde4c014e3394a 0x6fcc0400c71d8c60 0x2df9808018e3b18c

def z375 : W := mkw 0x0945c7fb416e9fa7 0x4128b8ff682dd3f4 0xf8cdc7ffc0ff9fe7 0xbf19b8fff81ff3fc

def z376 : W := mkw 0x030a0600a1000a50 0x806140c01420014a 0xc70e0601f0001ffb 0x78e1c0c03e0003ff

def z377 : W := mkw 0x0000c18100621080 0x00001830200c4210 0xd80dc581c0e39ce7 0xbb01b8b0381c739c

def z378 : W := mkw 0x17efb76df1000a00 0x02fdf6edbe200140 0xffffffffff001f07 0xffffffffffe003e0

def z379 : W := mkw 0x26ff68820efbf18a 0x24dfed1041df7e31 0xaffff8000ffff39d 0xf5ffff0001fffe73

def z380 : W := mkw 0x26ba38061e91610a 0x24d74700c3d22c21 0x07323a0e3f006318 0x40e64741c7e00c63

def z381 : W := mkw 0x0fba06daafb55f57 0x81f740db55f6abea 0xfff207fe3ffc7f1e 0xfffe40ffc7ff8fe3

def z382 : W := mkw 0x1045b12550000000 0x0208b624aa000000 0x0001f80000000000 0x00003f0000000000

def z383 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x0f0202003f03fffc 0x41e0404007e07fff

def z384 : W := mkw 0x1fba364ebd900b03 0x03f746c9d7b20160 0x07323a0e3f000300 0x40e64741c7e00060

def z385 : W := mkw 0x07ef2600a3014a50 0x80fde4c01460294a 0xeffffe01ff03ffff 0xfdffffc03fe07fff

def z386 : W := mkw 0x04a0000004100000 0x0094000000820000 0x2fc00000071c0000 0x25f8000000e38000

def z387 : W := mkw 0x201008000e916000 0x0402010001d22c00 0x000000000f006000 0x0000000001e00c00

def z388 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x073ff8000f03e001 0x40e7ff0001e07c00

def z389 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x9031fb8e08e01306 0xd2063f71c11c0260

def z390 : W := mkw 0x06ef200002014000 0x00dde40000402800 0xaffff8000f03e005 0xf5ffff0001e07c00

def z391 : W := mkw 0x224f20000209c000 0x0449e40000413800 0x000c000000018000 0x0001800000003000

def z392 : W := mkw 0x1fffb76ffd900b03 0x03fff6edffb20160 0xf7ffffffff000303 0xfeffffffffe00060

def z393 : W := mkw 0x0cb000da0db41f07 0x0196001b41b683e0 0x38f001fe0ffc1f04 0x871e003fc1ff83e0

def z394 : W := mkw 0x14e5206840000000 0x029ca40d08000000 0x20c0007000000000 0x0418000e00000000

def z395 : W := mkw 0x0cb0004a0c900103 0x0196000941920020 0x0030000e00000000 0x00060001c0000000

def z396 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x8f0e02003f03e31d 0x71e1c04007e07c63

def z397 : W := mkw 0x20456800004aa000 0x0408ad0000095400 0x0001f80000000000 0x00003f0000000000

def z398 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x38c1c1f000ff9ce4 0x8718383e001ff39c

def z399 : W := mkw 0x24f5f9871cfab18a 0x249ebf30e39f5631 0xb0f3fb8f38fe739f 0xd61e7f71e71fce73

def z400 : W := mkw 0x000081b1402414a4 0x4000103628048294 0xd80c05f1c0039ce7 0x3b0180be3800739c

def z401 : W := mkw 0x15a0976df0000000 0x02b412edbe000000 0xf7f007fff0000002 0xfefe00fffe000000

def z402 : W := mkw 0x0010488208e2318a 0x20020910411c4631 0x8033f80008e2739d 0xd0067f00011c4e73

def z403 : W := mkw 0x0055d9b758eeb5ae 0x600abb36eb1dd6b5 0xf8fdfdffc0ff9ce7 0xbf1fbfbff81ff39c

def z404 : W := mkw 0x090006da01241f07 0x012000db402483e0 0xdf0007fe0f001f06 0x7be000ffc1e003e0

def z405 : W := mkw 0x020a0000a2014050 0x804140001440280a 0x8f0e0001ff03e0fd 0x71e1c0003fe07c1f

def z406 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0xcf0206003f007f1e 0x79e040c007e00fe3

def z407 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf0cdc5f1c0fc0003 0xbe19b8be381f8000

def z408 : W := mkw 0x0db0064a0d900b03 0x01b600c941b20160 0xf7f007fe0f000302 0xfefe00ffc1e00060

def z409 : W := mkw 0x17aab76df0000000 0x02f556edbe000000 0x57323ffff0000002 0x4ae647fffe000000

def z410 : W := mkw 0x17aa2648a0000000 0x02f544c914000000 0x0700000000000000 0x00e0000000000000

def z411 : W := mkw 0x0000000003014a50 0x800000000060294a 0x0800000007018c60 0x0100000000e0318c

def z412 : W := mkw 0x130a976df0000000 0x026152edbe000000 0xd70e07fff0000003 0x7ae1c0fffe000000

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0xc80e0601f803ffff 0x7901c0c03f007fff

def z414 : W := mkw 0x2fffeffb4fffffa7 0x45fffdff69fffff4 0xffffffffcfffffe7 0xfffffffff9fffffc

def z415 : W := mkw 0x1100164cb0000000 0x022002c996000000 0x0000020e30000000 0x00000041c6000000

def z416 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0xcf0c0401c7039ce7 0x39e1808038e0739c

def z417 : W := mkw 0x01000600a1000a50 0x802000c01420014a 0x0000020030000318 0x0000004006000063

def z418 : W := mkw 0x0010918718a01102 0x00021230e3140220 0x9033fb8f38e01307 0xd2067f71e71c0260

def z419 : W := mkw 0x034f8721e0000000 0x0069f0e43c000000 0xf7cfc7f1f0000003 0xfef9f8fe3e000000

def z420 : W := mkw 0x030a0600a2014050 0x806140c01440280a 0xc70e0601f003e0fb 0x78e1c0c03e007c1f

def z421 : W := mkw 0x0000d18510621080 0x00001a30a20c4210 0x9033fb8f30e21087 0xd2067f71e61c4210

def z422 : W := mkw 0x0010d99718e6358e 0x20021b32e31cc6b1 0xf8f3ffff38fe7f9f 0xff1e7fffe71fcff3

def z423 : W := mkw 0x0da006d805341e05 0x01b400db00a683c0 0xffc005f007fc1c06 0xbff800be00ff8380

def z424 : W := mkw 0x0110068209a01b02 0x002200d041340360 0xdf30078e0fe01f06 0xfbe600f1c1fc03e0

def z425 : W := mkw 0x225f68000acbe000 0x044bed0001597c00 0x803ff80008e3e005 0xd007ff00011c7c00

def z426 : W := mkw 0x081040920dfe9fa7 0x4102081241bfd3f4 0x080000000fff9fe4 0x0100000001fff3fc

def z427 : W := mkw 0x07ba0600af914a50 0x80f740c015f2294a 0xeffe0601ffffffff 0xfdffc0c03fffffff

def z428 : W := mkw 0x0000008000201000 0x0000001000040200 0x9000018000e01006 0x92000030001c0200

def z429 : W := mkw 0x220a280002016000 0x0441450000402c00 0x0002380000006000 0x0000470000000c00

def z430 : W := mkw 0x00454090006e9404 0x0008a812000dd280 0xf8cdc5f000ff9c07 0xbf19b8be001ff380

def z431 : W := mkw 0x17ef2668e3014a50 0x82fde4cd1c60294a 0xefce0671ff03ffff 0x7df9c0ce3fe07fff

def z432 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0xcf0e0400cf03ec65 0x79e1c08019e07d8c

def z433 : W := mkw 0x034fc721e34bcaf0 0xc069f8e43c69795e 0xcf0fc601ff03ffff 0x79e1f8c03fe07fff

def z434 : W := mkw 0x1fffb7ffffb55f57 0x83fff6fffff6abea 0xffffffffffffffff 0xffffffffffffffff

def z435 : W := mkw 0x125ff9a7f8e2318a 0x224bff34ff1c4631 0x903ffb8ff8e2739f 0xd207ff71ff1c4e73

def z436 : W := mkw 0x0cb000da0cb41507 0x0196001b419682a0 0xb0f003fe08fc1306 0xd61e007fc11f8260

def z437 : W := mkw 0x0000d98510623088 0x20001b30a20c4611 0x9003f98130e2709f 0x92007f30261c4e13

def z438 : W := mkw 0x0010c18308e21182 0x00021830611c4230 0x9031c38f08e21387 0xd2063871e11c4270

def z439 : W := mkw 0x17efff6df0422088 0x22fdffedbe084411 0xf7fffffff002609b 0xfefffffffe004c13

def z440 : W := mkw 0x2eff68da0efff507 0x05dfed1b41dffea0 0xbffff9fe0fffe005 0xf7ffff3fc1fffc00

def z441 : W := mkw 0x224f6800a24be050 0x8449ed0014497c0a 0x000ff801f003e0f9 0x0001ff003e007c1f

def z442 : W := mkw 0x17aab74db0000000 0x02f556e9b6000000 0x9733fb8f30000003 0xd2e67f71e6000000

def z443 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x400e0601f003fffb 0x0801c0c03e007fff

def z444 : W := mkw 0x2cf568da0cfeb507 0x059ead1b419fd6a0 0x30f1f9fe00fc0000 0x861e3f3fc01f8000

def z445 : W := mkw 0x030a0600a0000000 0x006140c014000000 0xcf0e0601f0039ce7 0x79e1c0c03e00739c

def z446 : W := mkw 0x2df56eda0dfebf07 0x05beaddb41bfd7e0 0xfff1fffe0ffc1f06 0xfffe3fffc1ff83e0

def z447 : W := mkw 0x01000600a1000a50 0x802000c01420014a 0x40000400c0000c60 0x080000801800018c

def z448 : W := mkw 0x2fba2eda0fb57f07 0x05f745db41f6afe0 0xfff23ffe0ffc7f06 0xfffe47ffc1ff8fe0

def z449 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x20fff80000ffe001 0x841fff00001ffc00

def z450 : W := mkw 0x0000000001000a50 0x800000000020014a 0x0000000000001ff8 0x00000000000003ff

def z451 : W := mkw 0x0cb000920db41f07 0x0196001241b683e0 0xaff000000ffc1f04 0xf5fe000001ff83e0

def z452 : W := mkw 0x26ff78061edbe10a 0x24dfef00c3db7c21 0xaffffa0e3fffe31d 0xf5ffff41c7fffc63

def z453 : W := mkw 0x0010c98308e2318a 0x20021930611c4631 0x9001c18108e2739f 0x92003830211c4e73

def z454 : W := mkw 0x0010008208a01102 0x0002001041140220 0x0000000008e01304 0x00000000011c0260

def z455 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x27f3f8000ffc6000 0xc4fe7f0001ff8c00

def z456 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x573007fe0f001f02 0x4ae600ffc1e003e0

def z457 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x67cffc71f0000001 0x2cf9ff8e3e000000

def z458 : W := mkw 0x124ff925f0422088 0x2249ff24be084411 0x000ff801f0026099 0x0001ff003e004c13

def z459 : W := mkw 0x024fc1b1e26fd4f4 0xc049f8363c4dfa9e 0xf8cfc5f1f0fffcff 0xbf19f8be3e1fff9f

def z460 : W := mkw 0x1fefb77df5140e05 0x03fdf6efbea281c0 0xfffffffff71c0c03 0xfffffffffee38180

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000100021087 0x1000000020004210

def z462 : W := mkw 0x17eff76df04a8000 0x02fdfeedbe095000 0xfffffffff0ff8007 0xfffffffffe1ff000

def z463 : W := mkw 0x00458131400c8424 0x4008b02628019084 0xf8cdc5f1c01d8c63 0xbf19b8be3803b18c

def z464 : W := mkw 0x00454000004a8000 0x0008a80000095000 0xe8cdc401c0ff9ce7 0xbd19b880381ff39c

def z465 : W := mkw 0x00454030404e8424 0x4008a8060809d084 0xe8cdc470c0ff8c65 0xbd19b88e181ff18c

def z466 : W := mkw 0x0010d90718c2218a 0x20021b20e3184431 0x0033fa0f38026399 0x40067f41e7004c73

def z467 : W := mkw 0x16efb16df0000000 0x02ddf62dbe000000 0x30fff9fff0000001 0x861fff3ffe000000

def z468 : W := mkw 0x020a000002014000 0x0041400000402800 0x000e00000003e001 0x0001c00000007c00

def z469 : W := mkw 0x24f568000edbe000 0x049ead0001db7c00 0x28f1f8000fffe004 0x851e3f0001fffc00

def z470 : W := mkw 0x1fefb7fff1241f07 0x03fdf6fffe2483e0 0xf7fffffff0001f03 0xfefffffffe0003e0

def z471 : W := mkw 0x004581b1402c94a4 0x4008b03628059294 0x78cc05f1c01d9ce2 0x2f1980be3803b39c

def z472 : W := mkw 0x00004000004a80a0 0x4000080000095014 0x00000000000380e0 0x000000000000701c

def z473 : W := mkw 0x0100064800000000 0x002000c900000000 0x500007fe00000002 0x0a0000ffc0000000

def z474 : W := mkw 0x091006da0db41f07 0x012200db41b683e0 0x580007fe0ffc1f06 0x0b0000ffc1ff83e0

def z475 : W := mkw 0x00004090006e94a4 0x40000812000dd294 0xf8c005f000ff9ce6 0xbf1800be001ff39c

def z476 : W := mkw 0x0000100410000000 0x0000020082000000 0x00323a0e30000000 0x40064741c6000000

def z477 : W := mkw 0x37ffff6dffdbea50 0x86ffffedbffb7d4a 0xffffffffffffffff 0xffffffffffffffff

def z478 : W := mkw 0x05a0064801000a00 0x00b400c900200140 0xfff007fe0f001f06 0xfffe00ffc1e003e0

def z479 : W := mkw 0x04a0000000000000 0x0094000000000000 0xa7f0000000000000 0xf4fe000000000000

def z480 : W := mkw 0x030a9705b0000000 0x006152e0b6000000 0xd73fff8ff0000003 0xfae7fff1fe000000

def z481 : W := mkw 0x0da0065805140e05 0x01b400cb00a281c0 0xefc006700f1c1f06 0x7df800ce01e383e0

def z482 : W := mkw 0x0df5c7fb4dfe9fa7 0x41beb8ff69bfd3f4 0xfff1c7fe0ffc1f06 0xfffe38ffc1ff83e0

def z483 : W := mkw 0x0df5dfff5dfebfaf 0x61bebbffebbfd7f5 0xffffffffffffffff 0xffffffffffffffff

def z484 : W := mkw 0x0000180410002008 0x2000030082000401 0x0002380030006018 0x0000470006000c03

def z485 : W := mkw 0x2fff26da0fbddf07 0x05ffe4db41f7bbe0 0xfffc07fe0ffd9f06 0xffff80ffc1ffb3e0

def z486 : W := mkw 0x0055d9a758eab1aa 0x600abb34eb1d5635 0x903ffb8ff8e3f3ff 0xd207ff71ff1c7e7f

def z487 : W := mkw 0x17efb7fdf02414a4 0x42fdf6ffbe048294 0xf7fffffff0001ce3 0xfefffffffe00039c

def z488 : W := mkw 0x17ffb76dfc900000 0x02fff6edbf920000 0xfffffffffffc0007 0xffffffffffff8000

def z489 : W := mkw 0x0910dfdf19e63f8f 0x21221bfbe33cc7f1 0xd033ffff38e27f9f 0xda067fffe71c4ff3

def z490 : W := mkw 0x2db04eda0fffff07 0x05b609db41ffffe0 0xfff007fe0fffff06 0xfffe00ffc1ffffe0

def z491 : W := mkw 0x0010000208800102 0x0002000041100020 0x0030020e08000300 0x40060041c1000060

def z492 : W := mkw 0x0045002040000000 0x0008a00408000000 0x60cc0470c0000000 0x2c19808e18000000

def z493 : W := mkw 0x0010008208a01102 0x0002001041140220 0x1030018e00e00000 0x82060031c01c0000

def z494 : W := mkw 0x0055c9b148eeb4a4 0x400ab936291dd694 0xf8fffdf1c8fffce7 0xff1fffbe391fff9c

def z495 : W := mkw 0x0cf5c1fb4cfe95a7 0x419eb83f699fd2b4 0x30f1c1fe00fc0000 0x861e383fc01f8000

def z496 : W := mkw 0x0df587fb4db41f07 0x01beb0ff69b683e0 0xfffdc7ffcffc1f07 0xffffb8fff9ff83e0

def z497 : W := mkw 0x07aa0648a0000000 0x00f540c914000000 0xf7fe07fff0000003 0xfeffc0fffe000000

def z498 : W := mkw 0x020a0000a2014050 0x804140001440280a 0x000c0000c0018060 0x000180001800300c

def z499 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x070e0201ff03e3f9 0x40e1c0403fe07c7f

def z500 : W := mkw 0x0db006da0cb41507 0x01b600db419682a0 0xf7f007fe00fc0002 0xfefe00ffc01f8000

def z501 : W := mkw 0x0010009208a41506 0x00020012411482a0 0xf8f007fe08fc1f06 0xff1e00ffc11f83e0

def z502 : W := mkw 0x020a0000a2014050 0x804140001440280a 0xc80e0401f003fcff 0x3901c0803e007f9f

def z503 : W := mkw 0x27ba2e00af916a50 0x84f745c015f22d4a 0x07323a003f006318 0x40e6474007e00c63

def z504 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x47020601ff007ffa 0x48e040c03fe00fff

def z505 : W := mkw 0x01000600a3014a50 0x802000c01460294a 0x48000601ff03fffe 0x090000c03fe07fff

def z506 : W := mkw 0x001048820be37bda 0xa0020910417c6f7b 0x080000000fe3fffc 0x0100000001fc7fff

def z507 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8c1c5f000fc1c06 0xbf1838be001f8380

def z508 : W := mkw 0x14e5f1fd506e94a4 0x429cbe3faa0dd294 0x30f1f9fe00fc0000 0x861e3f3fc01f8000

def z509 : W := mkw 0x00000090002414a4 0x4000001200048294 0x0000000000001ce0 0x000000000000039c

def z510 : W := mkw 0x080000da00241507 0x0100001b400482a0 0x100001fe00000000 0x0200003fc0000000

def z511 : W := mkw 0x37ba3e4cbe916000 0x06f747c997d22c00 0x07323a0e3f006000 0x40e64741c7e00c00

def z512 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z513 : W := mkw 0x0000480000422088 0x2000090000084411 0x0000000000026098 0x0000000000004c13

def z514 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x4f0c0400cf03fffc 0x29e1808019e07fff

def z515 : W := mkw 0x2fff6edaafffff57 0x85ffeddb55ffffea 0xffffffffffffffff 0xffffffffffffffff

def z516 : W := mkw 0x201048000cdaa000 0x04020900019b5400 0x0000000000fc0000 0x00000000001f8000

def z517 : W := mkw 0x0db006daadb41f57 0x81b600db55b683ea 0xfff007fffffc1ffe 0xfffe00ffffff83ff

def z518 : W := mkw 0x1df5b7ff5db41f07 0x03beb6ffebb683e0 0xfff1fffe0ffc1f06 0xfffe3fffc1ff83e0

def z519 : W := mkw 0x27ff6e00afdbea50 0x84ffedc015fb7d4a 0xeffffc00cfffec65 0xfdffff8019fffd8c

def z520 : W := mkw 0x06efb10510000000 0x00ddf620a2000000 0xb7fffb8f30000003 0xf6ffff71e6000000

def z521 : W := mkw 0x0810d9971df63f8f 0x21021b32e3bec7f1 0x9833fb8f3ffe7f9f 0xd3067f71e7ffcff3

def z522 : W := mkw 0x1110dfeff8e2318a 0x22221bfdff1c4631 0xd033fffff8e2739f 0xda067fffff1c4e73

def z523 : W := mkw 0x0db006ca0db01b03 0x01b600d941b60360 0x9730038e0fe01306 0xd2e60071c1fc0260

def z524 : W := mkw 0x0fbadfdfbff77fdf 0xa1f75bfbf7feeffb 0xffffffffffffffff 0xffffffffffffffff

def z525 : W := mkw 0x26ffe9214edbe000 0x04dffd2429db7c00 0xfffffdf1cfffe007 0xffffffbe39fffc00

def z526 : W := mkw 0x091006920db41f07 0x012200d241b683e0 0xcf0006000ffc1f06 0x79e000c001ff83e0

def z527 : W := mkw 0x04e5200000000000 0x009ca40000000000 0x20f1f80000000000 0x841e3f0000000000

def z528 : W := mkw 0x0000910510000000 0x00001220a2000000 0x1000038f30000002 0x02000071e6000000

def z529 : W := mkw 0x00004090036fdef4 0xc0000812006dfbde 0x080000000ffffffc 0x0100000001ffffff

def z530 : W := mkw 0x124ff1b5f06e94a4 0x4249fe36be0dd294 0xf8cffdf1f0ff9ce7 0xbf19ffbe3e1ff39c

def z531 : W := mkw 0x24b028000c902000 0x0496050001920400 0x0030380000000000 0x0006070000000000

def z532 : W := mkw 0x020a000002014000 0x0041400000402800 0x070200000f006000 0x40e0400001e00c00

def z533 : W := mkw 0x0100060003014a50 0x802000c00060294a 0xcf0006000f03fffe 0x79e000c001e07fff

def z534 : W := mkw 0x010087b1e1241ef4 0xc02010f63c2483de 0x500007f1f0001ffa 0x0a0000fe3e0003ff

def z535 : W := mkw 0x0df546da0dfe9f07 0x01bea8db41bfd3e0 0xfffdc7fe0fff9f07 0xffffb8ffc1fff3e0

def z536 : W := mkw 0x0045c181006a9080 0x0008b830200d5210 0xb8cdc18100ff9087 0xb719b830201ff210

def z537 : W := mkw 0x0000812140000000 0x0000102428000000 0x500005f1c0000002 0x0a0000be38000000

def z538 : W := mkw 0x36fff96d5edbe000 0x06dfff2dabdb7c00 0xbffff9fe0fffe005 0xf7ffff3fc1fffc00

def z539 : W := mkw 0x030a0690a3255e54 0x806140d21464abca 0xffce07f1ffffffff 0xfff9c0fe3fffffff

def z540 : W := mkw 0x031adf87b8e2318a 0x20635bf0f71c4631 0xd73fff8ff8e2739f 0xfae7fff1ff1c4e73

def z541 : W := mkw 0x24f5f9871cfab18a 0x249ebf30e39f5631 0x30f1f98e00fc0000 0x861e3f31c01f8000

def z542 : W := mkw 0x0db097df1db41f8f 0x21b612fbe3b683f1 0xfff007ff3ffc1f9e 0xfffe00ffe7ff83f3

def z543 : W := mkw 0x27ba2e00af916a50 0x84f745c015f22d4a 0xcf3e3e01ff03ffff 0x79e7c7c03fe07fff

def z544 : W := mkw 0x17ef2668e0000000 0x02fde4cd1c000000 0xe7fffc70c0000001 0xfcffff8e18000000

def z545 : W := mkw 0x081000020d900b03 0x0102000041b20160 0x000000000f000300 0x0000000001e00060

def z546 : W := mkw 0x3fffffffffffff07 0x07ffffffffffffe0 0xffffffffffffff07 0xffffffffffffffe0

def z547 : W := mkw 0x34f5f96d5cdaa000 0x069ebf2dab9b5400 0x30f1f9fe00fc0000 0x861e3f3fc01f8000

def z548 : W := mkw 0x034f0630e30dce74 0xc069e0c61c61b9ce 0x6fcc0470c71d8c60 0x2df9808e18e3b18c

def z549 : W := mkw 0x0fba064aaf914b53 0x81f740c955f2296a 0xcf3e060fff03ffff 0x79e7c0c1ffe07fff

def z550 : W := mkw 0x134fb725f0000000 0x0269f6e4be000000 0xc70ffe01f0000003 0x78e1ffc03e000000

def z551 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x2ffdf80007fd8000 0xa5ffbf0000ffb000

def z552 : W := mkw 0x26fff9051edbe000 0x04dfff20a3db7c00 0xbffffb8f3fffe007 0xf7ffff71e7fffc00

def z553 : W := mkw 0x0045c121404a80a0 0x4008b82428095014 0x0001c00000000000 0x0000380000000000

def z554 : W := mkw 0x0045000000000000 0x0008a00000000000 0xa0cdc00000000001 0xb419b80000000000

def z555 : W := mkw 0x26ef6800024be000 0x04dded0000497c00 0xa7fff8000003e001 0xf4ffff0000007c00

def z556 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x77cc07fff0000002 0x2ef980fffe000000

def z557 : W := mkw 0x04b000900cb41404 0x0096001201968280 0xfff005f00ffc1c06 0xfffe00be01ff8380

def z558 : W := mkw 0x05b0dfcf18e2318a 0x20b61bf9e31c4631 0xf7f3ffff38e2739f 0xfefe7fffe71c4e73

def z559 : W := mkw 0x17ef2668e0000000 0x02fde4cd1c000000 0xe7ce0671f0000003 0x7cf9c0ce3e000000

def z560 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x080dc001c0ff9ce5 0x0101b800381ff39c

def z561 : W := mkw 0x124fb125f0000000 0x0249f624be000000 0x903ffb8ff0000003 0xd207ff71fe000000

def z562 : W := mkw 0x26ff68900efff4a4 0x44dfed1201dffe94 0xaffff8000ffffce5 0xf5ffff0001ffff9c

def z563 : W := mkw 0x24e5200004188000 0x049ca40000831000 0x20c00000001c0000 0x0418000000038000

def z564 : W := mkw 0x030adf05b3436ad8 0xa0615be0b6686d5b 0xcf0ffe01ff03ffff 0x79e1ffc03fe07fff

def z565 : W := mkw 0x0055d9a758e2318a 0x200abb34eb1c4631 0xf0fffffff8e2739f 0xfe1fffffff1c4e73

def z566 : W := mkw 0x04b000000c900000 0x0096000001920000 0x20f0000000fc0000 0x841e0000001f8000

def z567 : W := mkw 0x17efb7fdf0241404 0x02fdf6ffbe048280 0xfffffffff0fc1c07 0xfffffffffe1f8380

def z568 : W := mkw 0x0900064a01000b03 0x012000c940200160 0x0000020e00000300 0x00000041c0000060

def z569 : W := mkw 0x0010d9b758e635ae 0x60021b36eb1cc6b5 0xd033fffff8e27fff 0xda067fffff1c4fff

def z570 : W := mkw 0x06fff98718e2318a 0x20dfff30e31c4631 0xb7fffb8f38e2739f 0xf6ffff71e71c4e73

def z571 : W := mkw 0x0055c9b348eeb5ae 0x600ab936691dd6b5 0xf8cdc5f1c8ffffff 0xbf19b8be391fffff

def z572 : W := mkw 0x000091871020118a 0x20001230e2040231 0x9002038f3802739f 0x52004071e7004e73

def z573 : W := mkw 0x020a0000a2014050 0x804140001440280a 0x800e0201f803f3ff 0x5001c0403f007e7f

def z574 : W := mkw 0x0df506fa4dbc9f27 0x41bea0df49b793e4 0xfffc07fecffd9f66 0xffff80ffd9ffb3ec

def z575 : W := mkw 0x0cb000da0cb41507 0x0196001b419682a0 0xf8f005fe00fc1c06 0xbf1e00bfc01f8380

def z576 : W := mkw 0x17ffffeffbe37bda 0xa2fffffdff7c6f7b 0xffffffffffe3ffff 0xfffffffffffc7fff

def z577 : W := mkw 0x26fff9b75efff5ae 0x64dfff36ebdffeb5 0xffffffffffffffff 0xffffffffffffffff

def z578 : W := mkw 0x091006da09a41f07 0x012200db413483e0 0xd03007fe08e01f06 0xda0600ffc11c03e0

def z579 : W := mkw 0x001018061880210a 0x20020300c3100421 0x80323a0f3802739f 0x50064741e7004e73

def z580 : W := mkw 0x0010588618e2318a 0x20020b10c31c4631 0x00323a0e38e2739c 0x40064741c71c4e73

def z581 : W := mkw 0x17ef2678e00c8424 0x42fde4cf1c019084 0x6fcc0470c01d8c60 0x2df9808e1803b18c

def z582 : W := mkw 0x05a006d800241404 0x00b400db00048280 0xfff007fe00fc1c06 0xfffe00ffc01f8380

def z583 : W := mkw 0x020a0000a3014a50 0x804140001460294a 0x080e0001ff03fffd 0x0101c0003fe07fff

def z584 : W := mkw 0x00454090006e94a4 0x4008a812000dd294 0xa8cdc00000ff9ce5 0xb519b800001ff39c

def z585 : W := mkw 0x0db01ede1db43f0f 0x21b603dbc3b687e1 0xfff23ffe3ffc7f1e 0xfffe47ffc7ff8fe3

def z586 : W := mkw 0x224fe921424be0a0 0x4449fd2428497c14 0x000ff801c003e0e1 0x0001ff0038007c1c

def z587 : W := mkw 0x07ef2600a0000000 0x00fde4c014000000 0xe7fffe01f0000003 0xfcffffc03e000000

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000020008001306 0x5000004001000260

def z589 : W := mkw 0x1ffffffffdf63f8f 0x23ffffffffbec7f1 0xfffffffffffe7f9f 0xffffffffffffcff3

def z590 : W := mkw 0x26ff28000e916000 0x04dfe50001d22c00 0xa7fff8000f006001 0xf4ffff0001e00c00

def z591 : W := mkw 0x26ff68820efbf102 0x04dfed1041df7e20 0xbffffb8e0ffff307 0xf7ffff71c1fffe60

def z592 : W := mkw 0x06ba00000e914000 0x00d7400001d22800 0xaffe00000fffe005 0xf5ffc00001fffc00

def z593 : W := mkw 0x0000d90510422088 0x20001b20a2084411 0x8003fa013802739f 0x50007f4027004e73

def z594 : W := mkw 0x0055d9b758eeb5ae 0x600abb36eb1dd6b5 0x30f1f9fe00fc0000 0x861e3f3fc01f8000

def z595 : W := mkw 0x1fef2678e5140e05 0x03fde4cf1ca281c0 0x6fcc0470c71c0c00 0x2df9808e18e38180

def z596 : W := mkw 0x24f568000cdaa000 0x049ead00019b5400 0xa0f3f80008fe6005 0xd41e7f00011fcc00

def z597 : W := mkw 0x17ba3e4eb880210a 0x22f747c9d7100421 0x07323a0e38006318 0x40e64741c7000c63

def z598 : W := mkw 0x04a0004800000000 0x0094000900000000 0x30f001fe00000000 0x861e003fc0000000

def z599 : W := mkw 0x0010d9871be37bda 0xa0021b30e37c6f7b 0x9833fb8f3fe3ffff 0xd3067f71e7fc7fff

def z600 : W := mkw 0x231a4e00afdbea50 0x846349c015fb7d4a 0xcf0e0601ffffffff 0x79e1c0c03fffffff

def z601 : W := mkw 0x0ca0005804140405 0x0194000b00828080 0x20c00070001c0000 0x0418000e00038000

def z602 : W := mkw 0x10009125f0000000 0x02001224be000000 0x00000001f0000000 0x000000003e000000

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x480c0400c0018c60 0x290180801800318c

def z604 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x0700000007000000 0x00e0000000e00000

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x8002020130000003 0x5000404026000000

def z606 : W := mkw 0x06ff680008c22000 0x00dfed0001184400 0xa7fff80008e26005 0xf4ffff00011c4c00

def z607 : W := mkw 0x031a4e82abe37bda 0xa06349d0557c6f7b 0xcf0e0601ffe3ffff 0x79e1c0c03ffc7fff

def z608 : W := mkw 0x0db0064a0d900b03 0x01b600c941b20160 0xaff0020e0ffc0304 0xf5fe0041c1ff8060

def z609 : W := mkw 0x030a9787b3215bda 0xa06152f0f6642b7b 0xdf0e078fff03ffff 0x7be1c0f1ffe07fff

def z610 : W := mkw 0x27ff6e480edbe000 0x04ffedc901db7c00 0xfffffffe0fffe007 0xffffffffc1fffc00

def z611 : W := mkw 0x020a000003014a50 0x804140000060294a 0x8f0e00000f03fffd 0x71e1c00001e07fff

def z612 : W := mkw 0x0000910510000088 0x20001220a2000011 0x0000000130000098 0x0000000026000013

def z613 : W := mkw 0x0db097df1db41f07 0x01b612fbe3b683e0 0xfff3ffff3ffc1f07 0xfffe7fffe7ff83e0

def z614 : W := mkw 0x0110df8719e23b8a 0x20221bf0e33c4771 0xdf33ff8f3fe27f9f 0xfbe67ff1e7fc4ff3

def z615 : W := mkw 0x05b006000d900a00 0x00b600c001b20140 0xeff006000ffc1f06 0xfdfe00c001ff83e0

def z616 : W := mkw 0x0145c7b1416e9ea4 0x4028b8f6282dd3d4 0xffcdc7f1cfff9fe7 0xfff9b8fe39fff3fc

def z617 : W := mkw 0x0045c1a1406a90a0 0x4008b834280d5214 0x900dc181c0e390e7 0x9201b830381c721c

def z618 : W := mkw 0x0000d9871062318a 0x20001b30e20c4631 0x1003fb8f3002739b 0x02007f71e6004e73

def z619 : W := mkw 0x1100976df1000a50 0x822012edbe20014a 0x500007fff0001ffa 0x0a0000fffe0003ff

def z620 : W := mkw 0x17efb77df00c8424 0x42fdf6efbe019084 0xfffffffff01d8c63 0xfffffffffe03b18c

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x000002013000139a 0x0000004026000273

def z622 : W := mkw 0x0000d1871062118a 0x20001a30e20c4231 0x9001c38f30e2139f 0x92003871e61c4273

def z623 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x500dc5f1c0039ce3 0x0a01b8be3800739c

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800040000001c06 0x3900008000000380

def z625 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x1000038f38e2739e 0x02000071e71c4e73

def z626 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x2fcc00000fffe004 0x25f9800001fffc00

def z627 : W := mkw 0x2fba2e4a0f916b03 0x05f745c941f22d60 0x07323a0e0f006300 0x40e64741c1e00c60

def z628 : W := mkw 0x0100069001241e04 0x002000d2002483c0 0xffc007f00ffc1f06 0xfff800fe01ff83e0

def z629 : W := mkw 0x0000000000000000 0x0000000000000000 0x9030038e00000002 0xd2060071c0000000

def z630 : W := mkw 0x030a0600a0000000 0x006140c014000000 0x0702020030000000 0x40e0404006000000

def z631 : W := mkw 0x0045c121404a8000 0x0008b82428095000 0xf8cdc5f1c0ff8007 0xbf19b8be381ff000

def z632 : W := mkw 0x0055c1b348ee95a6 0x400ab836691dd2b4 0xf8fdc7ffc8ff9fe7 0xff1fb8fff91ff3fc

def z633 : W := mkw 0x081000920cb41507 0x01020012419682a0 0x0000000000fc0000 0x00000000001f8000

def z634 : W := mkw 0x0000d90510422088 0x20001b20a2084411 0x9033fb8f3002609b 0xd2067f71e6004c13

def z635 : W := mkw 0x0000c191006e94a4 0x40001832200dd294 0x9801c18100ff9ce7 0x93003830201ff39c

def z636 : W := mkw 0x0000000002014000 0x0000000000402800 0x080000000f03e004 0x0100000001e07c00

def z637 : W := mkw 0x04f5c1b14cfe94a4 0x409eb836299fd294 0xfffdc5f1cfff9ce7 0xffffb8be39fff39c

def z638 : W := mkw 0x031a1e06bb816b5a 0xa06343c0d7702d6b 0xcf3e3e0fff03ffff 0x79e7c7c1ffe07fff

def z639 : W := mkw 0x004581b140241404 0x0008b03628048280 0xf8cdc5f1c0fc1c07 0xbf19b8be381f8380

def z640 : W := mkw 0x17ef2668e0000000 0x02fde4cd1c000000 0xf7fc07fec0000002 0xfeff80ffd8000000

def z641 : W := mkw 0x001000000c900000 0x0002000001920000 0x080000000ffc0004 0x0100000001ff8000

def z642 : W := mkw 0x17ffffeff8e2318a 0x22fffffdff1c4631 0xf7fffffff0e00003 0xfefffffffe1c0000

def z643 : W := mkw 0x00004000004a8000 0x0000080000095000 0x0800000000ff8004 0x01000000001ff000

def z644 : W := mkw 0x034f4600a34bca50 0x8069e8c01469794a 0xefcfc601ffffffff 0xfdf9f8c03fffffff

def z645 : W := mkw 0x2fffffdf1fffff8f 0x25fffffbe3fffff1 0xffffffff3fffff9f 0xffffffffe7fffff3

def z646 : W := mkw 0x110097eff020118a 0x222012fdfe040231 0x500007fff000139a 0x0a0000fffe000273

def z647 : W := mkw 0x224f6800024be000 0x0449ed0000497c00 0x8f0ff8000f03e005 0x71e1ff0001e07c00

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x8002000008026005 0x5000400001004c00

def z649 : W := mkw 0x0cf5c1fb4cfe95a7 0x419eb83f699fd2b4 0xf8fdc5ffc0ff9ce7 0xbf1fb8bff81ff39c

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00c0401c0000003 0x3801808038000000

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8c0000000fc0004 0xb5180000001f8000

def z652 : W := mkw 0x0000009000241404 0x0000001200048280 0x500005f000001c02 0x0a0000be00000380

def z653 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x70c1c5f1c0fc1ce2 0x8e1838be381f839c

def z654 : W := mkw 0x1fffb7fffcb41507 0x03fff6ffff9682a0 0xf7fffffff0fc0003 0xfefffffffe1f8000

def z655 : W := mkw 0x05e5c7f9406e94a4 0x40bcb8ff280dd294 0xfffdc7ffc0ff9ce7 0xffffb8fff81ff39c

def z656 : W := mkw 0x001008020880210a 0x2002010041100421 0x0000000008006318 0x0000000001000c63

def z657 : W := mkw 0x17ffb7eff8a01102 0x02fff6fdff140220 0xf7fffffff8e01307 0xfeffffffff1c0260

def z658 : W := mkw 0x0055d9b758eeb5ae 0x600abb36eb1dd6b5 0xb0f3fbff38fe739f 0xd61e7f7fe71fce73

def z659 : W := mkw 0x0100060001000a00 0x002000c000200140 0xcf0c0601cf039fe7 0x79e180c039e073fc

def z660 : W := mkw 0x034f8721e3014a50 0x8069f0e43c60294a 0xffcfc7f1ff03ffff 0xfff9f8fe3fe07fff

def z661 : W := mkw 0x0045c121404a80a0 0x4008b82428095014 0xc80dc401c0039ce7 0x3901b8803800739c

def z662 : W := mkw 0x021ad9871ae3718a 0x20435b30e35c6e31 0x9f3ffb8f3fe3f39f 0xf3e7ff71e7fc7e73

def z663 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0xc70e0601ff00631b 0x78e1c0c03fe00c63

def z664 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000802739c 0x0000000001004e73

def z665 : W := mkw 0x01000600a1000a50 0x802000c01420014a 0xc0020601f8027fff 0x580040c03f004fff

def z666 : W := mkw 0x0045c1b1436fdef4 0xc008b836286dfbde 0xf8cdc5f1cfffffff 0xbf19b8be39ffffff

def z667 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x870202013f02739f 0x50e0404027e04e73

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000401c0001ce2 0x080000803800039c

def z669 : W := mkw 0x024fc121e24bc0f0 0xc049f8243c49781e 0x000fc001f003e0f9 0x0001f8003e007c1f

def z670 : W := mkw 0x0fba06da0fb55f07 0x01f740db41f6abe0 0xfffe07fe0fffff07 0xffffc0ffc1ffffe0

def z671 : W := mkw 0x0010d90518c22000 0x00021b20a3184400 0x9033fb8f38e26007 0xd2067f71e71c4c00

def z672 : W := mkw 0x031adf87bbe37bda 0xa0635bf0f77c6f7b 0x9733fb8f3fe2739f 0xd2e67f71e7fc4e73

def z673 : W := mkw 0x0000009000241404 0x0000001200048280 0x0800000000fc1c04 0x01000000001f8380

def z674 : W := mkw 0x0db0065a0d940f07 0x01b600cb41b281e0 0x6ff0067e0f1c0f00 0x6dfe00cfc1e381e0

def z675 : W := mkw 0x36fff925fedbe000 0x06dfff24bfdb7c00 0xaffff801ffffe005 0xf5ffff003ffffc00

def z676 : W := mkw 0x020ad905b24360d8 0xa0415b20b6486c1b 0x000ff801f003e0f9 0x0001ff003e007c1f

def z677 : W := mkw 0x1fff26faedb41f07 0x03ffe4df5db683e0 0xfffc07fecffc1f06 0xffff80ffd9ff83e0

def z678 : W := mkw 0x0045812140000000 0x0008b02428000000 0x000dc001c0000001 0x0001b80038000000

def z679 : W := mkw 0x124f2020e0000000 0x0249e4041c000000 0x000c0000c0000000 0x0001800018000000

def z680 : W := mkw 0x00450030400c8424 0x4008a00608019084 0xe8cc0471c01f9ce7 0x3d19808e3803f39c

def z681 : W := mkw 0x020a0000a2014050 0x804140001440280a 0x0002000030006018 0x0000400006000c03

def z682 : W := mkw 0x0da0064805100a01 0x01b400c900a20140 0x0700000007000000 0x00e0000000e00000

def z683 : W := mkw 0x0000000000000000 0x0000000000000000 0x0002000130026099 0x0000400026004c13

def z684 : W := mkw 0x2fef2658071dce05 0x05fde4cb00e3b9c0 0x6fcc0470071d8c00 0x2df9808e00e3b180

def z685 : W := mkw 0x0db04eda0df63f8f 0x21b609db41bec7f1 0xfff007fe0ffe7f9e 0xfffe00ffc1ffcff3

def z686 : W := mkw 0x030a0600a1000a00 0x006140c014200140 0xcf0e0601ff001f07 0x79e1c0c03fe003e0

def z687 : W := mkw 0x06efe1b1406e94a4 0x40ddfc36280dd294 0xfffffdf1c0ff9ce7 0xffffffbe381ff39c

def z688 : W := mkw 0x0000818100201080 0x0000103020040210 0x1000018100001082 0x0200003020000210

def z689 : W := mkw 0x26ba68000edbe000 0x04d74d0001db7c00 0x0f3238000fffe004 0x41e6470001fffc00

def z690 : W := mkw 0x201048000fdbea50 0x8402090001fb7d4a 0x080000000ffffffc 0x0100000001ffffff

def z691 : W := mkw 0x17efe7f9e06e94a4 0x42fdfcff3c0dd294 0xffcdc5f1c0ff9ce7 0xbff9b8be381ff39c

def z692 : W := mkw 0x2010d9871efbf18a 0x24021b30e3df7e31 0x9833fb8f3ffff39f 0xd3067f71e7fffe73

def z693 : W := mkw 0x14f5f9ef58e2318a 0x229ebf3deb1c4631 0x30f1f9fe00e00000 0x861e3f3fc01c0000

def z694 : W := mkw 0x0000480000422000 0x0000090000084400 0x0003f80000026001 0x00007f0000004c00

def z695 : W := mkw 0x225f68000edbe000 0x044bed0001db7c00 0x080ff8000fffe005 0x0101ff0001fffc00

def z696 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x9031f98f00e21087 0x92063f31e01c4210

def z697 : W := mkw 0x0010188618a0310a 0x20020310c3140621 0x90323b8e38e0731e 0xd2064771c71c0e63

def z698 : W := mkw 0x0000400000420000 0x0000080000084000 0x8001c00000e20005 0x90003800001c4000

def z699 : W := mkw 0x034f0630e30dce74 0xc069e0c61c61b9ce 0xefce0671ff1fffff 0x7df9c0ce3fe3ffff

def z700 : W := mkw 0x26ffe9214edbe0a0 0x44dffd2429db7c14 0xaffff801cfffe0e5 0xf5ffff0039fffc1c

def z701 : W := mkw 0x0010480008c22000 0x0002090001184400 0x0000000008e26004 0x00000000011c4c00

def z702 : W := mkw 0x04f540000cda8000 0x009ea800019b5000 0xaffdc0000fff8005 0xf5ffb80001fff000

def z703 : W := mkw 0x124ff125f04a80a0 0x4249fe24be095014 0x000ff801f00380e1 0x0001ff003e00701c

def z704 : W := mkw 0x37ffffeffefbf18a 0x26fffffdffdf7e31 0xfffffffffffff39f 0xfffffffffffffe73

def z705 : W := mkw 0x081000920db41f07 0x0102001241b683e0 0xf8c005f00ffc1f06 0xbf1800be01ff83e0

def z706 : W := mkw 0x0db0dfdf1df63f8f 0x21b61bfbe3bec7f1 0xfff1fffe0ffc1f06 0xfffe3fffc1ff83e0

def z707 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fdfffec0000002 0xfeffbfffd8000000

def z708 : W := mkw 0x0db006da0db41f8f 0x21b600db41b683f1 0xfff007fe0ffc1f9e 0xfffe00ffc1ff83f3

def z709 : W := mkw 0x26ff6800aedbe050 0x84dfed0015db7c0a 0xeffffc01fffffcff 0xfdffff803fffff9f

def z710 : W := mkw 0x281048920cfeb507 0x05020912419fd6a0 0x0000000000fc0000 0x00000000001f8000

def z711 : W := mkw 0x2b4f6eda036fff07 0x0569eddb406dffe0 0x500ffffe0003ff03 0x0a01ffffc0007fe0

def z712 : W := mkw 0x1fefb76df5100a01 0x03fdf6edbea20140 0xf7fffffff7000003 0xfefffffffee00000

def z713 : W := mkw 0x0000c19100661484 0x00001832200cc290 0xf8cdc5f1c0ff9ce7 0xbf19b8be381ff39c

def z714 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xbff003fe0ffc0304 0xf7fe007fc1ff8060

def z715 : W := mkw 0x2fba2e4aaf916b53 0x85f745c955f22d6a 0x07323a0e3f006318 0x40e64741c7e00c63

def z716 : W := mkw 0x000081b1402414a4 0x4000103628048294 0xf8cc05f1c0ff9ce7 0xbf1980be381ff39c

def z717 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff207ff3ffc1f07 0xfffe40ffe7ff83e0

def z718 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff207fe0ffe7f07 0xfffe40ffc1ffcfe0

def z719 : W := mkw 0x17ff6eeae8e2318a 0x22ffeddd5d1c4631 0x67cc0470c8e2739c 0x2cf9808e191c4e73

def z720 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x77f007fe0ffc1f02 0xcefe00ffc1ff83e0

def z721 : W := mkw 0x0000910510000000 0x00001220a2000000 0xf0f3ffff30000003 0xfe1e7fffe6000000

def z722 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0xffce07f1ff03ffff 0xfff9c0fe3fe07fff

def z723 : W := mkw 0x0010d90718c2218a 0x20021b20e3184431 0x9033fb8f3802639b 0xd2067f71e7004c73

def z724 : W := mkw 0x225f68000edbe000 0x044bed0001db7c00 0x8f0ff8000fffe005 0x71e1ff0001fffc00

def z725 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8fdc7ffc0ff9ce7 0xff1fb8fff81ff39c

def z726 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x9833fb8f38e3ffff 0xd3067f71e71c7fff

def z727 : W := mkw 0x15e5b76d50000000 0x02bcb6edaa000000 0xf7fdffffc0000003 0xfeffbffff8000000

def z728 : W := mkw 0x05b006ca0cb01102 0x00b600d941960220 0xfff007fe0ffc1306 0xfffe00ffc1ff8260

def z729 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x470e0601ff03fffb 0x48e1c0c03fe07fff

def z730 : W := mkw 0x004500b0402c9424 0x4008a01608059284 0x78cc05f0c0fd8c60 0xaf1980be181fb18c

def z731 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff007ff0ffe1f87 0xfffe00ffe1ffc3f0

def z732 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x37f001fe07fc0000 0x86fe003fc0ff8000

def z733 : W := mkw 0x004540b0406e94a4 0x4008a816080dd294 0xe8cc0471c0ff9ce7 0x3d19808e381ff39c

def z734 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x9033fb8e38e2631d 0xd2067f71c71c4c63

def z735 : W := mkw 0x25f56e00addaaa50 0x84beadc015bb554a 0x60f1fe01f0fc1ffa 0x8c1e3fc03e1f83ff

def z736 : W := mkw 0x124fb125f0000000 0x0249f624be000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z737 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0xd833ff8f38e27f9f 0xfb067ff1e71c4ff3

def z738 : W := mkw 0x0000910510000000 0x00001220a2000000 0x9033fb8f3800631b 0xd2067f71e7000c63

def z739 : W := mkw 0x17efb76df2014050 0x82fdf6edbe40280a 0xfffffffff003fcff 0xfffffffffe007f9f

def z740 : W := mkw 0x17efb76df1000a00 0x02fdf6edbe200140 0xf7fffffff0001f03 0xfefffffffe0003e0

def z741 : W := mkw 0x04b000480c900000 0x0096000901920000 0xbff001fe0ffc0004 0xf7fe003fc1ff8000

def z742 : W := mkw 0x1a5fb1b7fdb41f07 0x034bf636ffb683e0 0x080ff801fffc1f05 0x0101ff003fff83e0

def z743 : W := mkw 0x004540b0406e9424 0x4008a816080dd284 0xf8cdc5f0c0ff9c67 0xbf19b8be181ff38c

def z744 : W := mkw 0x37efb76df719ca50 0x86fdf6edbee3394a 0xffffffffff1fffff 0xffffffffffe3ffff

def z745 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0x70f1fdffc0000002 0x8e1e3fbff8000000

def z746 : W := mkw 0x0eba00daaeb55557 0x81d7401b55d6aaaa 0x30fe01fff0ffe0f9 0x861fc03ffe1ffc1f

def z747 : W := mkw 0x15e5b76df1000a50 0x82bcb6edbe20014a 0x70f1fffff0001ffa 0x8e1e3ffffe0003ff

def z748 : W := mkw 0x04e5204800000000 0x009ca40900000000 0x30f1f9fe00000000 0x861e3f3fc0000000

def z749 : W := mkw 0x0010d9b758eeb5ae 0x60021b36eb1dd6b5 0xd833fffff8ffffff 0xdb067fffff1fffff

def z750 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff207fe3ffc7f1e 0xfffe40ffc7ff8fe3

def z751 : W := mkw 0x06ff20000e914000 0x00dfe40001d22800 0xaffff8000fffe005 0xf5ffff0001fffc00

def z752 : W := mkw 0x0045c131404e84a4 0x4008b8262809d094 0xe8cdc471c0ff8ce5 0xbd19b88e381ff19c

def z753 : W := mkw 0x2010d9871cfab18a 0x24021b30e39f5631 0x9033fb8f38fe739f 0xd2067f71e71fce73

def z754 : W := mkw 0x05a006d801241e04 0x00b400db002483c0 0xfff007fe0ffc1f06 0xfffe00ffc1ff83e0

def z755 : W := mkw 0x0010d90718c2218a 0x20021b20e3184431 0x8033fa0f3802739f 0x50067f41e7004e73

def z756 : W := mkw 0x324ff925524be000 0x0649ff24aa497c00 0x000ff8000003e001 0x0001ff0000007c00

def z757 : W := mkw 0x031adf87bbe37bda 0xa0635bf0f77c6f7b 0x5f3dfd8ec7e18c60 0xabe7bfb1d8fc318c

def z758 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffffa000ffff307 0xf5ffff4001fffe60

def z759 : W := mkw 0x17efb76df1000a00 0x02fdf6edbe200140 0xf7ffffffff000303 0xfeffffffffe00060

def z760 : W := mkw 0x17efb76df2014050 0x82fdf6edbe40280a 0xffffffffff03e0ff 0xffffffffffe07c1f

def z761 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff007fe0ffe7f9e 0xfffe00ffc1ffcff3

def z762 : W := mkw 0x0010d99718eeb5ae 0x60021b32e31dd6b5 0xf8f3ffff38ffffff 0xff1e7fffe71fffff

def z763 : W := mkw 0x07aa974db0000000 0x00f552e9b6000000 0xf7fffffff0000003 0xfefffffffe000000

def z764 : W := mkw 0x221a48000edbe000 0x0443490001db7c00 0x8f3ff8000fffe005 0xf1e7ff0001fffc00

def z765 : W := mkw 0x1100976df1000a50 0x822012edbe20014a 0xd033fffff8027fff 0xda067fffff004fff

def z766 : W := mkw 0x0010d9b758e635ae 0x60021b36eb1cc6b5 0x9033fbff38e2739f 0xd2067f7fe71c4e73

def z767 : W := mkw 0x0010d9a758e231aa 0x60021b34eb1c4635 0x9033fb8ff8e273ff 0xd2067f71ff1c4e7f

def z768 : W := mkw 0x004581b140241404 0x0008b03628048280 0xf8cdc5f1c0ff9ce7 0xbf19b8be381ff39c

def z769 : W := mkw 0x0010580618c2210a 0x20020b00c3184421 0x0033fa0e38e06318 0xc0067f41c71c0c63

def z770 : W := mkw 0x001099071880210a 0x20021320e3100421 0x0033fa0f38006319 0x40067f41e7000c63

def z771 : W := mkw 0x034f9725f0000000 0x0069f2e4be000000 0xf7fffffff0000003 0xfefffffffe000000

def z772 : W := mkw 0x0010489208eeb5ae 0x60020912411dd6b5 0x0000000000fc0000 0x00000000001f8000

def z773 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x2ffdf8000fffe004 0xa5ffbf0001fffc00

def z774 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xbffffb8e0fffe007 0xf7ffff71c1fffc00

def z775 : W := mkw 0x0da0df5d15562e8d 0x21b41beba2aac5d1 0x6fc3fc71371e6c99 0x2df87f8e26e3cd93

def z776 : W := mkw 0x26ff6800aedbe050 0x84dfed0015db7c0a 0xaffff8003fffe01d 0xf5ffff0007fffc03

def z777 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x7ff007fe07fc1f02 0xaffe00ffc0ff83e0

def z778 : W := mkw 0x001099071880210a 0x20021320e3100421 0x9033fb8f3802739f 0xd2067f71e7004e73

def z779 : W := mkw 0x0010998718a0318a 0x20021330e3140631 0x9033fb8f3800739b 0xd2067f71e7000e73

def z780 : W := mkw 0x0db006daadb41f57 0x81b600db55b683ea 0xfffc07ffffff9fff 0xffff80fffffff3ff

def z781 : W := mkw 0x37efb76df4188000 0x06fdf6edbe831000 0xf7fffffff01c0003 0xfefffffffe038000

def z782 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x1033fb8f3802739b 0x42067f71e7004e73

def z783 : W := mkw 0x004500b0402c9424 0x4008a01608059284 0xf8cc05f1c0ff9ce7 0xbf1980be381ff39c

def z784 : W := mkw 0x26efb1871639d18a 0x24ddf630e2c73a31 0x3fcc038f371d939a 0x27f98071e6e3b273

def z785 : W := mkw 0x1fef2678e7154e55 0x83fde4cf1ce2a9ca 0x6fcc0470c71d8c60 0x2df9808e18e3b18c

def z786 : W := mkw 0x020a000002014000 0x0041400000402800 0xcf0e0601ff03ffff 0x79e1c0c03fe07fff

def z787 : W := mkw 0x2b1a4e92afffff57 0x856349d255ffffea 0xcf0e0601ffffffff 0x79e1c0c03fffffff

def z788 : W := mkw 0x0010489208e6358e 0x20020912411cc6b1 0x0800000008fe7f9c 0x01000000011fcff3

def z789 : W := mkw 0x36ff68684edbe000 0x06dfed0d09db7c00 0xaffff8700fffe005 0xf5ffff0e01fffc00

def z790 : W := mkw 0x0db00eda0db43f0f 0x21b601db41b687e1 0xfff007fe0ffc7f1e 0xfffe00ffc1ff8fe3

def z791 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffff8000ffff39d 0xf5ffff0001fffe73

def z792 : W := mkw 0x04b000000c900000 0x0096000001920000 0xaff3f8000ffc0005 0xf5fe7f0001ff8000

def z793 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xffffffffff019f67 0xffffffffffe033ec

def z794 : W := mkw 0x000091871020118a 0x20001230e2040231 0x9033fb8f3802739f 0xd2067f71e7004e73

def z795 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x1033fb8f38e26399 0xc2067f71e71c4c73

def z796 : W := mkw 0x0045d1b5506e94a4 0x4008ba36aa0dd294 0xf8fdfdffc0ff9ce7 0xbf1fbfbff81ff39c

def z797 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xb7fffbfe30000001 0xf6ffff7fc6000000

def z798 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xeffffe01ffffffff 0xfdffffc03fffffff

def z799 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xfffffffff7019ffb 0xfffffffffee033ff

def z800 : W := mkw 0x17efb76df1000a50 0x82fdf6edbe20014a 0xf7fffffff8027fff 0xfeffffffff004fff

def z801 : W := mkw 0x37efb76df6114000 0x06fdf6edbec22800 0xf7fffffff7000003 0xfefffffffee00000

def z802 : W := mkw 0x004500b0402c9424 0x4008a01608059284 0x68cc0470c0fd9c64 0x2d19808e181fb38c

def z803 : W := mkw 0x09104e920df63f8f 0x212209d241bec7f1 0xcf0206013ffe7f9f 0x79e040c027ffcff3

def z804 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x9f33fb8f3fe2739f 0xf3e67f71e7fc4e73

def z805 : W := mkw 0x37ef2668e719ca50 0x86fde4cd1ce3394a 0x6fcc0470c71d8c60 0x2df9808e18e3b18c

def z806 : W := mkw 0x004540b0406e94a4 0x4008a816080dd294 0x68cc0470c0fd8c60 0x2d19808e181fb18c

def z807 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fffffff800631b 0xfeffffffff000c63

def z808 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8cdc5f1c0fd8c63 0xbf19b8be381fb18c

def z809 : W := mkw 0x16efb16df0000000 0x02ddf62dbe000000 0x30f3f9fe30000000 0x861e7f3fc6000000

def z810 : W := mkw 0x06ff60000cda8000 0x00dfec00019b5000 0xaffff8000fff8005 0xf5ffff0001fff000

def z811 : W := mkw 0x26baa9b14eb574a4 0x44d7553629d6ae94 0x57323df1cf007ce2 0x4ae647be39e00f9c

def z812 : W := mkw 0x17efb76df0000050 0x82fdf6edbe00000a 0xf7fffffff00000fb 0xfefffffffe00001f

def z813 : W := mkw 0x37ba3e4cbf916a50 0x86f747c997f22d4a 0x07323a0e3f006318 0x40e64741c7e00c63

def z814 : W := mkw 0x0df5c76b4dda8ba3 0x41beb8ed69bb5174 0x073dc20fcf0383e1 0x40e7b841f9e0707c

def z815 : W := mkw 0x1000916d50000000 0x0200122daa000000 0x9033fbff30000003 0xd2067f7fe6000000

def z816 : W := mkw 0x0045d1b5506e94a4 0x4008ba36aa0dd294 0xf8fffffff8ffffff 0xff1fffffff1fffff

def z817 : W := mkw 0x00551836588ca52e 0x600aa306cb1194a5 0x68fe3e7ef81def78 0x6d1fc7cfdf03bdef

def z818 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff005fe0ffc0c04 0xfffe00bfc1ff8180

def z819 : W := mkw 0x281048920fffff8f 0x2502091241fffff1 0x080000000fffff9c 0x0100000001fffff3

def z820 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaff3f8000ffc6004 0xf5fe7f0001ff8c00

def z821 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0xd033ff8ff8e27fff 0xda067ff1ff1c4fff

def z822 : W := mkw 0x034fc7b1e36fdef4 0xc069f8f63c6dfbde 0x37c3c3f03ffc6318 0xc6f8787e07ff8c63

def z823 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x0033fa0f38e2739d 0x40067f41e71c4e73

def z824 : W := mkw 0x0010d99718e6358e 0x20021b32e31cc6b1 0xd033ffff38e27f9f 0xda067fffe71c4ff3

def z825 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xeffffc01cfffe007 0xfdffff8039fffc00

def z826 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x2fcff8000fffe005 0x25f9ff0001fffc00

def z827 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0x30f3f9ff30000001 0x861e7f3fe6000000

def z828 : W := mkw 0x124ff125f24bc0f0 0xc249fe24be49781e 0x000ff801f003e0f9 0x0001ff003e007c1f

def z829 : W := mkw 0x0010489208eeb5ae 0x60020912411dd6b5 0x0000000008fe739c 0x00000000011fce73

def z830 : W := mkw 0x0010588618e2318a 0x20020b10c31c4631 0x8033fa0e38e2739d 0xd0067f41c71c4e73

def z831 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x0f3ff8000fffe005 0x41e7ff0001fffc00

def z832 : W := mkw 0x26ba68000ed36000 0x04d74d0001da6c00 0xaff3f8000ffe6005 0xf5fe7f0001ffcc00

def z833 : W := mkw 0x031a4e92abeffffe 0xe06349d2557dffff 0xcf0e0601ffffffff 0x79e1c0c03fffffff

def z834 : W := mkw 0x15e5b76df0000000 0x02bcb6edbe000000 0x70f1fdfec0000000 0x8e1e3fbfd8000000

def z835 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x37fffbfff0000001 0xc6ffff7ffe000000

def z836 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xeffffc000ffffc07 0xfdffff8001ffff80

def z837 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0xb8f3fb8f38fe739f 0xf71e7f71e71fce73

def z838 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8cdc5f0c0ff8c65 0xbf19b8be181ff18c

def z839 : W := mkw 0x05a0974d10000000 0x00b412e9a2000000 0xf7f1fffe00000002 0xfefe3fffc0000000

def z840 : W := mkw 0x06ef6000024bc000 0x00ddec0000497800 0xaffff8000fffe005 0xf5ffff0001fffc00

def z841 : W := mkw 0x190097ff51241f07 0x032012ffea2483e0 0x500007fe00001f02 0x0a0000ffc00003e0

def z842 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8cdc7f1f0ff9fff 0xbf19b8fe3e1ff3ff

def z843 : W := mkw 0x14e5b16df0000000 0x029cb62dbe000000 0x30f1f9fff0000000 0x861e3f3ffe000000

def z844 : W := mkw 0x14e5b16d53014a50 0x829cb62daa60294a 0x38f1f9fe0f03fffc 0x871e3f3fc1e07fff

def z845 : W := mkw 0x26ef6000065bc000 0x04ddec0000cb7800 0xaffff80007ff8005 0xf5ffff0000fff000

def z846 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xfffffffff0018c63 0xfffffffffe00318c

def z847 : W := mkw 0x24f568000cdaa000 0x049ead00019b5400 0xaff3f8000ffe6005 0xf5fe7f0001ffcc00

def z848 : W := mkw 0x0045d1b5506e94ac 0x6008ba36aa0dd295 0xf8cdc5f1f0ff9cff 0xbf19b8be3e1ff39f

def z849 : W := mkw 0x001048920beffffe 0xe0020912417dffff 0x080000000ffffffc 0x0100000001ffffff

def z850 : W := mkw 0x090097df11241f07 0x012012fbe22483e0 0x500007ff30001f02 0x0a0000ffe60003e0

def z851 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x4f0c0601ff03fffe 0x29e180c03fe07fff

def z852 : W := mkw 0x110097fdf1241ef4 0xc22012ffbe2483de 0x500007fff0001ffa 0x0a0000fffe0003ff

def z853 : W := mkw 0x16efb16d52014000 0x02ddf62daa402800 0xbffff9fe0f03e005 0xf7ffff3fc1e07c00

def z854 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xa7fff8000ffc6001 0xf4ffff0001ff8c00

def z855 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xfffffffff0038007 0xfffffffffe007000

def z856 : W := mkw 0x3110df6dfedbe000 0x06221bedbfdb7c00 0x580007ffffffe006 0x0b0000fffffffc00

def z857 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x78cc05f1c0ff9ce6 0x2f1980be381ff39c

def z858 : W := mkw 0x0045912550000000 0x0008b224aa000000 0xf8fffffff803ffff 0xff1fffffff007fff

def z859 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffffa003fffe31d 0xf5ffff4007fffc63

def z860 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x9033fb8e38e0731e 0xd2067f71c71c0e63

def z861 : W := mkw 0x26ff68000edbe050 0x84dfed0001db7c0a 0xaffff8000fffe0fd 0xf5ffff0001fffc1f

def z862 : W := mkw 0x081048920cf6358f 0x21020912419ec6b1 0x0000000008fe739c 0x00000000011fce73

def z863 : W := mkw 0x0010d99718eeb5ae 0x60021b32e31dd6b5 0xd83fff8ff8ffffff 0xfb07fff1ff1fffff

def z864 : W := mkw 0x17efb76df0088000 0x02fdf6edbe011000 0xfffffffff01d8003 0xfffffffffe03b000

def z865 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8cdc5f0c0fd9c66 0xbf19b8be181fb38c

def z866 : W := mkw 0x05a0974d11000a00 0x00b412e9a2200140 0xfff3ffff3f027f9f 0xfffe7fffe7e04ff3

def z867 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xb7f3fbff30000003 0xd6fe7f7fe6000000

def z868 : W := mkw 0x324ff925f24be0a0 0x4649ff24be497c14 0x000ff801f003e0e1 0x0001ff003e007c1c

def z869 : W := mkw 0x0000912550000000 0x00001224aa000000 0xd033fffff0000003 0xda067ffffe000000

def z870 : W := mkw 0x190097fff1241f57 0x832012fffe2483ea 0x500007fff0001ffa 0x0a0000fffe0003ff

def z871 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xfffffffff0001c07 0xfffffffffe000380

def z872 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0x30f3fbfe30000000 0xc61e7f7fc6000000

def z873 : W := mkw 0x16efb16df0000000 0x02ddf62dbe000000 0xf0fffdfff0000003 0xbe1fffbffe000000

def z874 : W := mkw 0x17efb76df0088020 0x42fdf6edbe011004 0xf7fffffff0018063 0xfefffffffe00300c

def z875 : W := mkw 0x15e5b76d50000000 0x02bcb6edaa000000 0x77f1fdfe00000000 0xaefe3fbfc0000000

def z876 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x573ffffff0000003 0x4ae7fffffe000000

def z877 : W := mkw 0x0cb000da0db41f07 0x0196001b41b683e0 0xbff001fe0ffc1f04 0xf7fe003fc1ff83e0

def z878 : W := mkw 0x17efb76df1000a00 0x02fdf6edbe200140 0xffffffffff027f9f 0xffffffffffe04ff3

def z879 : W := mkw 0x15a0976df0000000 0x02b412edbe000000 0xf7f3fffff0000003 0xfefe7ffffe000000

def z880 : W := mkw 0x004540b0406e94a4 0x4008a816080dd294 0xe8cdc470c0ff9ce5 0xbd19b88e181ff39c

def z881 : W := mkw 0x130a976df0000000 0x026152edbe000000 0xd73ffffff0000003 0xfae7fffffe000000

def z882 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff005fe07fc1c06 0xbffe00bfc0ff8380

def z883 : W := mkw 0x26ff6800aedbe050 0x84dfed0015db7c0a 0xaffff800cfffe065 0xf5ffff0019fffc0c

def z884 : W := mkw 0x2eff684a0edbe103 0x05dfed0941db7c20 0xaffff80e0fffe005 0xf5ffff01c1fffc00

def z885 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xffffffffff000007 0xffffffffffe00000

def z886 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xf7fffffff7000003 0xfefffffffee00000

def z887 : W := mkw 0x0045d1b7506e95ae 0x6008ba36ea0dd2b5 0xf8fffffff0ff9fff 0xff1ffffffe1ff3ff

def z888 : W := mkw 0x0045d9b5506eb4ac 0x6008bb36aa0dd695 0xf8cdfdf1c0ff9ce7 0xbf19bfbe381ff39c

def z889 : W := mkw 0x004581b1402c94a4 0x4008b03628059294 0xf8cc05f1c0fd9ce6 0xbf1980be381fb39c

def z890 : W := mkw 0x07ef2648a0000000 0x00fde4c914000000 0xf7fffffff0000003 0xfefffffffe000000

def z891 : W := mkw 0x0db006da0cb41507 0x01b600db419682a0 0xfff007fe0ffc0006 0xfffe00ffc1ff8000

def z892 : W := mkw 0x00454030404e8424 0x4008a8060809d084 0x68cc0470c0ff8c64 0x2d19808e181ff18c

def z893 : W := mkw 0x081048920dfebfaf 0x6102091241bfd7f5 0x080000000ffffffc 0x0100000001ffffff

def z894 : W := mkw 0x06ff68000cd22000 0x00dfed00019a4400 0xaffff8000ffe6005 0xf5ffff0001ffcc00

def z895 : W := mkw 0x0045d9b7506eb5ae 0x6008bb36ea0dd6b5 0xf8cffffff0ffffff 0xbf19fffffe1fffff

def z896 : W := mkw 0x17efb76df2014000 0x02fdf6edbe402800 0xffffffffff03fce7 0xffffffffffe07f9c

def z897 : W := mkw 0x0cb000da0cb41507 0x0196001b419682a0 0x37f001fe0ffc0000 0xc6fe003fc1ff8000

def z898 : W := mkw 0x24f568000edbe000 0x049ead0001db7c00 0xaff1f8000fffe004 0xf5fe3f0001fffc00

def z899 : W := mkw 0x2b1a4e920fffff07 0x056349d241ffffe0 0xcf0e06000fffff07 0x79e1c0c001ffffe0

def z900 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff007ff3ffc1f9e 0xfffe00ffe7ff83f3

def z901 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffff8010ffff087 0xf5ffff0021fffe10

def z902 : W := mkw 0x26ff68204edbe020 0x44dfed0409db7c04 0xaffff800cfffe065 0xf5ffff0019fffc0c

def z903 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0xb0f3f9fe00000001 0xd61e7f3fc0000000

def z904 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xfffffdf00fffe007 0xffffffbe01fffc00

def z905 : W := mkw 0x281048920fffffa7 0x4502091241fffff4 0x080000000fffffe4 0x0100000001fffffc

def z906 : W := mkw 0x0010d99718e6358e 0x20021b32e31cc6b1 0xb0f3fbff38fe739f 0xd61e7f7fe71fce73

def z907 : W := mkw 0x0045d9b5506eb4ac 0x6008bb36aa0dd695 0xf8cffff1f8ffffff 0xff19fffe3f1fffff

def z908 : W := mkw 0x0045d1b5506e94a4 0x4008ba36aa0dd294 0xf8cdc7fff0ff9ce7 0xbf19b8fffe1ff39c

def z909 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x1033fb8f38e0739a 0xc2067f71e71c0e73

def z910 : W := mkw 0x04a0914d10000000 0x00941229a2000000 0xb0f3fbff30000003 0xd61e7f7fe6000000

def z911 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8cfc5f1f0fffcff 0xbf19f8be3e1fff9f

def z912 : W := mkw 0x224f6800024be000 0x0449ed0000497c00 0xafcff8000fffe005 0xf5f9ff0001fffc00

def z913 : W := mkw 0x0010d90718c2218a 0x20021b20e3184431 0x8033fa0f38e2639d 0xd0067f41e71c4c73

def z914 : W := mkw 0x324ff925f24be088 0x2649ff24be497c11 0x000ff801f003e099 0x0001ff003e007c13

def z915 : W := mkw 0x0010d9a758e2318a 0x20021b34eb1c4631 0xd033fffff8e2739f 0xda067fffff1c4e73

def z916 : W := mkw 0x26ff68000cdaa000 0x04dfed00019b5400 0xaffff8000ffc0005 0xf5ffff0001ff8000

def z917 : W := mkw 0x0010d90518c22000 0x00021b20a3184400 0x9033fb8f38e2739f 0xd2067f71e71c4e73

def z918 : W := mkw 0x17ef364cb0000000 0x02fde6c996000000 0xf7fffffe30000003 0xfeffffffc6000000

def z919 : W := mkw 0x17aa76dcb06e94a4 0x42f54edb960dd294 0x0f323a0e30ff9ce4 0x41e64741c61ff39c

def z920 : W := mkw 0x030a0648a3014a50 0x806140c91460294a 0xdf0e07ffff03ffff 0x7be1c0ffffe07fff

def z921 : W := mkw 0x17ef2668e3014a50 0x82fde4cd1c60294a 0x67cc0470c7000000 0x2cf9808e18e00000

def z922 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fffffff000139b 0xfefffffffe000273

def z923 : W := mkw 0x0810d9971cf6358f 0x21021b32e39ec6b1 0x9033fb8f38fe739f 0xd2067f71e71fce73

def z924 : W := mkw 0x06ba48000ed36000 0x00d7490001da6c00 0xaffff8000fffe005 0xf5ffff0001fffc00

def z925 : W := mkw 0x130a976df3014a50 0x826152edbe60294a 0xdf3fffffff03ffff 0xfbe7ffffffe07fff

def z926 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0xf0f3ffff38e2739f 0xfe1e7fffe71c4e73

def z927 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fffffff00380e3 0xfefffffffe00701c

def z928 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x983ffb8f38e3f39f 0xf307ff71e71c7e73

def z929 : W := mkw 0x0045912550000000 0x0008b224aa000000 0xb0f3fbff30000003 0xd61e7f7fe6000000

def z930 : W := mkw 0x00450030400c8424 0x4008a00608019084 0xe8cc0470c0fd8c64 0xbd19808e181fb18c

def z931 : W := mkw 0x17efb76df2014050 0x82fdf6edbe40280a 0xf7fffffff803f3ff 0xfeffffffff007e7f

def z932 : W := mkw 0x1145976df0000000 0x0228b2edbe000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z933 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x4f0e0401ff03fffd 0x29e1c0803fe07fff

def z934 : W := mkw 0x17efb76df2014050 0x82fdf6edbe40280a 0xf7fffffff000601b 0xfefffffffe000c03

def z935 : W := mkw 0x04f548000cdaa000 0x009ea900019b5400 0xaffff8000fffe005 0xf5ffff0001fffc00

def z936 : W := mkw 0x0000d18510621080 0x00001a30a20c4210 0x9033fb8f38e2739f 0xd2067f71e71c4e73

def z937 : W := mkw 0x0110069209a41f06 0x002200d2413483e0 0xfff007fe0ffc1f06 0xfffe00ffc1ff83e0

def z938 : W := mkw 0x06efb12550000000 0x00ddf624aa000000 0xf7fffffff0000003 0xfefffffffe000000

def z939 : W := mkw 0x0010489208e635ae 0x60020912411cc6b5 0x0000000008e27ffc 0x00000000011c4fff

def z940 : W := mkw 0x0db006daadb41f57 0x81b600db55b683ea 0xfff007fe3ffc1f1e 0xfffe00ffc7ff83e3

def z941 : W := mkw 0x1045f1b5506e94a4 0x4208be36aa0dd294 0xf8cdfdf1c0ff9ce7 0xbf19bfbe381ff39c

def z942 : W := mkw 0x0cb000da0cb41507 0x0196001b419682a0 0xbff003fe0ffc1306 0xf7fe007fc1ff8260

def z943 : W := mkw 0x00004090006e94a4 0x40000812000dd294 0xf8cc05f1c0ff9ce7 0xbf1980be381ff39c

def z944 : W := mkw 0x025f48000acbe000 0x004be90001597c00 0xaffff8000fffe005 0xf5ffff0001fffc00

def z945 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8cdc5f1c8ffffff 0xbf19b8be391fffff

def z946 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0xb0fdf9fe00000001 0xb61fbf3fc0000000

def z947 : W := mkw 0x17efb76df1000a50 0x82fdf6edbe20014a 0xfffffffff0039fff 0xfffffffffe0073ff

def z948 : W := mkw 0x0010d90718c2218a 0x20021b20e3184431 0x0033fa0e38006318 0x40067f41c7000c63

def z949 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8fffdf1c0ff9ce7 0xff1fffbe381ff39c

def z950 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fffffff0001ce3 0xfefffffffe00039c

def z951 : W := mkw 0x16efb16d50000000 0x02ddf62daa000000 0x30fff9fe00000001 0x861fff3fc0000000

def z952 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fffffff0021087 0xfefffffffe004210

def z953 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff007fe0fff9fe6 0xfffe00ffc1fff3fc

def z954 : W := mkw 0x1fba364ebf914b53 0x83f746c9d7f2296a 0x07323a0e3f006318 0x40e64741c7e00c63

def z955 : W := mkw 0x0045c9b1406eb4a4 0x4008b936280dd694 0xf8cffdf1c0fffce7 0xbf19ffbe381fff9c

def z956 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0xb7f1f9fe00000000 0xf6fe3f3fc0000000

def z957 : W := mkw 0x0010d9b758e635ae 0x60021b36eb1cc6b5 0xf8f3fffff8fe7fff 0xff1e7fffff1fcfff

def z958 : W := mkw 0x05e5264800000000 0x00bca4c900000000 0xf7f1fffe00000002 0xfefe3fffc0000000

def z959 : W := mkw 0x0010d9871cf2318a 0x20021b30e39e4631 0x9833fb8f3ffe739f 0xd3067f71e7ffce73

def z960 : W := mkw 0x15e5b76d50000000 0x02bcb6edaa000000 0x70f1fffe00000002 0x8e1e3fffc0000000

def z961 : W := mkw 0x16efb16d50000000 0x02ddf62daa000000 0x37f3f9fe00000000 0xc6fe7f3fc0000000

def z962 : W := mkw 0x04f520000c900000 0x009ea40001920000 0xaff1f8000ffc0004 0xf5fe3f0001ff8000

def z963 : W := mkw 0x020a0000a3014a50 0x804140001460294a 0x8f0e0001ff03fffd 0x71e1c0003fe07fff

def z964 : W := mkw 0x16efb16df0000000 0x02ddf62dbe000000 0x30fdf9fec0000000 0x861fbf3fd8000000

def z965 : W := mkw 0x05b006480d900a00 0x00b600c901b20140 0xfff007fe0ffc1f06 0xfffe00ffc1ff83e0

def z966 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x7ff005fe0ffc1f04 0xaffe00bfc1ff83e0

def z967 : W := mkw 0x0000009000241404 0x0000001200048280 0xf8cc05f0c0fd9c66 0xbf1980be181fb38c

def z968 : W := mkw 0x001099071880210a 0x20021320e3100421 0x1033fb8e38006318 0xc2067f71c7000c63

def z969 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffdf8000ffd8004 0xf5ffbf0001ffb000

def z970 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0x30f1fbff30000002 0x861e3f7fe6000000

def z971 : W := mkw 0x1000916d50000000 0x0200122daa000000 0x1031f9fe00000000 0x82063f3fc0000000

def z972 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xf7f007fe0ffc0302 0xfefe00ffc1ff8060

def z973 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xfffffffff703ecfb 0xfffffffffee07d9f

def z974 : W := mkw 0x37efb76df719ca50 0x86fdf6edbee3394a 0xfffffffff71d8c63 0xfffffffffee3b18c

def z975 : W := mkw 0x17efb76df1000a50 0x82fdf6edbe20014a 0xffffffffff001fff 0xffffffffffe003ff

def z976 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xa7f3f8000ffe6005 0xd4fe7f0001ffcc00

def z977 : W := mkw 0x090006da01241f07 0x012000db402483e0 0xffc007fe0ffc1f06 0xfff800ffc1ff83e0

def z978 : W := mkw 0x281048920efff507 0x0502091241dffea0 0x080000000fffe004 0x0100000001fffc00

def z979 : W := mkw 0x081048920ff77fdf 0xa102091241feeffb 0x080000000ffffffc 0x0100000001ffffff

def z980 : W := mkw 0x17efb76df4100000 0x02fdf6edbe820000 0xfffffffff71c0003 0xfffffffffee38000

def z981 : W := mkw 0x24f568000cdaa000 0x049ead00019b5400 0xaffdf8000fff8005 0xf5ffbf0001fff000

def z982 : W := mkw 0x26ef6800065be000 0x04dded0000cb7c00 0xafcff80007ffe005 0xb5f9ff0000fffc00

def z983 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffff8013fffe09d 0xf5ffff0027fffc13

def z984 : W := mkw 0x0db006da0db41f57 0x81b600db41b683ea 0xfff007fe0ffc1ffe 0xfffe00ffc1ff83ff

def z985 : W := mkw 0x0045912550000000 0x0008b224aa000000 0x30f1f9fe00000000 0x861e3f3fc0000000

def z986 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x3ff003fe0ffc1f04 0xc7fe007fc1ff83e0

def z987 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0xb0f1f9ff00000003 0x961e3f3fe0000000

def z988 : W := mkw 0x16efb16d50000000 0x02ddf62daa000000 0x37fdf9fe00000000 0xa6ffbf3fc0000000

def z989 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x903ffb8ff8e3f3ff 0xd207ff71ff1c7e7f

def z990 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfffc07ffcffc1f07 0xffff80fff9ff83e0

def z991 : W := mkw 0x0045c121404a8000 0x0008b82428095000 0xf8cdc5f1c0ff9ce7 0xbf19b8be381ff39c

def z992 : W := mkw 0x17efb76df2014000 0x02fdf6edbe402800 0xffffffffff03f39f 0xffffffffffe07e73

def z993 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x37f1f9fe00000000 0x86fe3f3fc0000000

def z994 : W := mkw 0x0010489208eeb5ae 0x60020912411dd6b5 0x0800000000ff9ce4 0x01000000001ff39c

def z995 : W := mkw 0x0045c1b3406e95ae 0x6008b836680dd2b5 0xf8cdc5f1c0ff9fff 0xbf19b8be381ff3ff

def z996 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xffcdc5f1cfff9ce7 0xfff9b8be39fff39c

def z997 : W := mkw 0x17aab76df0000000 0x02f556edbe000000 0xd733fffff0000003 0xdae67ffffe000000

def z998 : W := mkw 0x224ff925524be0a8 0x6449ff24aa497c15 0x000ff801f003e0f9 0x0001ff003e007c1f

def z999 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff007fe07fc0c02 0xfffe00ffc0ff8180

def z1000 : W := mkw 0x36efb16d5619c000 0x06ddf62daac33800 0x3ffdf9fe071d8000 0xa7ffbf3fc0e3b000

def z1001 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0xd03fff8ff8e2739f 0xfa07fff1ff1c4e73

def z1002 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x9033fb8f38e0631b 0xd2067f71e71c0c63

def z1003 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0xf8fdfdffc0039ce7 0xbf1fbfbff800739c

def z1004 : W := mkw 0x0010d90718c2210a 0x20021b20e3184421 0x9033fb8f38e2631f 0xd2067f71e71c4c63

def z1005 : W := mkw 0x16efb16d50000000 0x02ddf62daa000000 0xf7fffdffc0000003 0xfeffffbff8000000

def z1006 : W := mkw 0x17aab74db0000000 0x02f556e9b6000000 0xf7f3ffff30000003 0xfefe7fffe6000000

def z1007 : W := mkw 0x36ff6820eedbe000 0x06dfed041ddb7c00 0xaffff800cfffe005 0xf5ffff0019fffc00

def z1008 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x77fffdfff0000001 0xaeffffbffe000000

def z1009 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffff80007fd8001 0xf5ffff0000ffb000

def z1010 : W := mkw 0x0db006da0db41fa7 0x41b600db41b683f4 0xfff007fe0ffc1fe6 0xfffe00ffc1ff83fc

def z1011 : W := mkw 0x201048920efff5ae 0x6402091241dffeb5 0x080000000ffffffc 0x0100000001ffffff

def z1012 : W := mkw 0x2db02eda0db43f07 0x05b605db41b687e0 0xfff03ffe0ffc1f06 0xfffe07ffc1ff83e0

def z1013 : W := mkw 0x26ff68480edbe000 0x04dfed0901db7c00 0xbffff9fe0fffe005 0xf7ffff3fc1fffc00

def z1014 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x7fc007fe0ffc1f06 0x2ff800ffc1ff83e0

def z1015 : W := mkw 0x0045912550000000 0x0008b224aa000000 0xf0fdfdffc0000003 0xbe1fbfbff8000000

def z1016 : W := mkw 0x0cb000da0cb41507 0x0196001b419682a0 0xfff005fe0ffc1c06 0xfffe00bfc1ff8380

def z1017 : W := mkw 0x26ba68000edbe000 0x04d74d0001db7c00 0x8f33f8000fffe005 0xd1e67f0001fffc00

def z1018 : W := mkw 0x24f568000cdaa000 0x049ead00019b5400 0x27f1f8000ffc0000 0xc4fe3f0001ff8000

def z1019 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0xb0f1fbfe00000002 0xd61e3f7fc0000000

def z1020 : W := mkw 0x17efb76df2014000 0x02fdf6edbe402800 0xf7fffffff003e003 0xfefffffffe007c00

def z1021 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fffffff8001307 0xfeffffffff000260

def z1022 : W := mkw 0x15e5b76df0000000 0x02bcb6edbe000000 0x30f1fbfe30000000 0x861e3f7fc6000000

def z1023 : W := mkw 0x0100974d10000000 0x002012e9a2000000 0xd033ffff30000003 0xda067fffe6000000

def z1024 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x2ffff8000ffde000 0xe5ffff0001ffbc00

def z1025 : W := mkw 0x0010489208eeb5ae 0x60020912411dd6b5 0xc80e0601f8ffffff 0x7901c0c03f1fffff

def z1026 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8cfc7f1f0ff9ce7 0xff19f8fe3e1ff39c

def z1027 : W := mkw 0x0010d9b758e635ae 0x60021b36eb1cc6b5 0xd83ffffff8e3ffff 0xfb07ffffff1c7fff

def z1028 : W := mkw 0x07ef264803014a00 0x00fde4c900602940 0xfffffffe0f03ff07 0xffffffffc1e07fe0

def z1029 : W := mkw 0x324ff925f24be050 0x8649ff24be497c0a 0x000ff801f003e0f9 0x0001ff003e007c1f

def z1030 : W := mkw 0x004581b1402c9424 0x4008b03628059284 0xf8cdc5f1c0fd9c67 0xbf19b8be381fb38c

def z1031 : W := mkw 0x0010998718a0310a 0x20021330e3140621 0x9033fb8f38e0731f 0xd2067f71e71c0e63

def z1032 : W := mkw 0x0010d99718e6358e 0x20021b32e31cc6b1 0xf8fffffff8ffffff 0xff1fffffff1fffff

def z1033 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z1034 : W := mkw 0x26ff68000edbe0a0 0x44dfed0001db7c14 0xaffff8000fffe0e5 0xf5ffff0001fffc1c

def z1035 : W := mkw 0x15e5b76df0000000 0x02bcb6edbe000000 0xf0f3fffff0000003 0xde1e7ffffe000000

def z1036 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x77fffffef0000000 0xeeffffffde000000

def z1037 : W := mkw 0x07efa76940000000 0x00fdf4ed28000000 0xf7ffffffc0000003 0xfefffffff8000000

def z1038 : W := mkw 0x0010588618e2310a 0x20020b10c31c4621 0x9033fb8e38e2731f 0xd2067f71c71c4e63

def z1039 : W := mkw 0x0da006d805341e05 0x01b400db00a683c0 0xfff007fe07fc1c06 0xfffe00ffc0ff8380

def z1040 : W := mkw 0x24b048000edbe000 0x0496090001db7c00 0xaff3f8000fffe005 0xf5fe7f0001fffc00

def z1041 : W := mkw 0x15e5b76d51000a00 0x02bcb6edaa200140 0xfff1fffe0f001f06 0xfffe3fffc1e003e0

def z1042 : W := mkw 0x0045d9b5506eb4ac 0x6008bb36aa0dd695 0xf8fffffff0fffcff 0xff1ffffffe1fff9f

def z1043 : W := mkw 0x010097b7f1241ffe 0xe02012f6fe2483ff 0x500007fff0001ffa 0x0a0000fffe0003ff

def z1044 : W := mkw 0x0045c1b3406e95a6 0x4008b836680dd2b4 0xf8cdc7ffc0ff9fe7 0xbf19b8fff81ff3fc

def z1045 : W := mkw 0x190097fff1241fa7 0x432012fffe2483f4 0x500007fff0001fe2 0x0a0000fffe0003fc

def z1046 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xffffffffff01ef7b 0xffffffffffe03def

def z1047 : W := mkw 0x0cb000da0cb41507 0x0196001b419682a0 0x3ff001fe07fc0000 0xa7fe003fc0ff8000

def z1048 : W := mkw 0x281048920fffff57 0x8502091241ffffea 0x080000000ffffffc 0x0100000001ffffff

def z1049 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfffc07fecffd9f66 0xffff80ffd9ffb3ec

def z1050 : W := mkw 0x0045d1b7506e95ae 0x6008ba36ea0dd2b5 0xf8cdc5ffc0ff9ce7 0xbf19b8bff81ff39c

def z1051 : W := mkw 0x17ef2678e30dce74 0xc2fde4cf1c61b9ce 0x6fcc0470c71d8c60 0x2df9808e18e3b18c

def z1052 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xffffffffff03e31f 0xffffffffffe07c63

def z1053 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x78cdc5f1c0ff8ce1 0xaf19b8be381ff19c

def z1054 : W := mkw 0x0010d99718eeb5ae 0x60021b32e31dd6b5 0x9033fb8f38fe739f 0xd2067f71e71fce73

def z1055 : W := mkw 0x17efb76df2014000 0x02fdf6edbe402800 0xf7ffffffff006003 0xfeffffffffe00c00

def z1056 : W := mkw 0x024fd925f24be0f8 0xe049fb24be497c1f 0x000ff801f003e0f9 0x0001ff003e007c1f

def z1057 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8cdc7f1c8ff9fe7 0xff19b8fe391ff3fc

def z1058 : W := mkw 0x081048920df63f8f 0x2102091241bec7f1 0x080000000ffc1f04 0x0100000001ff83e0

def z1059 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0x0f0e0201ff03fffd 0x41e1c0403fe07fff

def z1060 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0x7ffdfdfec7018c60 0xafffbfbfd8e0318c

def z1061 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7f3fffe30000002 0xfefe7fffc6000000

def z1062 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffffa013fffe007 0xf5ffff4027fffc00

def z1063 : W := mkw 0x17efb76df1000a00 0x02fdf6edbe200140 0xffffffffff039fe7 0xffffffffffe073fc

def z1064 : W := mkw 0x0db006daadb41f07 0x01b600db55b683e0 0xfff007fffffc1f06 0xfffe00ffffff83e0

def z1065 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0x37f3fbfe3f006318 0xc6fe7f7fc7e00c63

def z1066 : W := mkw 0x0010580618c2210a 0x20020b00c3184421 0x8033fa0f38e2739f 0xd0067f41e71c4e73

def z1067 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xffffffffff007f1f 0xffffffffffe00fe3

def z1068 : W := mkw 0x0045d1b7506e95ae 0x6008ba36ea0dd2b5 0xf8cfc7fff8ffffff 0xff19f8ffff1fffff

def z1069 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fffdfec0000001 0xfeffffbfd8000000

def z1070 : W := mkw 0x081048920cf6358f 0x21020912419ec6b1 0x0000000000fc0000 0x00000000001f8000

def z1071 : W := mkw 0x26ff68020edbe102 0x04dfed0041db7c20 0xaffffa0e0fffe305 0xf5ffff41c1fffc60

def z1072 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x78cdc5f1c0fd9ce2 0xaf19b8be381fb39c

def z1073 : W := mkw 0x15e5b76d50000000 0x02bcb6edaa000000 0xf7f3ffff30000003 0xfefe7fffe6000000

def z1074 : W := mkw 0x0010918718a01102 0x00021230e3140220 0x9033fb8f38e2739f 0xd2067f71e71c4e73

def z1075 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xffffffffff03ec67 0xffffffffffe07d8c

def z1076 : W := mkw 0x15e5b76df0000000 0x02bcb6edbe000000 0xf0fdfffff0000003 0xbe1fbffffe000000

def z1077 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfffe07ffffffffff 0xffffc0ffffffffff

def z1078 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffff8000ffffce5 0xf5ffff0001ffff9c

def z1079 : W := mkw 0x0010d99718e6358e 0x20021b32e31cc6b1 0x9833fb8f38fe7f9f 0xd3067f71e71fcff3

def z1080 : W := mkw 0x16efb16df0000000 0x02ddf62dbe000000 0xb7fff9fff0000001 0xf6ffff3ffe000000

def z1081 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0x30fdf9ffc0000001 0x861fbf3ff8000000

def z1082 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x70fffffff0000003 0x8e1ffffffe000000

def z1083 : W := mkw 0x00454090006e9404 0x0008a812000dd280 0xf8cdc5f1c0ff9ce7 0xbf19b8be381ff39c

def z1084 : W := mkw 0x26ff68000edbe088 0x24dfed0001db7c11 0xaffff8000fffe09d 0xf5ffff0001fffc13

def z1085 : W := mkw 0x0db006580d940e05 0x01b600cb01b281c0 0xfff007fe0ffc0c06 0xfffe00ffc1ff8180

def z1086 : W := mkw 0x0da006da05341f07 0x01b400db40a683e0 0xffc007fe07fc1f06 0xbff800ffc0ff83e0

def z1087 : W := mkw 0x0045d1b5506e94a4 0x4008ba36aa0dd294 0xf8cffdf1f0ff9ce7 0xbf19ffbe3e1ff39c

def z1088 : W := mkw 0x15e5b76df0000000 0x02bcb6edbe000000 0xf7f1fffff0000002 0xfefe3ffffe000000

def z1089 : W := mkw 0x2fef2658a71dce55 0x85fde4cb14e3b9ca 0x6fcc0470c71d8c60 0x2df9808e18e3b18c

def z1090 : W := mkw 0x090097ff51241faf 0x612012ffea2483f5 0x500007fff0001ffa 0x0a0000fffe0003ff

def z1091 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x78cdc5f0c0ff9ce4 0xaf19b8be181ff39c

def z1092 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x77f3fffff0000002 0xcefe7ffffe000000

def z1093 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffdf80007ff8005 0xb5ffbf0000fff000

def z1094 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xb7f003fe0ffc1306 0xd6fe007fc1ff8260

def z1095 : W := mkw 0x0000d90510422088 0x20001b20a2084411 0x9033fb8f3802739f 0xd2067f71e7004e73

def z1096 : W := mkw 0x190097fff1241f8f 0x232012fffe2483f1 0x500007fff0001f9a 0x0a0000fffe0003f3

def z1097 : W := mkw 0x1100976df0000000 0x022012edbe000000 0x5031fffff0000002 0x8a063ffffe000000

def z1098 : W := mkw 0x0b1a4e92aff77fdf 0xa16349d255feeffb 0xcf0e0601ffffffff 0x79e1c0c03fffffff

def z1099 : W := mkw 0x081048920df63f07 0x0102091241bec7e0 0x080000000ffe7f04 0x0100000001ffcfe0

def z1100 : W := mkw 0x17efb76df1000a50 0x82fdf6edbe20014a 0xf7fffffff000031b 0xfefffffffe000063

def z1101 : W := mkw 0x0100060001000a00 0x002000c000200140 0xcf0e0601ff03ffff 0x79e1c0c03fe07fff

def z1102 : W := mkw 0x24f5f9b75cfeb5ae 0x649ebf36eb9fd6b5 0x30f1f9fe00fc0000 0x861e3f3fc01f8000

def z1103 : W := mkw 0x0fba064aaf914b53 0x81f740c955f2296a 0x0730020e0f000300 0x40e60041c1e00060

def z1104 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0xdf3e078fff03ffff 0xfbe7c0f1ffe07fff

def z1105 : W := mkw 0x2045e9b1406eb4a4 0x4408bd36280dd694 0xf8cdfdf1c0ff9ce7 0xbf19bfbe381ff39c

def z1106 : W := mkw 0x281048920dfebf07 0x0502091241bfd7e0 0x080000000ffc1f04 0x0100000001ff83e0

def z1107 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xfffffffff803ffff 0xffffffffff007fff

def z1108 : W := mkw 0x26ff68204edbe000 0x04dfed0409db7c00 0xeffffc70cfffe005 0xfdffff8e19fffc00

def z1109 : W := mkw 0x0045c131404e8424 0x4008b8262809d084 0xf8cdc5f1c0ff8c67 0xbf19b8be381ff18c

def z1110 : W := mkw 0x0010d98718eab18a 0x20021b30e31d5631 0x9833fb8f38fff39f 0xd3067f71e71ffe73

def z1111 : W := mkw 0x00454030404e8424 0x4008a8060809d084 0x68cdc470c0fd8c60 0xad19b88e181fb18c

def z1112 : W := mkw 0x04a0914d10000000 0x00941229a2000000 0x30f1f9fe00000000 0x861e3f3fc0000000

def z1113 : W := mkw 0x26ff28000e916000 0x04dfe50001d22c00 0xaffff8000ffc6005 0xf5ffff0001ff8c00

def z1114 : W := mkw 0x17efb76df00000a0 0x42fdf6edbe000014 0xf7fffffff00000e3 0xfefffffffe00001c

def z1115 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xf7fffffff003fffb 0xfefffffffe007fff

def z1116 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff007ffcffc1fe6 0xfffe00fff9ff83fc

def z1117 : W := mkw 0x17efb76df2014050 0x82fdf6edbe40280a 0xf7fffffff0018063 0xfefffffffe00300c

def z1118 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x68cdc471c0ff9ce5 0x2d19b88e381ff39c

def z1119 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0x70cdc5f1c0ff9ce3 0x8e19b8be381ff39c

def z1120 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x1033fb8e38e2739c 0xc2067f71c71c4e73

def z1121 : W := mkw 0x001018061880210a 0x20020300c3100421 0x8033fa0e38006319 0xd0067f41c7000c63

def z1122 : W := mkw 0x17efb76df1000a50 0x82fdf6edbe20014a 0xf7fffffff0000c63 0xfefffffffe00018c

def z1123 : W := mkw 0x26ff6800aedbe000 0x04dfed0015db7c00 0xaffff801ffffe005 0xf5ffff003ffffc00

def z1124 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0xb0f3fbff3802739f 0xd61e7f7fe7004e73

def z1125 : W := mkw 0x090097dfb1241fdf 0xa12012fbf62483fb 0x500007fff0001ffa 0x0a0000fffe0003ff

def z1126 : W := mkw 0x0010580618c2210a 0x20020b00c3184421 0x0033fa0e38026319 0x40067f41c7004c63

def z1127 : W := mkw 0x0045c1b1406e94a4 0x4008b836280dd294 0xf8cfc5f1c8fffce7 0xff19f8be391fff9c

def z1128 : W := mkw 0x0fba1e4ebf916b5b 0xa1f743c9d7f22d6b 0x07323a0e3f006318 0x40e64741c7e00c63

def z1129 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xf7ffffffff03e3fb 0xfeffffffffe07c7f

def z1130 : W := mkw 0x07ef2648a3014a50 0x80fde4c91460294a 0xffffffffff03ffff 0xffffffffffe07fff

def z1131 : W := mkw 0x0cf5d9ff5cfeb5af 0x619ebb3feb9fd6b5 0x30f1f9fe00fc0000 0x861e3f3fc01f8000

def z1132 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xeffffc00cfffec65 0xfdffff8019fffd8c

def z1133 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0x77fdfffff0000002 0xaeffbffffe000000

def z1134 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfff3fffe0ffc1f07 0xfffe7fffc1ff83e0

def z1135 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0xcf3ffe01ff03ffff 0xf9e7ffc03fe07fff

def z1136 : W := mkw 0x07aa974db3014a50 0x80f552e9b660294a 0xffffffffff03ffff 0xffffffffffe07fff

def z1137 : W := mkw 0x26ff6800aedbe050 0x84dfed0015db7c0a 0xaffffa01fffff3ff 0xf5ffff403ffffe7f

def z1138 : W := mkw 0x37efb76df619c000 0x06fdf6edbec33800 0xffffffffff1fe007 0xffffffffffe3fc00

def z1139 : W := mkw 0x24f568000cdaa000 0x049ead00019b5400 0x2ff1f80007fc0000 0xa5fe3f0000ff8000

def z1140 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x27f1f80007fc0000 0x84fe3f0000ff8000

def z1141 : W := mkw 0x034f9725f3014a50 0x8069f2e4be60294a 0xffffffffff03ffff 0xffffffffffe07fff

def z1142 : W := mkw 0x16efb16df2014050 0x82ddf62dbe40280a 0x30fff9fff003e0f9 0x861fff3ffe007c1f

def z1143 : W := mkw 0x07efb74d10000000 0x00fdf6e9a2000000 0xf7ffffff30000003 0xfeffffffe6000000

def z1144 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xf7ffffffff007ffb 0xfeffffffffe00fff

def z1145 : W := mkw 0x0010488208e23102 0x00020910411c4620 0x9033fb8f38e2739f 0xd2067f71e71c4e73

def z1146 : W := mkw 0x26ff68020edbe10a 0x24dfed0041db7c21 0xaffff8000fffe31d 0xf5ffff0001fffc63

def z1147 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xf7ffffffff02739f 0xfeffffffffe04e73

def z1148 : W := mkw 0x0db00eda0db43f07 0x01b601db41b687e0 0xfff23ffe0ffc7f06 0xfffe47ffc1ff8fe0

def z1149 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x2ff3f8000fffe004 0xc5fe7f0001fffc00

def z1150 : W := mkw 0x05b006d80cb41404 0x00b600db01968280 0xfff007fe0ffc1c06 0xfffe00ffc1ff8380

def z1151 : W := mkw 0x0db0064a0d900b03 0x01b600c941b20160 0xfff007fe0ffc0306 0xfffe00ffc1ff8060

def z1152 : W := mkw 0x00454030404e8424 0x4008a8060809d084 0xe8cdc471c0ff9ce7 0xbd19b88e381ff39c

def z1153 : W := mkw 0x0db006daadb41f57 0x81b600db55b683ea 0xfff007fecffc1f66 0xfffe00ffd9ff83ec

def z1154 : W := mkw 0x06ef204800000000 0x00dde40900000000 0xb7fff9fe00000001 0xf6ffff3fc0000000

def z1155 : W := mkw 0x090097df11241f8f 0x212012fbe22483f1 0x500007fe00001f02 0x0a0000ffc00003e0

def z1156 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0xfffc07fe0fff9f07 0xffff80ffc1fff3e0

def z1157 : W := mkw 0x04b000920cb41506 0x00960012419682a0 0xfff007fe0ffc1f06 0xfffe00ffc1ff83e0

def z1158 : W := mkw 0x0010d99718e635ae 0x60021b32e31cc6b5 0x9033fb8f38e27fff 0xd2067f71e71c4fff

def z1159 : W := mkw 0x16efb16df0000000 0x02ddf62dbe000000 0xb0fffbfff0000003 0xd61fff7ffe000000

def z1160 : W := mkw 0x0045c9b1406eb4ac 0x6008b936280dd695 0xf8cdc5f1c0fffcff 0xbf19b8be381fff9f

def z1161 : W := mkw 0x17efb76df0000088 0x22fdf6edbe000011 0xf7fffffff000009b 0xfefffffffe000013

def z1162 : W := mkw 0x15e5b76d50000000 0x02bcb6edaa000000 0x37f1fbfe00000000 0xc6fe3f7fc0000000

def z1163 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fdfdffc0000003 0xbeffbfbff8000000

def z1164 : W := mkw 0x04b048000cd22000 0x00960900019a4400 0xaff1f8000ffc0004 0xf5fe3f0001ff8000

def z1165 : W := mkw 0x134fb76df0000000 0x0269f6edbe000000 0xd03ffffff0000003 0xda07fffffe000000

def z1166 : W := mkw 0x34e5b16d54188000 0x069cb62daa831000 0x30f1f9fe001c0000 0x861e3f3fc0038000

def z1167 : W := mkw 0x26ff20000e99c000 0x04dfe40001d33800 0xaffff8000ffd8005 0xf5ffff0001ffb000

def z1168 : W := mkw 0x030a0600a3014a50 0x806140c01460294a 0xefce0601ffffffff 0xfdf9c0c03fffffff

def z1169 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xfffffffff0fc0007 0xfffffffffe1f8000

def z1170 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0x70fdfdfec0000000 0xae1fbfbfd8000000

def z1171 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x2ffff80007ffe001 0xa5ffff0000fffc00

def z1172 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0x27fff8000fffe001 0xc4ffff0001fffc00

def z1173 : W := mkw 0x17efb76df3014a00 0x02fdf6edbe602940 0xffffffffff03ff07 0xffffffffffe07fe0

def z1174 : W := mkw 0x0810489209e63f8f 0x21020912413cc7f1 0x0000000008e27f9c 0x00000000011c4ff3

def z1175 : W := mkw 0x17efb76df3014a50 0x82fdf6edbe60294a 0xfffffffff7039ce7 0xfffffffffee0739c

def z1176 : W := mkw 0x05a0064800000000 0x00b400c900000000 0xf7f3fffe00000003 0xfefe7fffc0000000

def z1177 : W := mkw 0x0010d98718e2318a 0x20021b30e31c4631 0x1033fb8f30e2739b 0x82067f71e61c4e73

def z1178 : W := mkw 0x05e5976d50000000 0x00bcb2edaa000000 0xf7fffffff0000003 0xfefffffffe000000

def z1179 : W := mkw 0x17ef2668e0000000 0x02fde4cd1c000000 0xf7fffffec0000003 0xfeffffffd8000000

def z1180 : W := mkw 0x0db006daadb41f57 0x81b600db55b683ea 0xfff207fffffe7fff 0xfffe40ffffffcfff

def z1181 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fffffff8026007 0xfeffffffff004c00

def z1182 : W := mkw 0x17efb76df2014000 0x02fdf6edbe402800 0xfffffffff7018003 0xfffffffffee03000

def z1183 : W := mkw 0x37efb76df209c000 0x06fdf6edbe413800 0xf7fffffff0018003 0xfefffffffe003000

def z1184 : W := mkw 0x0010d98718eab1aa 0x60021b30e31d5635 0x9033fb8f38e3f3ff 0xd2067f71e71c7e7f

def z1185 : W := mkw 0x17efb76d50000000 0x02fdf6edaa000000 0xf7fffffe00000003 0xfeffffffc0000000

def z1186 : W := mkw 0x17efb76df0000000 0x02fdf6edbe000000 0xf7fffffff002609b 0xfefffffffe004c13

def z1187 : W := mkw 0x0db006da0db41f07 0x01b600db41b683e0 0x7ff007fe0ffc0f00 0xeffe00ffc1ff81e0

def z1188 : W := mkw 0x17efb76df1000a00 0x02fdf6edbe200140 0xfffffffff7000c03 0xfffffffffee00180

def z1189 : W := mkw 0x004540b0406e94a4 0x4008a816080dd294 0xf8cc05f0c0ff9ce6 0xbf1980be181ff39c

def z1190 : W := mkw 0x0000d9871062318a 0x20001b30e20c4631 0x9033fb8f3002739b 0xd2067f71e6004e73

def z1191 : W := mkw 0x16efb16d50000000 0x02ddf62daa000000 0xb7fffbff30000003 0xf6ffff7fe6000000

def z1192 : W := mkw 0x26ff68000edbe000 0x04dfed0001db7c00 0xaffff801cfffe0e5 0xf5ffff0039fffc1c

def z1193 : W := mkw 0x14e5b16d50000000 0x029cb62daa000000 0xf0f1fdfe00000002 0xbe1e3fbfc0000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z8,z5,z6]),(0,[z0,z9,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z10,z5,z6])],[(0,[z0,z1,z11,z2,z3,z5,z6]),(0,[z12,z0,z13,z1,z2,z3,z6]),(0,[z0,z1,z14,z2,z3,z15,z6]),(0,[z0,z16,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z17,z6]),(1,[z0,z18,z2,z3,z5,z6]),(0,[z19,z0,z1,z2,z3,z5,z6]),(0,[z20,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z21,z3,z5,z6,z22]),(0,[z23,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z24])],[(0,[z0,z25,z2,z3,z5,z26,z6]),(1,[z27,z0,z2,z28,z5,z6])],[(0,[z0,z29,z1,z2,z3,z5,z6]),(0,[z0,z1,z30,z2,z3,z31,z6]),(0,[z0,z1,z32,z2,z3,z5,z6])],[(0,[z33,z0,z1,z2,z3,z15,z6]),(0,[z34,z0,z9,z2,z3,z5,z6]),(0,[z0,z1,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z36,z6])],[(0,[z0,z1,z2,z3,z5,z37,z6]),(0,[z0,z1,z14,z2,z3,z38,z6]),(0,[z0,z1,z2,z3,z39,z5,z6])],[(0,[z0,z1,z2,z3,z40,z5,z6]),(0,[z0,z1,z2,z41,z3,z5,z6]),(0,[z0,z1,z2,z3,z42,z5,z6]),(0,[z0,z1,z2,z43,z44,z3,z5])]],
   [[(0,[z0,z1,z2,z45,z3,z5,z6]),(0,[z0,z1,z2,z46,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z47,z6]),(0,[z27,z0,z16,z2,z3,z5,z6]),(1,[z0,z1,z3,z15,z31,z6]),(0,[z0,z1,z2,z48,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z49,z6])],[(0,[z50,z1,z51,z2,z3,z5,z6])],[(0,[z52,z0,z1,z2,z53,z5,z6]),(0,[z12,z0,z1,z2,z3,z54,z6]),(0,[z0,z1,z2,z55,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z6,z56]),(0,[z0,z1,z57,z2,z3,z5,z6]),(0,[z0,z58,z1,z2,z3,z5,z6])],[(0,[z7,z0,z59,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z60,z6]),(0,[z61,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z3,z5,z6])],[(1,[z0,z1,z2,z3,z62,z6]),(0,[z63,z0,z13,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z64,z5,z6]),(0,[z0,z1,z2,z3,z65,z5,z6]),(0,[z0,z1,z2,z3,z66,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z67]),(0,[z0,z1,z21,z2,z3,z5,z68])],[(1,[z50,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z69,z6]),(1,[z70,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z71]),(0,[z0,z1,z2,z3,z5,z6,z72]),(0,[z0,z1,z2,z3,z15,z31,z6])],[(0,[z73,z0,z1,z74,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z75]),(0,[z76,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z77,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z78,z5,z6]),(0,[z0,z1,z79,z2,z3,z5,z6]),(0,[z80,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z25,z2,z81,z3,z5,z6]),(0,[z0,z1,z2,z82,z3,z5,z6]),(0,[z0,z1,z2,z83,z3,z5,z6]),(0,[z84,z0,z1,z2,z3,z15,z6]),(0,[z85,z0,z1,z2,z3,z5,z6]),(0,[z0,z14,z2,z86,z3,z5,z6]),(0,[z0,z1,z2,z3,z87,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z88])],[(0,[z89,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z90,z5,z6]),(0,[z0,z1,z2,z3,z5,z91,z6]),(0,[z34,z92,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z93,z3,z5,z6]),(1,[z94,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z95,z6]),(1,[z0,z1,z2,z96,z97,z6])],[(0,[z0,z1,z2,z3,z5,z98,z6]),(0,[z73,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z99,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z100])],[(1,[z0,z1,z2,z3,z101,z6]),(0,[z0,z1,z102,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z103,z5,z6]),(0,[z0,z1,z2,z3,z5,z104,z6]),(0,[z0,z1,z2,z43,z3,z5,z6])],[(0,[z105,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z106,z3,z5,z6]),(0,[z107,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z108,z5,z6])],[(0,[z0,z1,z2,z3,z5,z109,z6]),(0,[z73,z89,z1,z2,z3,z5,z6]),(0,[z63,z0,z1,z2,z3,z54,z6]),(0,[z0,z1,z2,z110,z3,z5,z6]),(0,[z0,z1,z111,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z112,z5,z6])],[(0,[z1,z2,z53,z3,z8,z5,z6]),(0,[z0,z1,z113,z2,z3,z5,z6]),(0,[z0,z1,z114,z2,z3,z5,z6])],[(1,[z63,z1,z2,z3,z115,z6]),(0,[z0,z9,z1,z2,z3,z31,z6])]],
   [[(0,[z116,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z117,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z2,z118,z3,z5,z6]),(0,[z0,z16,z1,z2,z3,z31,z6]),(0,[z0,z1,z30,z2,z3,z15,z6])],[(0,[z0,z1,z2,z3,z119,z5,z6]),(0,[z20,z0,z1,z2,z3,z31,z6])],[(0,[z0,z1,z120,z2,z3,z5,z6]),(0,[z63,z0,z18,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z121,z6]),(1,[z0,z1,z2,z122,z3,z6]),(0,[z0,z123,z1,z2,z3,z5,z6])],[(0,[z73,z0,z124,z2,z3,z5,z6]),(0,[z0,z1,z125,z2,z3,z5,z6]),(0,[z0,z1,z2,z126,z3,z5,z6]),(0,[z0,z1,z127,z128,z3,z5,z6]),(1,[z0,z1,z2,z5,z6,z129])],[(0,[z0,z130,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z131,z6])],[(1,[z0,z1,z2,z3,z132,z6]),(0,[z0,z1,z2,z3,z5,z6,z133]),(0,[z0,z1,z2,z134,z3,z5,z6]),(0,[z0,z1,z14,z2,z3,z135,z6]),(0,[z136,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z137,z5,z6]),(0,[z0,z1,z138,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z139,z5,z6])],[(0,[z140,z0,z1,z2,z3,z141,z6])],[(0,[z0,z1,z2,z142,z3,z5,z6]),(0,[z143,z0,z144,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z145,z5,z6]),(0,[z0,z1,z146,z2,z108,z5,z6]),(0,[z0,z1,z2,z147,z3,z5,z148])],[(0,[z0,z149,z1,z2,z3,z5,z6]),(0,[z150,z0,z1,z2,z3,z5,z6]),(0,[z140,z0,z1,z2,z3,z5,z6]),(0,[z0,z13,z1,z2,z3,z141,z6]),(0,[z151,z0,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z152,z3,z5,z68]),(0,[z0,z1,z2,z153,z3,z5,z6])],[(0,[z0,z1,z2,z3,z154,z5,z6]),(0,[z0,z1,z2,z155,z3,z5,z6]),(1,[z156,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z3,z31,z6]),(0,[z0,z1,z2,z3,z15,z15,z6]),(0,[z0,z1,z2,z3,z157,z5,z6])],[(0,[z0,z1,z74,z2,z3,z5,z6]),(1,[z0,z1,z2,z117,z3,z5]),(1,[z0,z1,z2,z3,z158,z6]),(0,[z0,z1,z2,z3,z5,z159,z6])],[(0,[z50,z0,z25,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z160]),(0,[z0,z1,z2,z3,z5,z161,z6])],[(0,[z7,z1,z51,z2,z3,z5,z6]),(1,[z0,z59,z2,z3,z5,z6]),(0,[z0,z1,z162,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z163]),(0,[z0,z1,z2,z3,z5,z6,z164]),(0,[z0,z1,z2,z43,z152,z5,z6]),(0,[z0,z1,z2,z3,z165,z5,z6])],[(1,[z0,z166,z2,z3,z5,z6]),(0,[z0,z1,z167,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z168,z5,z6]),(0,[z0,z1,z2,z169,z3,z5,z6])],[(0,[z73,z1,z2,z170,z3,z5,z6]),(0,[z0,z1,z2,z3,z171,z5,z6]),(0,[z0,z1,z2,z172,z3,z5,z6])]],
   [[(0,[z89,z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z86,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z26,z6]),(0,[z0,z1,z2,z3,z5,z173,z6]),(0,[z0,z1,z2,z3,z174,z5,z49]),(0,[z175,z0,z1,z2,z3,z5,z6])],[(0,[z73,z0,z1,z2,z3,z31,z6]),(0,[z176,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z177,z6]),(0,[z178,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z179]),(0,[z0,z1,z2,z3,z5,z180,z6])],[(0,[z181,z0,z1,z2,z3,z5,z6]),(0,[z182,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z183,z5,z6]),(0,[z0,z9,z1,z81,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z184,z6]),(0,[z0,z1,z2,z43,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z185,z6])],[(0,[z33,z84,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z186,z3,z8,z6]),(0,[z0,z1,z2,z187,z3,z8,z5]),(0,[z0,z1,z2,z188,z3,z5,z6]),(0,[z189,z0,z1,z2,z3,z5,z6]),(0,[z0,z9,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z190,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z191,z6]),(0,[z0,z1,z192,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z193]),(0,[z0,z1,z194,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z195]),(0,[z196,z0,z1,z2,z3,z5,z6]),(0,[z197,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z198,z2,z3,z5,z6]),(0,[z199,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z60,z22]),(0,[z0,z16,z1,z2,z3,z15,z6]),(0,[z0,z1,z21,z2,z3,z5,z22])],[(0,[z200,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z201,z6]),(0,[z1,z2,z3,z54,z5,z115,z6]),(0,[z84,z0,z1,z2,z43,z3,z5]),(0,[z34,z0,z1,z14,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z202,z6]),(0,[z203,z0,z1,z2,z3,z5,z6]),(0,[z20,z0,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z96,z3,z97,z6])],[(0,[z0,z1,z2,z3,z5,z6,z204]),(0,[z0,z1,z205,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z206,z6])],[(0,[z0,z1,z2,z3,z54,z5,z6]),(0,[z0,z1,z2,z3,z15,z115,z6]),(1,[z0,z1,z2,z207,z5,z6]),(1,[z208,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z209,z6]),(0,[z210,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z211,z5,z31,z6]),(0,[z0,z1,z2,z212,z5,z6,z213]),(0,[z0,z1,z2,z3,z174,z5,z213])],[(0,[z0,z1,z214,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z215,z6]),(0,[z0,z1,z2,z3,z5,z216,z6]),(1,[z0,z1,z2,z3,z6,z217])],[(0,[z218,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z54,z6]),(0,[z219,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z68,z6])],[(0,[z220,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z43,z3,z5,z131]),(0,[z0,z1,z2,z43,z3,z174,z5])],[(0,[z0,z221,z1,z2,z3,z5,z6]),(0,[z143,z0,z1,z2,z3,z5,z222]),(0,[z143,z0,z1,z2,z152,z3,z5]),(0,[z223,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z138,z2,z3,z31,z6]),(1,[z0,z1,z2,z3,z224,z6]),(0,[z0,z1,z2,z3,z139,z31,z6])],[(0,[z225,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z226,z3,z5,z6]),(0,[z0,z1,z2,z3,z227,z5,z6]),(0,[z0,z1,z21,z2,z3,z159,z6]),(0,[z0,z228,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z15,z229,z6]),(0,[z0,z1,z2,z44,z3,z15,z6]),(0,[z0,z1,z2,z230,z3,z5,z6])],[(0,[z0,z1,z231,z2,z3,z5,z6]),(0,[z232,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z145,z31,z6]),(0,[z0,z1,z233,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z234,z2,z3,z5,z6]),(0,[z140,z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z56,z22]),(0,[z235,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z148,z6])],[(0,[z236,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z237,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z238,z6]),(0,[z12,z0,z1,z2,z3,z6,z213]),(1,[z0,z1,z2,z239,z5,z6]),(0,[z0,z1,z240,z2,z3,z5,z6]),(0,[z0,z1,z2,z43,z5,z6,z241]),(0,[z0,z1,z2,z3,z242,z5,z6]),(0,[z0,z243,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z244,z3,z5,z6]),(0,[z245,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z74,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z246,z5,z6]),(1,[z247,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z78,z15,z6]),(0,[z0,z1,z2,z3,z5,z248,z6])],[(0,[z0,z1,z2,z3,z5,z6,z249]),(0,[z0,z1,z2,z3,z250,z5,z6]),(0,[z0,z1,z2,z3,z5,z251,z6]),(0,[z0,z1,z2,z3,z5,z195,z6]),(0,[z0,z1,z146,z2,z3,z209,z6]),(0,[z0,z1,z2,z3,z252,z5,z6])],[(1,[z89,z1,z74,z3,z5,z6]),(0,[z89,z0,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z128,z8,z5,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z0,z1,z2,z3,z5,z253,z6])],[(0,[z73,z0,z1,z2,z3,z15,z6]),(1,[z12,z1,z2,z3,z54,z6])],[(0,[z0,z254,z1,z2,z3,z5,z6]),(0,[z12,z1,z2,z3,z54,z5,z6]),(0,[z0,z1,z2,z3,z171,z31,z6]),(0,[z0,z1,z2,z43,z3,z15,z6]),(0,[z0,z1,z2,z97,z5,z148,z6])],[(0,[z0,z1,z2,z3,z132,z5,z6]),(0,[z0,z1,z255,z2,z3,z5,z6]),(0,[z27,z0,z1,z2,z28,z5,z6]),(0,[z0,z1,z2,z86,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z68,z26]),(0,[z256,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z147,z3,z5,z6]),(0,[z0,z1,z2,z257,z3,z5,z6])]],
   [[(0,[z27,z0,z25,z2,z3,z5,z6]),(1,[z0,z1,z2,z186,z3,z6]),(0,[z258,z0,z1,z2,z3,z5,z6]),(0,[z259,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z260,z2,z3,z5,z6]),(1,[z0,z1,z2,z212,z5,z6])],[(1,[z0,z261,z2,z3,z5,z6]),(0,[z262,z0,z1,z2,z3,z5,z6]),(0,[z263,z0,z1,z2,z3,z5,z26]),(0,[z0,z1,z3,z5,z68,z6,z22]),(0,[z0,z1,z2,z152,z3,z5,z22])],[(0,[z264,z0,z1,z51,z2,z3,z6]),(0,[z34,z70,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z265,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z266]),(0,[z0,z1,z2,z28,z145,z5,z6]),(0,[z0,z1,z2,z267,z3,z5,z6]),(0,[z268,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z152,z5,z131,z6])],[(0,[z63,z0,z1,z2,z3,z6,z213]),(0,[z63,z0,z1,z2,z3,z174,z6]),(0,[z0,z1,z2,z3,z5,z6,z269]),(0,[z0,z1,z2,z270,z3,z5,z6]),(1,[z0,z1,z2,z3,z271,z6]),(0,[z272,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z273]),(0,[z0,z1,z2,z3,z5,z6,z274]),(0,[z0,z1,z2,z96,z97,z5,z6])],[(0,[z275,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z54,z31,z6]),(0,[z143,z0,z1,z2,z3,z5,z60]),(0,[z0,z1,z2,z145,z5,z131,z6]),(0,[z0,z1,z276,z2,z3,z5,z6])],[(0,[z277,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z278,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z279,z6])]],
   [[(0,[z0,z1,z2,z280,z3,z5,z6]),(0,[z281,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z138,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z15,z282,z6])],[(0,[z50,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z283,z6]),(0,[z0,z1,z2,z3,z5,z6,z284]),(0,[z0,z1,z146,z2,z3,z5,z68]),(0,[z0,z1,z2,z285,z3,z97,z6])],[(0,[z0,z1,z2,z286,z3,z5,z6]),(0,[z0,z1,z2,z3,z287,z5,z6]),(1,[z0,z1,z2,z3,z5,z288]),(0,[z289,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z285,z44,z3,z6]),(1,[z0,z1,z2,z147,z3,z5])],[(0,[z290,z0,z1,z2,z3,z5,z6]),(0,[z0,z166,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z117,z3,z8,z5]),(0,[z63,z1,z2,z3,z5,z115,z6]),(0,[z0,z1,z2,z3,z5,z6,z291]),(0,[z0,z1,z2,z292,z3,z5,z6]),(0,[z0,z293,z1,z2,z3,z5,z6]),(0,[z0,z1,z138,z127,z3,z5,z6]),(0,[z0,z1,z2,z3,z145,z15,z6]),(0,[z0,z1,z2,z294,z3,z5,z6]),(0,[z0,z1,z2,z285,z5,z148,z6]),(0,[z0,z1,z2,z44,z96,z3,z6])],[(0,[z0,z1,z2,z3,z5,z295,z6]),(0,[z140,z0,z1,z2,z3,z15,z6]),(1,[z0,z1,z127,z128,z5,z6]),(0,[z0,z1,z2,z296,z3,z5,z6])],[(0,[z297,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z298,z6]),(0,[z27,z0,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z28,z5,z6])],[(0,[z299,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z74,z2,z3,z15,z6]),(0,[z0,z70,z1,z2,z3,z5,z6]),(0,[z0,z1,z21,z2,z3,z5,z6]),(0,[z300,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z97,z5,z6])],[(0,[z0,z9,z51,z2,z3,z5,z6]),(0,[z52,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z2,z3,z301,z5,z6]),(0,[z0,z13,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z5,z6,z56])]],
   [[(0,[z1,z74,z2,z3,z54,z5,z6]),(0,[z302,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z303,z2,z3,z5,z6]),(0,[z0,z16,z1,z2,z86,z5,z6]),(1,[z0,z2,z3,z304,z5,z6])],[(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z305,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z306,z5,z6]),(0,[z0,z1,z2,z3,z15,z131,z6])],[(0,[z0,z25,z2,z3,z5,z307,z6]),(0,[z0,z308,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z141,z5,z6]),(1,[z263,z0,z2,z3,z5,z26]),(0,[z0,z1,z2,z3,z5,z6,z129])],[(0,[z0,z1,z2,z86,z3,z15,z6]),(0,[z0,z1,z2,z3,z5,z31,z6]),(0,[z309,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z310,z6]),(0,[z0,z311,z1,z2,z3,z5,z6]),(0,[z73,z0,z1,z2,z312,z5,z6]),(0,[z0,z1,z2,z239,z3,z5,z6]),(0,[z0,z1,z2,z3,z313,z5,z6]),(0,[z0,z1,z2,z3,z314,z5,z6]),(0,[z0,z1,z2,z3,z15,z6,z241])],[(0,[z34,z0,z1,z2,z3,z246,z6]),(0,[z0,z1,z2,z3,z315,z5,z6]),(0,[z20,z0,z1,z30,z3,z5,z6])],[(0,[z316,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z317,z3,z5,z6]),(0,[z0,z1,z2,z3,z318,z5,z6]),(0,[z319,z0,z1,z2,z3,z5,z6])],[(0,[z63,z1,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z320,z3,z5,z6]),(0,[z0,z1,z321,z2,z3,z5,z6]),(0,[z0,z322,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z131,z6,z241])]],
   [[(0,[z0,z1,z2,z3,z5,z323,z6]),(0,[z1,z51,z2,z170,z3,z5,z6]),(0,[z34,z0,z1,z2,z3,z158,z6]),(0,[z0,z1,z3,z15,z5,z31,z6]),(0,[z200,z0,z1,z2,z3,z15,z6])],[(0,[z0,z1,z2,z3,z5,z6,z324]),(0,[z0,z1,z2,z3,z5,z325,z6]),(0,[z63,z0,z261,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z326]),(0,[z0,z2,z86,z3,z28,z5,z6]),(0,[z0,z1,z2,z327,z3,z5,z6])],[(0,[z0,z1,z2,z328,z3,z5,z6]),(0,[z0,z1,z2,z329,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z330]),(0,[z0,z1,z2,z331,z3,z5,z6]),(0,[z0,z1,z332,z2,z3,z5,z6])],[(0,[z0,z1,z333,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z26,z6]),(0,[z0,z1,z2,z3,z334,z5,z6])],[(0,[z34,z27,z0,z2,z3,z5,z6]),(0,[z335,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z224,z5,z6]),(0,[z277,z0,z1,z2,z3,z31,z6])],[(0,[z0,z336,z1,z2,z3,z5,z6]),(0,[z337,z0,z1,z2,z3,z5,z6]),(0,[z0,z25,z338,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z68,z222]),(0,[z339,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z340,z3,z5,z6])]],
   [[(0,[z50,z0,z1,z2,z3,z31,z6]),(0,[z0,z341,z1,z2,z3,z5,z6]),(1,[z0,z144,z2,z3,z5,z6]),(0,[z0,z1,z2,z342,z3,z5,z6]),(0,[z0,z1,z2,z3,z227,z15,z6])],[(0,[z343,z0,z1,z2,z3,z5,z6]),(0,[z344,z0,z1,z2,z3,z5,z6]),(0,[z89,z0,z1,z170,z3,z5,z6]),(0,[z0,z345,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z346,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z6,z213])],[(0,[z264,z0,z1,z2,z3,z5,z6]),(0,[z73,z0,z1,z170,z3,z5,z6]),(0,[z263,z0,z2,z3,z5,z26,z6]),(0,[z0,z1,z347,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z6,z241]),(0,[z0,z1,z2,z3,z5,z348,z6])],[(0,[z0,z51,z2,z3,z5,z26,z6]),(1,[z0,z1,z2,z3,z246,z6]),(0,[z0,z1,z2,z3,z5,z349,z6]),(0,[z0,z1,z2,z3,z5,z350,z6]),(0,[z0,z1,z2,z152,z3,z5,z6])],[(0,[z0,z1,z2,z3,z351,z5,z6]),(0,[z73,z0,z1,z2,z352,z5,z6]),(0,[z34,z0,z1,z2,z207,z5,z6]),(0,[z0,z1,z2,z3,z5,z353,z6]),(0,[z0,z1,z2,z3,z28,z31,z6]),(0,[z0,z1,z2,z3,z354,z5,z6]),(0,[z0,z1,z2,z3,z355,z5,z6]),(0,[z0,z1,z2,z3,z5,z356,z148])],[(0,[z357,z0,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z358,z3,z8,z6]),(0,[z0,z1,z2,z3,z5,z359,z6]),(0,[z0,z1,z2,z3,z5,z6,z360]),(0,[z27,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z361,z5,z6]),(0,[z0,z1,z21,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z97,z31,z6]),(1,[z0,z1,z2,z285,z148,z6])],[(0,[z0,z1,z2,z3,z5,z362,z6]),(0,[z0,z25,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z363,z3,z5,z6]),(0,[z0,z1,z2,z3,z207,z5,z6]),(1,[z0,z1,z2,z3,z159,z6]),(0,[z0,z1,z2,z3,z5,z364,z6])],[(0,[z0,z1,z2,z53,z145,z5,z6]),(0,[z0,z1,z2,z3,z15,z68,z6])]],
   [[(0,[z33,z1,z2,z3,z5,z60,z6]),(0,[z0,z1,z2,z3,z8,z31,z6]),(0,[z365,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z127,z2,z3,z5,z195]),(0,[z305,z0,z1,z2,z3,z31,z6])],[(0,[z0,z366,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z141,z31,z6]),(0,[z263,z247,z1,z2,z3,z5,z6]),(0,[z0,z1,z127,z2,z145,z5,z6]),(0,[z367,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z146,z2,z3,z5,z22])],[(0,[z0,z1,z2,z368,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z369,z6])],[(0,[z33,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z2,z3,z5,z370,z6]),(0,[z0,z1,z2,z186,z3,z5,z6]),(0,[z0,z338,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z129,z213])],[(0,[z33,z0,z51,z2,z3,z5,z6]),(0,[z0,z1,z371,z2,z3,z5,z6]),(1,[z73,z1,z170,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z38,z6])],[(1,[z0,z1,z2,z3,z168,z6]),(0,[z0,z1,z2,z3,z5,z6,z372])],[(0,[z7,z0,z1,z2,z53,z5,z6]),(0,[z34,z0,z1,z2,z239,z5,z6]),(0,[z0,z1,z2,z3,z5,z373,z6]),(0,[z0,z322,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z6,z374]),(0,[z0,z1,z2,z375,z3,z5,z6]),(0,[z0,z1,z2,z3,z174,z49,z6]),(0,[z0,z1,z376,z2,z3,z5,z6])],[(0,[z377,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z138,z2,z3,z378,z6]),(0,[z94,z1,z2,z3,z5,z31,z6]),(0,[z0,z1,z2,z3,z31,z6,z213])]],
   [[(0,[z0,z51,z2,z81,z3,z5,z6]),(0,[z140,z0,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z379]),(0,[z0,z1,z2,z3,z5,z380,z6]),(0,[z0,z1,z2,z3,z381,z5,z6]),(0,[z0,z208,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z382,z5,z6])],[(1,[z0,z1,z2,z187,z3,z5]),(0,[z0,z1,z2,z3,z5,z68,z60]),(1,[z0,z16,z2,z86,z5,z6]),(0,[z0,z1,z383,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z26,z6,z56]),(0,[z247,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z127,z2,z3,z224,z6]),(0,[z0,z1,z2,z3,z5,z384,z6]),(0,[z0,z1,z2,z385,z3,z5,z6])],[(0,[z73,z63,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z386,z3,z5,z6]),(0,[z140,z0,z13,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z387,z6])],[(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z388,z6]),(0,[z389,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z211,z5,z6]),(0,[z0,z1,z2,z390,z3,z5,z6])],[(0,[z50,z0,z1,z2,z3,z15,z6]),(0,[z89,z1,z74,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z391,z6]),(0,[z0,z1,z2,z3,z5,z115,z6]),(0,[z0,z1,z2,z3,z5,z392,z6]),(0,[z0,z1,z2,z393,z3,z5,z6]),(0,[z20,z0,z1,z3,z15,z5,z6])],[(0,[z0,z1,z2,z3,z394,z5,z6]),(0,[z34,z0,z2,z81,z3,z5,z6]),(0,[z0,z1,z2,z395,z3,z5,z6]),(0,[z268,z0,z2,z3,z145,z5,z6]),(1,[z1,z2,z3,z211,z5,z6]),(0,[z0,z1,z2,z44,z3,z6,z213])],[(0,[z0,z1,z396,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z397,z6]),(0,[z0,z398,z1,z2,z3,z5,z6]),(1,[z0,z1,z146,z3,z5,z68]),(0,[z0,z1,z2,z3,z5,z399,z6]),(0,[z400,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z401,z5,z6]),(0,[z402,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z403,z2,z3,z5,z6]),(0,[z0,z1,z2,z404,z3,z5,z6]),(0,[z0,z1,z405,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z28,z15,z6]),(0,[z0,z1,z406,z2,z3,z5,z6]),(0,[z0,z407,z1,z2,z3,z5,z6])],[(0,[z0,z9,z1,z14,z3,z5,z6]),(0,[z0,z1,z2,z408,z3,z5,z6]),(0,[z0,z1,z2,z3,z409,z5,z6]),(0,[z0,z1,z21,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z97,z15,z6]),(0,[z0,z1,z2,z96,z3,z49,z6])],[(0,[z0,z1,z2,z3,z410,z5,z6]),(0,[z411,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z152,z3,z31,z6]),(0,[z0,z1,z2,z3,z412,z5,z6])],[(0,[z413,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z128,z28,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z414]),(0,[z0,z1,z2,z3,z415,z5,z6])],[(0,[z0,z1,z416,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z8,z15,z6]),(0,[z7,z0,z1,z2,z3,z31,z6]),(0,[z12,z0,z1,z2,z3,z174,z6]),(0,[z0,z1,z417,z2,z3,z5,z6]),(0,[z27,z0,z1,z2,z3,z31,z6]),(1,[z0,z1,z138,z145,z5,z6]),(0,[z418,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z419,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z217,z241])],[(0,[z0,z1,z420,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z140,z63,z0,z1,z2,z3,z6]),(0,[z421,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z51,z2,z3,z5,z6]),(0,[z27,z422,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z26,z22])],[(0,[z0,z1,z2,z423,z3,z5,z6]),(0,[z0,z1,z424,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z425,z6]),(0,[z143,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z426,z3,z5,z6]),(0,[z0,z1,z127,z2,z3,z271,z6]),(0,[z0,z1,z2,z128,z5,z131,z6]),(0,[z0,z1,z2,z427,z3,z5,z6])],[(0,[z428,z0,z1,z2,z3,z5,z6]),(0,[z0,z336,z1,z51,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z429,z6]),(0,[z0,z338,z1,z2,z3,z31,z6]),(0,[z0,z430,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z431,z5,z6]),(1,[z84,z1,z2,z3,z5,z222]),(0,[z0,z1,z432,z2,z3,z5,z6]),(0,[z0,z1,z2,z433,z3,z5,z6]),(1,[z0,z338,z2,z3,z5,z56]),(0,[z0,z1,z2,z3,z31,z434,z6]),(0,[z0,z1,z2,z3,z5,z356,z6]),(0,[z0,z1,z2,z3,z435,z5,z6]),(0,[z0,z1,z2,z152,z3,z5,z131]),(0,[z0,z1,z2,z152,z3,z174,z5])],[(0,[z0,z1,z2,z436,z3,z5,z6]),(0,[z437,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z438,z0,z1,z2,z3,z5,z6]),(0,[z140,z0,z2,z3,z141,z5,z6]),(1,[z0,z1,z2,z3,z5,z356])],[(0,[z0,z1,z2,z3,z5,z439,z6]),(0,[z0,z1,z2,z3,z15,z6,z222]),(0,[z0,z1,z2,z3,z5,z6,z440]),(0,[z0,z1,z2,z3,z5,z441,z6])],[(0,[z0,z1,z2,z3,z442,z5,z6]),(0,[z0,z2,z3,z141,z5,z307,z6]),(0,[z0,z2,z3,z304,z145,z5,z6]),(0,[z0,z1,z127,z2,z3,z5,z288]),(0,[z0,z1,z443,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z444])]],
   [[(1,[z0,z124,z2,z3,z5,z6]),(0,[z0,z1,z445,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z446])],[(0,[z0,z25,z2,z86,z3,z5,z6]),(0,[z0,z1,z447,z2,z3,z5,z6]),(1,[z140,z0,z2,z3,z141,z6]),(0,[z0,z1,z2,z3,z5,z6,z448]),(0,[z0,z1,z2,z3,z5,z449,z6]),(0,[z450,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z451,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z452]),(0,[z453,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z211,z31,z6]),(0,[z0,z1,z2,z390,z3,z31,z6])],[(0,[z454,z0,z1,z2,z3,z5,z6]),(0,[z34,z0,z1,z2,z3,z5,z455]),(0,[z0,z1,z2,z456,z3,z5,z6]),(0,[z0,z1,z146,z2,z3,z5,z6])],[(0,[z33,z1,z2,z3,z54,z5,z6]),(0,[z0,z1,z2,z3,z457,z5,z6]),(0,[z12,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z458,z5,z6]),(1,[z0,z9,z14,z3,z5,z6]),(0,[z0,z1,z459,z2,z3,z5,z6]),(1,[z1,z2,z3,z211,z31,z6])],[(0,[z0,z1,z2,z3,z5,z101,z6]),(0,[z0,z1,z2,z3,z5,z460,z6]),(0,[z0,z1,z2,z3,z5,z282,z6])],[(0,[z461,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z352,z5,z6]),(0,[z0,z1,z2,z3,z5,z378,z6]),(0,[z0,z1,z2,z3,z31,z49,z6]),(0,[z0,z1,z2,z152,z3,z15,z6])],[(0,[z143,z84,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z462,z6])]],
   [[(0,[z0,z1,z2,z312,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z15,z6]),(0,[z27,z0,z1,z2,z3,z15,z6])],[(0,[z0,z463,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z3,z5,z49])],[(0,[z0,z25,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z170,z3,z5,z6]),(0,[z0,z464,z1,z2,z3,z5,z6])],[(1,[z0,z465,z2,z3,z5,z6]),(0,[z27,z466,z1,z2,z3,z5,z6]),(0,[z0,z1,z138,z2,z3,z467,z6]),(0,[z0,z1,z468,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z469,z6]),(0,[z0,z1,z2,z3,z5,z470,z6])],[(0,[z0,z1,z59,z2,z3,z5,z6]),(0,[z0,z471,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z6,z222]),(0,[z0,z366,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z43,z3,z5,z241])],[(0,[z143,z0,z465,z2,z3,z5,z6]),(0,[z0,z1,z2,z285,z3,z49,z6]),(0,[z0,z1,z2,z122,z3,z6,z241])],[(0,[z1,z2,z3,z5,z60,z6,z222]),(0,[z472,z0,z1,z2,z3,z5,z6]),(0,[z0,z338,z1,z2,z3,z15,z6]),(1,[z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z131,z6])],[(0,[z0,z1,z51,z2,z3,z31,z6]),(0,[z63,z0,z1,z2,z3,z5,z6]),(1,[z34,z0,z81,z3,z5,z6]),(0,[z0,z1,z473,z2,z3,z5,z6]),(0,[z0,z1,z2,z474,z3,z5,z6])]],
   [[(0,[z50,z0,z51,z2,z3,z5,z6]),(0,[z84,z0,z1,z2,z3,z5,z222]),(0,[z84,z0,z1,z2,z152,z3,z5]),(0,[z143,z0,z1,z2,z3,z31,z6]),(0,[z475,z0,z1,z2,z3,z5,z6])],[(0,[z476,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z455]),(0,[z0,z1,z2,z3,z5,z6,z241]),(0,[z0,z1,z2,z44,z3,z5,z213])],[(1,[z422,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z229,z5,z6])],[(0,[z0,z1,z2,z3,z382,z15,z6])],[(0,[z52,z0,z1,z2,z8,z5,z6]),(0,[z34,z0,z1,z2,z3,z5,z266]),(0,[z0,z1,z2,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z31,z6,z477]),(0,[z0,z1,z2,z478,z3,z5,z6]),(0,[z0,z1,z2,z479,z3,z5,z6]),(0,[z0,z1,z2,z97,z5,z131,z6])],[(0,[z0,z1,z2,z480,z3,z5,z6]),(0,[z0,z1,z2,z481,z3,z5,z6]),(0,[z0,z1,z2,z3,z482,z5,z6])],[(0,[z0,z1,z2,z3,z483,z5,z6]),(0,[z484,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z485]),(0,[z0,z1,z486,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z487,z6]),(0,[z0,z1,z127,z2,z128,z5,z6]),(0,[z0,z1,z2,z3,z5,z488,z6]),(0,[z0,z1,z2,z489,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z490])],[(0,[z25,z1,z51,z2,z3,z5,z6]),(0,[z491,z0,z1,z2,z3,z5,z6]),(0,[z0,z492,z1,z2,z3,z5,z6]),(0,[z73,z0,z1,z2,z3,z62,z6]),(0,[z493,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z494,z2,z3,z5,z6]),(0,[z0,z1,z2,z495,z3,z5,z6]),(0,[z0,z1,z2,z3,z496,z5,z6]),(0,[z0,z1,z2,z497,z3,z5,z6])]],
   [[(0,[z0,z1,z498,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z455,z6]),(0,[z0,z1,z499,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z68,z56]),(0,[z0,z1,z2,z500,z3,z5,z6]),(0,[z0,z1,z2,z3,z394,z15,z6])],[(0,[z501,z0,z1,z2,z3,z5,z6]),(1,[z52,z1,z2,z8,z5,z6]),(0,[z466,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z502,z2,z3,z5,z6]),(0,[z0,z1,z2,z128,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z503])],[(0,[z73,z0,z1,z2,z3,z5,z75]),(0,[z7,z1,z2,z53,z3,z5,z6]),(0,[z140,z12,z0,z1,z2,z3,z6]),(0,[z0,z1,z504,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z26,z6]),(0,[z0,z338,z1,z2,z3,z5,z56]),(0,[z0,z1,z146,z2,z3,z31,z6]),(1,[z0,z1,z21,z3,z5,z22]),(0,[z0,z1,z505,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z174,z5,z6])],[(0,[z506,z0,z1,z2,z3,z5,z6]),(0,[z12,z0,z1,z2,z3,z31,z6]),(0,[z0,z507,z1,z2,z3,z5,z6])],[(0,[z12,z0,z1,z2,z285,z3,z6]),(0,[z0,z1,z2,z3,z508,z5,z6]),(0,[z509,z0,z1,z2,z3,z5,z6])],[(0,[z84,z1,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z358,z3,z5,z6]),(0,[z0,z9,z14,z2,z3,z5,z6]),(0,[z0,z1,z2,z510,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z511])],[(0,[z512,z0,z1,z2,z3,z5,z6]),(0,[z73,z0,z1,z2,z3,z101,z6]),(0,[z0,z1,z74,z2,z3,z17,z6]),(0,[z0,z1,z2,z3,z5,z6,z213])],[(0,[z513,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z514,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z515]),(0,[z0,z1,z2,z3,z31,z516,z6]),(0,[z0,z1,z2,z3,z517,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z75]),(1,[z0,z1,z2,z3,z6,z360]),(0,[z0,z1,z128,z3,z145,z5,z6]),(0,[z0,z1,z2,z3,z15,z518,z6])],[(0,[z0,z1,z2,z170,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z6,z519]),(0,[z0,z1,z2,z520,z3,z5,z6]),(0,[z0,z465,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z285,z5,z131,z6]),(0,[z0,z1,z2,z96,z3,z148,z6]),(0,[z0,z1,z2,z3,z49,z6,z213])],[(0,[z50,z33,z1,z2,z3,z5,z6]),(0,[z84,z0,z1,z2,z3,z5,z60]),(1,[z0,z1,z2,z3,z5,z266]),(1,[z0,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z521,z3,z5,z6])],[(0,[z0,z1,z51,z2,z3,z15,z6]),(0,[z34,z0,z2,z86,z3,z5,z6]),(0,[z0,z1,z2,z43,z97,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z217]),(0,[z0,z1,z2,z3,z522,z5,z6])],[(0,[z33,z25,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z523,z3,z5,z6]),(0,[z0,z1,z2,z3,z524,z5,z6]),(0,[z0,z18,z1,z2,z3,z5,z6]),(0,[z143,z0,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z5,z6,z525]),(0,[z0,z1,z2,z3,z15,z307,z6]),(0,[z0,z1,z2,z526,z3,z5,z6]),(0,[z0,z1,z2,z527,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z68,z6])],[(0,[z528,z0,z1,z2,z3,z5,z6]),(0,[z529,z0,z1,z2,z3,z5,z6]),(1,[z466,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z96,z3,z5,z6]),(0,[z0,z1,z2,z3,z530,z5,z6])],[(0,[z63,z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z531,z6]),(0,[z0,z1,z532,z2,z3,z5,z6]),(0,[z263,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z533,z2,z3,z5,z6])],[(0,[z63,z0,z1,z2,z285,z3,z6]),(0,[z0,z1,z2,z81,z3,z5,z6]),(0,[z0,z1,z534,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z535,z5,z6]),(1,[z0,z1,z2,z3,z180,z6])]],
   [[(1,[z264,z0,z1,z2,z3,z6]),(0,[z0,z1,z261,z2,z3,z5,z6]),(0,[z0,z536,z1,z2,z3,z5,z6]),(0,[z537,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z15,z6,z538])],[(0,[z0,z1,z2,z3,z62,z5,z6]),(1,[z0,z1,z2,z358,z3,z6]),(0,[z0,z1,z2,z539,z3,z5,z6]),(0,[z0,z1,z2,z540,z3,z5,z6])],[(0,[z0,z51,z2,z3,z5,z307,z6]),(0,[z0,z1,z2,z3,z5,z541,z6]),(0,[z0,z1,z2,z3,z542,z5,z6]),(0,[z0,z1,z2,z3,z60,z6,z360]),(0,[z0,z1,z2,z3,z5,z6,z543]),(0,[z0,z1,z2,z43,z128,z5,z6]),(0,[z0,z1,z146,z3,z5,z68,z6])],[(0,[z1,z74,z2,z170,z3,z5,z6]),(0,[z0,z1,z2,z3,z544,z5,z6]),(0,[z0,z1,z2,z545,z3,z5,z6]),(0,[z0,z1,z2,z478,z3,z31,z6]),(1,[z0,z1,z2,z517,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z546]),(0,[z0,z1,z2,z3,z5,z6,z547])],[(0,[z34,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z548,z3,z5,z6]),(0,[z27,z0,z1,z2,z86,z5,z6])],[(0,[z33,z0,z25,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z549,z5,z6]),(0,[z0,z1,z2,z3,z550,z5,z6]),(0,[z0,z1,z2,z108,z3,z5,z6])],[(1,[z0,z336,z1,z2,z3,z6]),(0,[z73,z0,z1,z2,z3,z5,z551]),(0,[z0,z1,z2,z3,z5,z6,z552]),(0,[z0,z553,z1,z2,z3,z5,z6]),(0,[z0,z554,z1,z2,z3,z5,z6]),(0,[z0,z1,z146,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z5,z555,z6])],[(0,[z12,z0,z1,z2,z3,z15,z6]),(1,[z268,z0,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z556,z5,z6]),(0,[z0,z1,z2,z128,z3,z31,z6]),(0,[z0,z1,z2,z44,z3,z174,z6])],[(0,[z140,z0,z25,z2,z3,z5,z6]),(0,[z0,z1,z2,z557,z3,z5,z6]),(0,[z0,z1,z2,z3,z174,z31,z6]),(0,[z0,z1,z2,z558,z3,z5,z6])],[(0,[z0,z1,z2,z3,z559,z5,z6]),(0,[z0,z1,z2,z53,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z307,z6]),(0,[z0,z560,z1,z2,z3,z5,z6])],[(1,[z33,z25,z2,z3,z5,z6]),(0,[z7,z0,z149,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z561,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z562]),(0,[z0,z1,z30,z3,z5,z31,z6]),(1,[z20,z0,z1,z3,z15,z6]),(0,[z0,z1,z146,z2,z3,z180,z6])],[(0,[z0,z1,z2,z3,z5,z563,z6]),(0,[z0,z1,z2,z564,z3,z5,z6]),(0,[z0,z1,z565,z2,z3,z5,z6]),(0,[z0,z1,z127,z2,z3,z5,z6]),(0,[z0,z1,z138,z2,z128,z5,z6]),(0,[z0,z1,z2,z566,z3,z5,z6])],[(0,[z0,z25,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z170,z3,z15,z6]),(0,[z0,z1,z2,z3,z5,z567,z6]),(0,[z0,z1,z2,z568,z3,z5,z6]),(1,[z569,z1,z2,z3,z5,z6]),(0,[z512,z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z570,z3,z5,z6])],[(0,[z52,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z571,z2,z3,z5,z6]),(0,[z263,z0,z338,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z271,z6]),(0,[z0,z1,z2,z3,z31,z148,z6]),(0,[z572,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z152,z3,z5])],[(0,[z0,z1,z2,z3,z5,z17,z6]),(0,[z0,z1,z573,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z304,z5,z6]),(0,[z0,z1,z2,z3,z31,z6,z22]),(0,[z0,z1,z146,z2,z517,z5,z6])]],
   [[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z574,z5,z6]),(0,[z0,z1,z2,z575,z3,z5,z6]),(0,[z0,z1,z2,z43,z145,z5,z6]),(0,[z0,z1,z2,z3,z31,z576,z6])],[(0,[z0,z1,z2,z3,z5,z6,z577]),(1,[z0,z1,z2,z312,z5,z6]),(0,[z0,z1,z74,z2,z3,z132,z6]),(0,[z0,z1,z2,z578,z3,z5,z6])],[(0,[z63,z0,z1,z2,z3,z15,z6]),(0,[z579,z0,z1,z2,z3,z5,z6]),(0,[z580,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z581,z5,z6])],[(0,[z0,z1,z2,z582,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z49,z6]),(0,[z0,z1,z583,z2,z3,z5,z6]),(0,[z0,z584,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z585,z5,z6]),(0,[z73,z1,z2,z3,z54,z5,z6]),(0,[z12,z0,z1,z2,z3,z115,z6]),(0,[z27,z0,z2,z3,z28,z5,z6]),(0,[z140,z156,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z586,z6]),(0,[z0,z1,z2,z96,z3,z31,z6]),(0,[z0,z1,z2,z587,z3,z5,z6])],[(0,[z588,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z352,z5,z6]),(0,[z0,z1,z2,z3,z5,z589,z6]),(0,[z0,z1,z2,z3,z5,z590,z6]),(0,[z263,z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z285,z3,z148,z6])],[(0,[z7,z33,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z591]),(0,[z0,z1,z2,z3,z15,z60,z6]),(0,[z0,z1,z2,z81,z3,z31,z6]),(1,[z0,z1,z2,z3,z135,z6]),(0,[z0,z1,z2,z592,z3,z5,z6])],[(0,[z593,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z594,z2,z3,z5,z6]),(1,[z0,z13,z2,z3,z307,z6]),(0,[z0,z1,z2,z3,z5,z595,z6])],[(0,[z0,z1,z2,z3,z5,z596,z6]),(0,[z0,z1,z2,z3,z597,z5,z6]),(0,[z143,z0,z1,z2,z43,z3,z5]),(0,[z0,z1,z21,z2,z3,z355,z6]),(0,[z0,z1,z2,z285,z3,z5,z6])],[(0,[z0,z1,z138,z2,z145,z5,z6]),(0,[z0,z1,z2,z598,z3,z5,z6]),(0,[z0,z599,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z600,z6])],[(0,[z0,z1,z2,z601,z3,z5,z6]),(0,[z89,z0,z1,z74,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z222]),(0,[z34,z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z602,z5,z6])],[(0,[z603,z0,z1,z2,z3,z5,z6]),(0,[z12,z0,z1,z2,z96,z3,z6]),(0,[z143,z1,z2,z3,z5,z60,z6]),(0,[z0,z338,z2,z3,z5,z6,z56]),(0,[z0,z1,z2,z128,z3,z15,z6])],[(0,[z0,z1,z604,z2,z3,z5,z6]),(0,[z605,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z606,z3,z5,z6]),(0,[z0,z1,z2,z607,z3,z5,z6]),(0,[z0,z1,z2,z608,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z42,z6]),(0,[z339,z0,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z174,z15,z6])],[],[(0,[z63,z0,z1,z2,z3,z115,z6]),(0,[z0,z1,z144,z2,z3,z5,z6]),(0,[z0,z1,z2,z609,z3,z5,z6]),(0,[z0,z1,z2,z3,z209,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z610]),(0,[z0,z1,z611,z2,z3,z5,z6])]],
   [[(0,[z612,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z613,z5,z6]),(0,[z0,z1,z146,z21,z3,z5,z6])],[(0,[z89,z1,z51,z2,z3,z5,z6]),(0,[z1,z51,z2,z3,z5,z60,z6]),(0,[z0,z1,z2,z53,z3,z31,z6]),(0,[z140,z208,z1,z2,z3,z5,z6]),(0,[z0,z1,z614,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z378,z6]),(0,[z512,z0,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z615,z3,z5,z6]),(0,[z0,z1,z2,z43,z3,z5,z68]),(1,[z0,z1,z2,z44,z3,z213])],[(0,[z0,z1,z616,z2,z3,z5,z6])],[(0,[z0,z617,z1,z2,z3,z5,z6]),(0,[z0,z1,z127,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z6,z477]),(0,[z618,z0,z1,z2,z3,z5,z6])],[(0,[z1,z51,z2,z3,z8,z5,z6]),(0,[z0,z1,z2,z3,z31,z60,z6]),(0,[z0,z1,z2,z3,z619,z5,z6])],[(0,[z0,z1,z2,z3,z5,z620,z6]),(0,[z621,z0,z1,z2,z3,z5,z6]),(0,[z52,z0,z1,z2,z3,z31,z6]),(1,[z0,z149,z2,z3,z5,z6]),(0,[z0,z1,z2,z86,z145,z5,z6]),(0,[z0,z1,z2,z3,z31,z6,z56]),(0,[z622,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z467,z5,z6]),(0,[z0,z623,z1,z2,z3,z5,z6])],[(1,[z143,z1,z2,z3,z5,z60]),(0,[z0,z1,z14,z2,z3,z5,z6]),(0,[z624,z0,z1,z2,z3,z5,z6]),(0,[z140,z0,z1,z2,z3,z307,z6]),(0,[z625,z0,z1,z2,z3,z5,z6])],[(0,[z63,z12,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z626,z6]),(0,[z63,z0,z1,z2,z96,z3,z6]),(0,[z0,z1,z2,z526,z3,z15,z6]),(0,[z0,z1,z2,z527,z3,z15,z6]),(0,[z0,z1,z2,z3,z5,z6,z627])]],
   [[(0,[z92,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z628,z2,z3,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z96,z3,z15,z6])],[(0,[z629,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z630,z2,z3,z5,z6]),(0,[z0,z13,z1,z2,z3,z307,z6]),(0,[z263,z0,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z31,z31,z6]),(0,[z0,z631,z1,z2,z3,z5,z6])],[(0,[z33,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z632,z2,z3,z5,z6]),(0,[z0,z14,z2,z81,z3,z5,z6]),(0,[z0,z1,z2,z81,z3,z15,z6]),(0,[z0,z1,z2,z633,z3,z5,z6])],[(0,[z0,z422,z1,z2,z3,z5,z6]),(0,[z0,z16,z1,z2,z28,z5,z6]),(0,[z0,z1,z2,z285,z96,z5,z6]),(0,[z634,z0,z1,z2,z3,z5,z6])],[(0,[z635,z0,z1,z2,z3,z5,z6]),(1,[z92,z1,z2,z3,z5,z6]),(0,[z94,z0,z1,z2,z3,z5,z6]),(0,[z636,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z637,z3,z5,z6])],[(0,[z0,z1,z2,z638,z3,z5,z6]),(0,[z33,z89,z1,z2,z3,z5,z6]),(0,[z0,z639,z1,z2,z3,z5,z6])],[(0,[z34,z0,z1,z81,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z516,z6])],[(0,[z0,z1,z2,z3,z640,z5,z6]),(0,[z34,z0,z1,z2,z3,z15,z6]),(0,[z641,z0,z1,z2,z3,z5,z6])]],
   [[(1,[z0,z1,z2,z3,z5,z551]),(0,[z0,z1,z2,z3,z5,z642,z6]),(0,[z0,z1,z2,z3,z5,z158,z6]),(0,[z643,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z644,z3,z5,z6]),(0,[z0,z1,z2,z285,z3,z31,z6])],[(0,[z0,z1,z2,z3,z5,z6,z645]),(0,[z0,z1,z2,z3,z646,z5,z6]),(0,[z0,z13,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z647,z6])],[(0,[z0,z25,z9,z2,z3,z5,z6]),(0,[z648,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z288]),(0,[z0,z1,z2,z649,z3,z5,z6])],[(1,[z7,z1,z2,z53,z5,z6]),(0,[z650,z0,z1,z2,z3,z5,z6]),(0,[z651,z0,z1,z2,z3,z5,z6]),(0,[z652,z0,z1,z2,z3,z5,z6]),(0,[z0,z13,z2,z3,z5,z307,z6]),(0,[z0,z653,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z152,z3,z5,z241])],[(0,[z0,z1,z2,z53,z3,z15,z6]),(0,[z84,z0,z1,z2,z3,z5,z6]),(0,[z263,z0,z1,z2,z3,z5,z56])],[(0,[z0,z1,z2,z3,z5,z222,z22]),(0,[z0,z1,z2,z3,z5,z654,z6]),(0,[z0,z1,z2,z655,z3,z5,z6])],[(0,[z656,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z657,z6]),(0,[z0,z1,z658,z2,z3,z5,z6]),(0,[z0,z1,z659,z2,z3,z5,z6]),(0,[z0,z1,z2,z660,z3,z5,z6]),(0,[z0,z1,z127,z2,z3,z15,z6]),(0,[z0,z661,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z662,z2,z3,z5,z6])],[(0,[z0,z51,z2,z86,z3,z5,z6]),(0,[z52,z0,z1,z2,z3,z15,z6]),(1,[z0,z1,z30,z3,z31,z6])],[(0,[z0,z1,z663,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z353,z6]),(1,[z0,z1,z2,z43,z5,z241])],[(0,[z664,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z665,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z619,z31,z6]),(0,[z0,z1,z666,z2,z3,z5,z6])],[(0,[z0,z1,z667,z2,z3,z5,z6]),(0,[z7,z52,z1,z2,z3,z5,z6]),(0,[z668,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z669,z2,z3,z5,z6]),(0,[z263,z569,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z670,z5,z6]),(0,[z671,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z128,z53,z5,z6]),(0,[z0,z1,z2,z672,z3,z5,z6]),(0,[z0,z1,z14,z2,z3,z31,z6]),(0,[z0,z1,z30,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z518,z6])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z673,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z674,z3,z5,z6]),(0,[z33,z1,z2,z170,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z675])]],
   [[(0,[z0,z1,z676,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z677,z6]),(0,[z84,z1,z2,z3,z5,z6,z222]),(0,[z0,z678,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z128,z86,z5,z6])],[(0,[z33,z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z679,z5,z6]),(0,[z0,z1,z2,z3,z5,z307,z6]),(0,[z0,z1,z2,z633,z3,z31,z6]),(0,[z0,z1,z2,z43,z3,z5,z22])],[(0,[z0,z680,z1,z2,z3,z5,z6]),(0,[z0,z1,z681,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z38,z6])],[(0,[z0,z1,z2,z682,z3,z5,z6]),(0,[z683,z0,z1,z2,z3,z5,z6]),(0,[z94,z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z15,z148,z6]),(0,[z0,z1,z2,z3,z5,z6,z684])],[(0,[z0,z1,z2,z3,z685,z5,z6]),(0,[z0,z1,z2,z3,z15,z141,z6]),(0,[z0,z1,z2,z3,z15,z6,z22]),(0,[z0,z1,z2,z285,z3,z15,z6]),(0,[z0,z1,z686,z2,z3,z5,z6]),(1,[z0,z1,z2,z152,z5,z131]),(0,[z0,z1,z2,z687,z3,z5,z6])],[(0,[z688,z0,z1,z2,z3,z5,z6]),(0,[z1,z51,z2,z3,z54,z5,z6]),(0,[z0,z1,z2,z3,z168,z60,z6]),(0,[z0,z1,z2,z3,z5,z689,z6]),(1,[z0,z1,z2,z3,z467,z6]),(0,[z0,z1,z2,z598,z3,z15,z6]),(0,[z0,z1,z2,z3,z5,z6,z538]),(0,[z0,z1,z2,z3,z5,z690,z6]),(0,[z0,z1,z2,z122,z3,z5,z6]),(1,[z0,z1,z2,z3,z174,z49])],[(0,[z0,z1,z2,z3,z5,z691,z6]),(0,[z151,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z22]),(0,[z0,z1,z2,z3,z5,z692,z6])],[(0,[z27,z0,z51,z2,z3,z5,z6]),(0,[z0,z1,z124,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z576,z6]),(0,[z0,z1,z2,z3,z693,z5,z6]),(0,[z0,z1,z2,z3,z15,z5,z6])]],
   [[(0,[z63,z33,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z187,z3,z5,z6]),(0,[z694,z0,z1,z2,z3,z5,z6]),(0,[z0,z16,z2,z86,z3,z5,z6]),(0,[z0,z13,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z695,z6])],[(0,[z696,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z135,z5,z6]),(0,[z697,z0,z1,z2,z3,z5,z6])],[(0,[z698,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z699,z3,z5,z6]),(0,[z63,z1,z74,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z115,z6]),(0,[z0,z1,z2,z3,z5,z6,z700]),(1,[z94,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z355,z6])],[(0,[z0,z1,z2,z3,z5,z551,z6]),(0,[z701,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z138,z3,z145,z5,z6])],[(0,[z73,z0,z166,z2,z3,z5,z6]),(0,[z84,z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z702,z3,z5,z6]),(0,[z0,z1,z2,z3,z703,z5,z6])],[(0,[z0,z338,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z8,z145,z5,z6]),(0,[z0,z1,z2,z3,z5,z434,z6]),(0,[z0,z1,z2,z43,z285,z5,z6]),(0,[z0,z1,z2,z212,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z704]),(0,[z0,z1,z2,z705,z3,z5,z6]),(0,[z0,z338,z1,z2,z3,z5,z26]),(0,[z0,z569,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z124,z2,z3,z101,z6]),(0,[z27,z0,z2,z207,z5,z6])],[(0,[z0,z1,z2,z3,z707,z6]),(0,[z89,z1,z74,z3,z132,z6]),(0,[z0,z1,z2,z708,z5,z6]),(0,[z0,z1,z2,z3,z5,z709]),(0,[z0,z1,z2,z3,z6,z710]),(0,[z0,z1,z2,z5,z711,z241])],[(0,[z0,z1,z2,z3,z712,z6]),(0,[z89,z1,z416,z3,z5,z6]),(0,[z713,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z714,z5,z6]),(0,[z0,z2,z3,z5,z6,z715]),(0,[z716,z0,z2,z3,z5,z6])],[(0,[z92,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z717,z5,z6]),(0,[z0,z1,z2,z633,z139,z6])],[(0,[z0,z1,z2,z718,z5,z6]),(1,[z1,z2,z3,z719,z6]),(0,[z0,z1,z2,z239,z158,z6]),(0,[z0,z1,z2,z720,z5,z6]),(0,[z0,z1,z2,z44,z3,z538]),(0,[z0,z1,z2,z43,z5,z610])],[(0,[z0,z1,z607,z3,z31,z6])],[(0,[z0,z1,z2,z352,z101,z6]),(0,[z721,z0,z1,z2,z3,z6]),(0,[z0,z1,z722,z3,z5,z6]),(0,[z723,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z724])],[(0,[z0,z1,z2,z3,z5,z551]),(0,[z1,z74,z3,z431,z5,z6]),(0,[z0,z725,z2,z3,z5,z6]),(0,[z63,z1,z2,z3,z211,z6]),(0,[z726,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z727,z6]),(0,[z0,z1,z2,z3,z224,z195])]],
   [[(0,[z73,z1,z286,z3,z5,z6]),(0,[z0,z1,z2,z728,z5,z6]),(0,[z70,z1,z2,z3,z31,z6]),(0,[z0,z1,z729,z3,z5,z6]),(0,[z0,z730,z2,z3,z5,z6]),(0,[z0,z1,z2,z478,z434,z6])],[(0,[z0,z1,z2,z731,z5,z6]),(0,[z0,z1,z2,z732,z5,z6]),(0,[z0,z733,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z619,z49])],[(0,[z1,z51,z2,z117,z3,z5]),(0,[z0,z1,z2,z3,z31,z75]),(0,[z734,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z735,z6]),(0,[z0,z1,z146,z3,z209,z68])],[(0,[z70,z1,z2,z3,z5,z455])],[(0,[z0,z1,z2,z3,z736,z6]),(0,[z0,z1,z2,z152,z542,z5]),(0,[z737,z1,z2,z3,z5,z6]),(0,[z738,z1,z2,z3,z5,z6]),(0,[z27,z422,z2,z28,z5,z6]),(0,[z0,z1,z2,z3,z739,z6]),(0,[z0,z1,z2,z3,z740,z6]),(0,[z0,z1,z2,z342,z5,z131]),(0,[z0,z1,z2,z741,z5,z6]),(0,[z0,z1,z2,z285,z742,z6])],[(0,[z140,z0,z336,z2,z3,z6]),(0,[z33,z25,z2,z3,z15,z6]),(0,[z0,z743,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z744]),(0,[z0,z1,z2,z3,z745,z6]),(0,[z0,z1,z2,z43,z602,z5])],[(0,[z0,z1,z128,z746,z5,z6]),(0,[z0,z1,z2,z3,z747,z6]),(0,[z0,z1,z2,z748,z3,z6]),(0,[z749,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z750,z5,z6]),(0,[z0,z9,z667,z3,z5,z6]),(0,[z63,z124,z2,z3,z5,z6]),(0,[z569,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z108,z31,z6]),(0,[z0,z1,z2,z751,z3,z31])]],
   [[(0,[z0,z124,z2,z3,z5,z551]),(0,[z0,z752,z2,z3,z5,z6]),(0,[z0,z1,z30,z3,z31,z6]),(0,[z1,z2,z3,z31,z753,z6])],[(0,[z143,z465,z2,z3,z5,z60]),(0,[z143,z1,z2,z3,z60,z360]),(0,[z0,z1,z2,z754,z5,z6]),(0,[z755,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z756]),(0,[z0,z1,z2,z44,z230,z3])],[(0,[z0,z1,z376,z3,z31,z6])],[(0,[z1,z74,z757,z3,z5,z6]),(0,[z0,z149,z2,z3,z31,z6])],[(0,[z264,z1,z2,z3,z54,z6]),(0,[z0,z1,z2,z3,z5,z758]),(0,[z0,z1,z514,z3,z15,z6]),(0,[z34,z70,z81,z3,z5,z6]),(0,[z0,z1,z2,z3,z759,z6]),(0,[z0,z1,z2,z3,z760,z6])],[(0,[z124,z2,z170,z3,z5,z6]),(0,[z0,z1,z2,z761,z5,z6]),(0,[z1,z2,z3,z719,z115,z6]),(0,[z0,z1,z2,z3,z6,z217]),(0,[z762,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z352,z5,z551]),(0,[z0,z1,z2,z763,z3,z6]),(0,[z0,z1,z2,z3,z5,z764]),(0,[z94,z1,z2,z3,z115,z6]),(0,[z0,z1,z2,z3,z765,z6]),(0,[z766,z1,z2,z3,z5,z6]),(0,[z767,z1,z2,z3,z5,z6]),(0,[z0,z1,z445,z3,z31,z6]),(0,[z0,z768,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z271,z195]),(0,[z769,z1,z2,z3,z5,z6]),(0,[z770,z1,z2,z3,z5,z6])]],
   [[(0,[z413,z0,z81,z3,z5,z6]),(0,[z0,z1,z2,z771,z3,z6]),(0,[z772,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z773]),(0,[z0,z1,z2,z3,z5,z774]),(0,[z1,z2,z775,z8,z5,z6]),(0,[z0,z1,z2,z3,z224,z6])],[(0,[z0,z1,z2,z3,z719,z6]),(0,[z0,z1,z2,z3,z5,z776]),(0,[z0,z1,z2,z108,z5,z22])],[(0,[z0,z1,z2,z777,z5,z6]),(0,[z92,z1,z2,z3,z31,z6]),(0,[z140,z94,z1,z2,z3,z6]),(0,[z0,z1,z2,z96,z6,z490])],[(0,[z0,z1,z2,z117,z3,z15]),(0,[z778,z1,z2,z3,z5,z6]),(0,[z779,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z780,z5,z6]),(0,[z0,z1,z2,z152,z5,z131])],[(0,[z0,z1,z2,z3,z6,z781]),(0,[z70,z1,z2,z3,z5,z266]),(0,[z0,z1,z2,z3,z467,z6]),(0,[z0,z1,z2,z3,z174,z49])],[(0,[z0,z1,z162,z3,z31,z6]),(0,[z782,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z31,z551]),(0,[z0,z783,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z784]),(0,[z1,z2,z3,z5,z785,z6]),(0,[z0,z1,z2,z751,z3,z5]),(0,[z94,z1,z2,z96,z3,z6])],[(0,[z0,z1,z746,z145,z5,z6]),(0,[z0,z1,z127,z128,z5,z195]),(0,[z0,z1,z2,z147,z3,z31])]],
   [[(0,[z0,z1,z3,z15,z431,z6]),(0,[z84,z1,z2,z48,z3,z5]),(0,[z0,z1,z127,z746,z5,z6])],[(0,[z0,z1,z786,z3,z5,z6]),(0,[z0,z1,z2,z186,z187,z3]),(0,[z0,z1,z2,z3,z158,z455]),(0,[z0,z1,z2,z3,z355,z6]),(0,[z0,z1,z2,z43,z285,z44]),(0,[z0,z1,z2,z3,z6,z787])],[(0,[z788,z422,z1,z2,z3,z6]),(0,[z94,z1,z2,z3,z211,z6]),(0,[z0,z1,z2,z3,z15,z789]),(0,[z0,z366,z2,z3,z229,z6]),(0,[z0,z1,z2,z3,z742,z6])],[(0,[z466,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z790,z5,z6]),(0,[z0,z1,z3,z746,z5,z6])],[(0,[z18,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z791]),(0,[z0,z1,z2,z186,z3,z6]),(0,[z0,z1,z2,z792,z3,z5]),(0,[z0,z1,z2,z212,z5,z6])],[(0,[z0,z1,z2,z3,z793,z6]),(0,[z794,z1,z2,z3,z5,z6])],[(0,[z84,z1,z2,z3,z5,z452]),(0,[z0,z1,z2,z187,z3,z15]),(0,[z795,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z224,z288])],[(0,[z0,z796,z2,z3,z5,z6]),(0,[z0,z149,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z797,z6]),(0,[z0,z1,z2,z285,z147,z5]),(0,[z0,z1,z2,z5,z131,z711])]],
   [[(0,[z0,z1,z2,z3,z5,z798]),(0,[z0,z1,z2,z3,z799,z6]),(0,[z0,z1,z2,z3,z800,z6]),(0,[z339,z0,z2,z3,z141,z6]),(0,[z0,z1,z2,z3,z271,z6]),(0,[z0,z1,z127,z128,z224,z6]),(0,[z0,z1,z2,z754,z31,z6]),(0,[z0,z1,z2,z108,z180,z6])],[(0,[z0,z18,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z801]),(0,[z0,z1,z2,z3,z17,z6]),(0,[z0,z802,z2,z3,z5,z6]),(0,[z0,z1,z2,z212,z44,z6])],[(0,[z466,z149,z2,z3,z5,z6]),(0,[z27,z0,z2,z28,z5,z6])],[(0,[z0,z1,z2,z803,z3,z6]),(0,[z70,z2,z86,z3,z5,z6]),(0,[z804,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z31,z6,z805]),(0,[z94,z806,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z735,z22])],[(0,[z0,z1,z2,z3,z807,z6]),(0,[z63,z1,z2,z3,z522,z6]),(0,[z84,z1,z2,z3,z5,z784]),(0,[z0,z1,z303,z3,z5,z22]),(0,[z0,z1,z2,z527,z3,z538])],[(0,[z0,z808,z2,z3,z5,z6]),(0,[z0,z1,z2,z207,z5,z455]),(0,[z0,z1,z2,z3,z809,z6]),(0,[z0,z1,z2,z810,z3,z5]),(0,[z0,z1,z2,z3,z5,z811]),(0,[z0,z1,z2,z3,z812,z6]),(0,[z0,z768,z2,z3,z31,z6])],[(0,[z12,z1,z2,z521,z3,z6]),(0,[z92,z1,z2,z3,z15,z6]),(0,[z0,z2,z3,z5,z6,z813])],[(0,[z0,z1,z3,z693,z31,z6]),(0,[z0,z16,z2,z814,z5,z6]),(0,[z0,z1,z2,z3,z815,z6])]],
   [[(0,[z0,z1,z2,z96,z685,z6]),(0,[z0,z816,z2,z3,z5,z6])],[(0,[z33,z817,z2,z3,z5,z6]),(0,[z0,z1,z2,z818,z5,z6]),(0,[z0,z1,z2,z3,z6,z819]),(0,[z0,z1,z2,z3,z5,z820]),(0,[z821,z1,z2,z3,z5,z6]),(0,[z0,z14,z822,z3,z5,z6]),(0,[z823,z1,z2,z3,z5,z6]),(0,[z824,z1,z2,z3,z5,z6]),(0,[z140,z208,z2,z3,z141,z6]),(0,[z0,z1,z443,z128,z5,z6]),(0,[z0,z1,z2,z43,z5,z711]),(1,[z0,z1,z2,z43,z122])],[(0,[z0,z1,z2,z312,z62,z6]),(0,[z0,z1,z2,z3,z15,z551]),(0,[z0,z1,z2,z3,z5,z825]),(0,[z0,z1,z2,z3,z158,z266]),(0,[z778,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z152,z31,z131])],[(0,[z0,z1,z2,z3,z5,z826]),(0,[z0,z1,z2,z3,z827,z6]),(0,[z0,z1,z2,z828,z5,z6]),(0,[z829,z0,z1,z2,z3,z6]),(0,[z0,z1,z660,z3,z15,z6]),(0,[z830,z1,z2,z3,z5,z6])],[(0,[z50,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z831]),(0,[z0,z733,z2,z3,z15,z6]),(0,[z0,z1,z2,z96,z742,z6]),(0,[z0,z1,z2,z43,z217,z241])],[(0,[z0,z1,z2,z3,z5,z832]),(0,[z0,z1,z2,z312,z5,z75]),(1,[z1,z2,z775,z5,z6]),(1,[z0,z2,z3,z5,z811])],[(0,[z0,z1,z2,z833,z3,z6]),(0,[z0,z1,z2,z3,z834,z6]),(0,[z0,z1,z2,z3,z835,z6]),(0,[z0,z1,z2,z3,z5,z836]),(0,[z837,z1,z2,z3,z5,z6]),(0,[z0,z13,z2,z3,z229,z6]),(0,[z0,z1,z2,z3,z271,z288]),(1,[z0,z1,z3,z5,z735])],[(0,[z0,z838,z2,z3,z5,z6]),(0,[z34,z0,z822,z3,z5,z6]),(0,[z0,z1,z2,z741,z15,z6])]],
   [[(0,[z0,z1,z2,z839,z3,z6]),(0,[z0,z1,z2,z840,z3,z5]),(0,[z0,z1,z127,z128,z271,z6]),(0,[z0,z1,z2,z3,z5,z841]),(0,[z0,z1,z2,z96,z97,z6])],[(0,[z33,z1,z2,z358,z3,z6]),(0,[z0,z1,z2,z312,z101,z6]),(0,[z0,z842,z2,z3,z5,z6])],[(0,[z73,z166,z170,z3,z5,z6]),(0,[z0,z661,z2,z86,z5,z6]),(0,[z0,z1,z2,z3,z843,z6])],[(0,[z0,z1,z2,z117,z3,z31]),(0,[z0,z1,z30,z3,z844,z6]),(0,[z0,z1,z2,z212,z31,z6]),(0,[z0,z1,z2,z43,z122,z3])],[(0,[z0,z1,z2,z3,z5,z845]),(0,[z0,z1,z2,z3,z846,z6]),(0,[z0,z1,z2,z3,z5,z847]),(0,[z0,z848,z2,z3,z5,z6]),(0,[z794,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z49,z164])],[(0,[z849,z0,z1,z2,z3,z6]),(0,[z52,z1,z2,z186,z8,z6]),(0,[z593,z1,z2,z53,z5,z6]),(0,[z0,z1,z2,z850,z3,z5]),(0,[z0,z1,z851,z3,z5,z6]),(0,[z0,z338,z2,z3,z5,z811]),(0,[z0,z1,z2,z3,z852,z31]),(0,[z0,z1,z2,z3,z853,z6])],[(0,[z0,z231,z2,z86,z5,z6]),(0,[z0,z1,z2,z207,z5,z266]),(0,[z0,z1,z2,z3,z5,z854]),(0,[z0,z1,z2,z3,z855,z6]),(0,[z0,z1,z127,z128,z5,z288]),(0,[z0,z1,z2,z44,z3,z488]),(0,[z0,z1,z2,z3,z856,z213])],[(0,[z0,z124,z2,z3,z5,z75]),(0,[z0,z857,z2,z3,z5,z6])]],
   [[(0,[z0,z858,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z859]),(0,[z0,z18,z2,z3,z31,z6]),(0,[z860,z1,z2,z3,z5,z6]),(0,[z788,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z861]),(0,[z0,z1,z2,z862,z3,z6]),(0,[z863,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z864,z6]),(0,[z0,z865,z2,z3,z5,z6]),(0,[z0,z1,z2,z866,z3,z6]),(0,[z27,z0,z2,z28,z31,z6]),(0,[z0,z1,z2,z3,z15,z764]),(0,[z0,z1,z2,z285,z518,z6])],[(0,[z579,z25,z2,z3,z5,z6]),(0,[z70,z9,z2,z3,z5,z6]),(0,[z0,z1,z55,z3,z31,z6]),(0,[z0,z1,z138,z746,z5,z6]),(0,[z94,z806,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z735]),(0,[z0,z1,z2,z5,z6,z129])],[(0,[z0,z1,z2,z3,z867,z6]),(0,[z0,z1,z2,z478,z148,z6])],[(0,[z0,z144,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z132,z6]),(0,[z0,z1,z2,z3,z295,z213]),(0,[z0,z1,z2,z239,z246,z6]),(0,[z0,z1,z2,z5,z6,z868]),(0,[z0,z1,z21,z3,z355,z22])],[(0,[z0,z1,z2,z352,z5,z75]),(1,[z0,z1,z2,z5,z711])],[(0,[z151,z1,z2,z3,z54,z6]),(0,[z869,z569,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z870]),(0,[z0,z1,z2,z152,z15,z131])],[(0,[z0,z1,z2,z3,z246,z6]),(0,[z0,z1,z2,z3,z871,z6]),(0,[z0,z322,z2,z3,z307,z6]),(0,[z0,z816,z2,z3,z31,z6]),(0,[z1,z2,z3,z5,z753,z6]),(0,[z0,z1,z2,z517,z209,z6]),(0,[z0,z1,z2,z97,z6,z24]),(0,[z0,z1,z2,z3,z5,z711])]],
   [[(0,[z0,z1,z2,z3,z872,z6]),(0,[z0,z1,z2,z239,z5,z266]),(0,[z0,z1,z3,z15,z137,z6]),(0,[z0,z1,z2,z122,z152,z3])],[(0,[z156,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z312,z5,z551]),(0,[z0,z1,z822,z3,z5,z6]),(0,[z0,z1,z2,z3,z873,z6])],[(0,[z0,z1,z2,z3,z874,z6]),(0,[z0,z1,z2,z775,z5,z6]),(0,[z0,z1,z2,z117,z3,z5]),(0,[z0,z1,z2,z3,z875,z6]),(0,[z0,z1,z2,z3,z158,z6]),(0,[z0,z1,z2,z828,z31,z6]),(0,[z0,z1,z2,z3,z227,z282]),(0,[z0,z1,z2,z147,z96,z3])],[(0,[z50,z51,z2,z3,z31,z6]),(0,[z268,z0,z2,z207,z5,z6]),(0,[z0,z1,z2,z3,z876,z6]),(0,[z0,z1,z2,z877,z5,z6])],[(0,[z0,z59,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z852,z5]),(0,[z94,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z390,z3,z213]),(0,[z0,z1,z3,z10,z15,z6])],[(0,[z0,z166,z2,z3,z5,z6]),(0,[z73,z1,z757,z3,z5,z6]),(0,[z0,z1,z2,z3,z878,z6]),(0,[z0,z1,z2,z3,z879,z6]),(0,[z0,z880,z2,z3,z5,z6]),(0,[z0,z2,z86,z207,z5,z6]),(0,[z0,z2,z3,z5,z811,z56])],[(0,[z0,z1,z2,z3,z881,z6])],[(0,[z199,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z882,z5,z6]),(0,[z0,z1,z2,z3,z5,z883]),(0,[z0,z1,z2,z3,z5,z884]),(0,[z0,z1,z2,z3,z885,z6]),(0,[z0,z1,z2,z212,z15,z6])]],
   [[(0,[z0,z1,z2,z3,z886,z6]),(0,[z73,z1,z170,z3,z5,z6]),(0,[z0,z1,z328,z3,z31,z6]),(0,[z61,z1,z2,z8,z5,z6]),(0,[z0,z1,z383,z3,z15,z6]),(0,[z0,z1,z443,z3,z5,z68]),(0,[z0,z1,z2,z742,z148,z6]),(0,[z0,z887,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z784,z222]),(1,[z0,z822,z3,z5,z6])],[(0,[z0,z888,z2,z3,z5,z6]),(0,[z0,z889,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z195]),(0,[z0,z796,z2,z3,z15,z6])],[(0,[z94,z13,z1,z2,z3,z6]),(0,[z0,z1,z2,z890,z3,z6]),(0,[z0,z1,z2,z891,z5,z6]),(0,[z0,z892,z2,z3,z5,z6])],[(0,[z1,z51,z2,z3,z168,z6]),(0,[z0,z1,z2,z893,z3,z6]),(0,[z0,z1,z2,z894,z3,z5]),(0,[z0,z18,z2,z3,z15,z6]),(0,[z0,z2,z3,z814,z5,z6]),(0,[z0,z1,z2,z526,z382,z6]),(0,[z0,z895,z2,z3,z5,z6])],[(0,[z0,z16,z2,z86,z5,z6]),(0,[z27,z0,z2,z28,z15,z6]),(0,[z569,z2,z3,z5,z26,z6])],[(0,[z208,z1,z2,z3,z5,z6]),(0,[z0,z1,z573,z128,z5,z6]),(0,[z0,z1,z2,z207,z5,z6]),(0,[z0,z1,z2,z3,z896,z6]),(0,[z0,z1,z2,z897,z5,z6]),(0,[z0,z1,z2,z3,z5,z898]),(0,[z0,z1,z2,z3,z209,z6]),(0,[z0,z1,z2,z3,z6,z899])],[(0,[z63,z1,z2,z3,z101,z6]),(0,[z0,z1,z2,z900,z5,z6])]],
   [[(0,[z264,z208,z1,z2,z3,z6]),(1,[z1,z757,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z901]),(0,[z0,z1,z2,z3,z5,z902]),(0,[z1,z2,z3,z211,z5,z6]),(0,[z0,z1,z2,z3,z903,z6]),(0,[z0,z2,z3,z5,z811,z6]),(0,[z0,z1,z2,z212,z44,z5])],[(0,[z0,z1,z2,z117,z145,z5]),(0,[z0,z1,z2,z3,z5,z904]),(0,[z0,z1,z2,z3,z6,z905]),(0,[z258,z0,z1,z3,z15,z6]),(0,[z0,z1,z3,z15,z844,z6]),(0,[z0,z1,z146,z3,z5,z68])],[(0,[z0,z144,z2,z3,z31,z6]),(0,[z906,z1,z2,z3,z5,z6]),(0,[z0,z1,z499,z3,z31,z6]),(0,[z0,z907,z2,z3,z5,z6])],[(0,[z0,z166,z2,z352,z5,z6]),(0,[z0,z908,z2,z3,z5,z6]),(0,[z94,z1,z2,z3,z54,z6]),(0,[z909,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z910,z3,z6])],[(0,[z33,z149,z2,z3,z5,z6]),(0,[z0,z911,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z912]),(0,[z913,z1,z2,z3,z5,z6]),(0,[z0,z1,z276,z145,z5,z6]),(0,[z0,z1,z2,z3,z31,z870]),(0,[z0,z1,z2,z5,z131,z675])],[(0,[z0,z1,z2,z5,z6,z914]),(0,[z915,z1,z2,z3,z5,z6])],[(0,[z50,z51,z2,z3,z15,z6]),(0,[z70,z1,z2,z3,z15,z6]),(0,[z34,z0,z81,z3,z246,z6]),(0,[z0,z1,z2,z3,z5,z916]),(0,[z0,z1,z172,z3,z31,z6]),(0,[z917,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z239,z5,z6]),(0,[z0,z822,z81,z3,z5,z6]),(0,[z0,z1,z2,z3,z918,z6]),(1,[z0,z2,z3,z919,z6]),(0,[z0,z2,z3,z919,z307,z6]),(0,[z156,z1,z2,z3,z31,z6]),(0,[z0,z1,z138,z145,z5,z6]),(0,[z0,z1,z920,z3,z5,z6])],[(0,[z247,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z75]),(0,[z7,z149,z2,z53,z5,z6]),(0,[z0,z1,z2,z3,z246,z455]),(0,[z1,z2,z3,z921,z5,z6])],[(0,[z0,z1,z2,z3,z922,z6]),(0,[z34,z0,z81,z3,z158,z6]),(0,[z1,z2,z923,z3,z5,z6])],[(0,[z89,z1,z74,z3,z5,z6]),(0,[z52,z1,z2,z117,z8,z5]),(0,[z0,z59,z2,z3,z31,z6])],[(0,[z0,z166,z2,z3,z31,z6]),(0,[z12,z1,z2,z3,z54,z6])],[(0,[z0,z1,z2,z924,z3,z5]),(0,[z0,z1,z2,z3,z925,z6]),(0,[z34,z92,z81,z3,z5,z6]),(0,[z926,z1,z2,z3,z5,z6]),(0,[z140,z0,z2,z3,z919,z6])],[(0,[z0,z1,z2,z3,z927,z6]),(0,[z928,z1,z2,z3,z5,z6]),(0,[z0,z929,z1,z2,z3,z6]),(0,[z0,z1,z2,z108,z15,z6]),(0,[z0,z930,z2,z3,z5,z6])],[(0,[z50,z264,z51,z2,z3,z6]),(0,[z0,z336,z261,z2,z3,z6]),(0,[z73,z1,z170,z3,z31,z6]),(0,[z0,z1,z2,z3,z931,z6]),(0,[z84,z1,z2,z3,z5,z222]),(0,[z94,z1,z3,z15,z31,z6]),(0,[z94,z1,z2,z633,z3,z6])]],
   [[(0,[z0,z261,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z932,z6]),(0,[z0,z1,z933,z3,z5,z6]),(0,[z0,z1,z2,z3,z934,z6])],[(0,[z0,z1,z2,z935,z3,z5]),(0,[z0,z338,z2,z3,z5,z71]),(0,[z1,z2,z3,z5,z60,z784]),(0,[z936,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z31,z195]),(0,[z0,z1,z3,z5,z68,z735]),(0,[z0,z1,z2,z3,z5,z356])],[(0,[z0,z1,z937,z2,z5,z6]),(0,[z0,z1,z2,z938,z3,z6]),(0,[z939,z0,z1,z2,z3,z6]),(0,[z305,z0,z2,z3,z171,z6])],[(0,[z0,z1,z2,z940,z5,z6]),(0,[z863,z1,z2,z3,z15,z6])],[(0,[z466,z25,z2,z3,z5,z6]),(0,[z27,z466,z2,z28,z5,z6]),(0,[z0,z16,z2,z86,z31,z6]),(0,[z0,z2,z3,z941,z5,z6])],[(0,[z0,z1,z2,z942,z5,z6]),(0,[z143,z1,z2,z3,z5,z784]),(0,[z0,z1,z2,z207,z31,z6]),(0,[z140,z0,z2,z3,z141,z6]),(0,[z208,z1,z2,z3,z31,z6]),(0,[z263,z0,z2,z3,z5,z811]),(0,[z0,z138,z304,z145,z5,z6]),(0,[z943,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z122,z131,z6])],[(0,[z0,z1,z944,z2,z3,z5]),(0,[z0,z945,z2,z3,z5,z6]),(0,[z0,z1,z2,z117,z128,z5]),(0,[z107,z1,z2,z3,z5,z222]),(0,[z34,z0,z81,z207,z5,z6]),(0,[z0,z1,z2,z3,z946,z6]),(0,[z939,z569,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z947,z6]),(0,[z948,z1,z2,z3,z5,z6])],[(0,[z89,z124,z2,z3,z5,z6]),(0,[z0,z949,z2,z3,z5,z6]),(0,[z0,z144,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z950,z6]),(0,[z339,z0,z2,z3,z78,z6]),(0,[z0,z1,z2,z43,z122,z6])]],
   [[(0,[z89,z1,z757,z3,z5,z6]),(0,[z0,z9,z14,z3,z5,z6]),(0,[z1,z2,z3,z211,z31,z6]),(0,[z0,z1,z2,z3,z951,z6])],[(0,[z0,z1,z2,z3,z952,z6]),(0,[z0,z1,z2,z953,z5,z6]),(0,[z0,z1,z2,z3,z5,z288]),(0,[z0,z1,z146,z3,z31,z68]),(0,[z0,z2,z3,z31,z954,z6]),(0,[z0,z1,z2,z147,z3,z5])],[(0,[z19,z51,z2,z3,z5,z6]),(0,[z94,z1,z2,z3,z101,z6]),(0,[z0,z1,z2,z3,z246,z266]),(0,[z0,z1,z505,z3,z15,z6])],[(0,[z0,z955,z2,z3,z5,z6]),(0,[z0,z1,z127,z128,z5,z6])],[(0,[z156,z1,z2,z3,z15,z6]),(0,[z0,z1,z663,z3,z31,z6]),(0,[z0,z1,z2,z3,z956,z6]),(0,[z957,z1,z2,z3,z5,z6])],[(0,[z1,z2,z757,z3,z5,z6]),(0,[z268,z0,z2,z28,z5,z6]),(0,[z0,z1,z2,z958,z3,z6]),(0,[z959,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z960,z6])],[(0,[z0,z464,z2,z3,z5,z56]),(0,[z0,z1,z2,z3,z961,z6]),(0,[z917,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z962,z3,z15]),(0,[z0,z1,z963,z3,z5,z6])],[(0,[z0,z1,z2,z3,z964,z6]),(0,[z0,z59,z2,z3,z15,z6]),(0,[z0,z1,z2,z239,z31,z6]),(0,[z0,z2,z3,z304,z5,z6]),(0,[z0,z1,z138,z145,z31,z6]),(0,[z0,z1,z2,z965,z5,z6])]],
   [[(1,[z817,z2,z3,z5,z6]),(0,[z0,z166,z2,z3,z15,z6]),(0,[z0,z1,z2,z966,z5,z6]),(0,[z967,z0,z2,z3,z5,z6]),(0,[z34,z0,z81,z239,z5,z6]),(0,[z247,z1,z2,z3,z31,z6]),(0,[z968,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z969]),(0,[z63,z1,z2,z3,z719,z6]),(0,[z0,z1,z2,z3,z970,z6]),(0,[z0,z1,z2,z3,z971,z6]),(0,[z27,z0,z2,z814,z5,z6]),(0,[z263,z0,z2,z3,z5,z26]),(0,[z1,z2,z923,z3,z31,z6]),(0,[z0,z1,z2,z390,z3,z477]),(0,[z0,z1,z2,z43,z5,z444])],[(0,[z89,z1,z74,z3,z31,z6]),(0,[z0,z1,z2,z239,z5,z455]),(0,[z0,z1,z2,z43,z5,z446])],[(0,[z0,z1,z146,z3,z5,z735])],[],[(0,[z1,z2,z775,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z455]),(0,[z0,z1,z2,z972,z5,z6]),(0,[z263,z569,z2,z3,z5,z26]),(0,[z0,z1,z2,z3,z15,z195])],[(0,[z7,z1,z2,z423,z5,z6]),(0,[z0,z1,z2,z3,z973,z6]),(0,[z84,z1,z2,z3,z31,z222]),(0,[z0,z1,z2,z3,z6,z974]),(0,[z0,z1,z2,z44,z3,z856])],[(0,[z0,z261,z2,z3,z31,z6]),(0,[z738,z1,z2,z3,z38,z6]),(0,[z0,z1,z2,z3,z975,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z976]),(0,[z0,z1,z2,z3,z62,z75]),(0,[z0,z1,z280,z3,z31,z6]),(0,[z936,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z31,z356])],[(0,[z0,z1,z2,z207,z15,z6]),(0,[z0,z1,z2,z977,z5,z6]),(0,[z208,z1,z2,z3,z15,z6])],[(0,[z140,z156,z2,z3,z141,z6]),(0,[z0,z1,z2,z3,z6,z978])],[(0,[z400,z0,z2,z3,z5,z26])],[(0,[z0,z1,z2,z979,z3,z6]),(0,[z0,z1,z2,z3,z980,z6]),(0,[z0,z1,z2,z3,z5,z981])],[(0,[z0,z1,z2,z3,z5,z982]),(0,[z0,z1,z2,z3,z5,z983]),(0,[z0,z1,z659,z145,z5,z6]),(0,[z0,z1,z2,z984,z5,z6]),(0,[z0,z1,z146,z3,z15,z68])],[(0,[z0,z1,z2,z3,z49,z856])],[(0,[z0,z1,z2,z3,z101,z75]),(0,[z1,z2,z53,z775,z5,z6]),(0,[z0,z9,z14,z3,z31,z6]),(0,[z0,z1,z3,z252,z15,z6]),(0,[z0,z1,z21,z3,z5,z735]),(0,[z0,z1,z2,z212,z174,z5])]],
   [[(0,[z817,z51,z2,z3,z5,z6]),(0,[z0,z985,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z31,z288]),(0,[z0,z1,z2,z3,z619,z516])],[(0,[z63,z264,z1,z2,z3,z6]),(0,[z63,z1,z2,z3,z17,z6]),(0,[z0,z1,z2,z187,z3,z31]),(0,[z0,z1,z2,z986,z5,z6])],[(0,[z0,z1,z2,z3,z987,z6]),(0,[z33,z18,z2,z3,z5,z6]),(0,[z0,z1,z127,z128,z31,z6]),(0,[z0,z1,z146,z3,z180,z68])],[(0,[z33,z471,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z988,z6]),(0,[z989,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z239,z15,z6]),(0,[z0,z1,z2,z990,z5,z6]),(0,[z0,z1,z138,z145,z15,z6]),(0,[z94,z1,z30,z3,z31,z6]),(0,[z94,z1,z2,z3,z6,z213]),(0,[z0,z991,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z992,z6]),(0,[z247,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z285,z148,z6])],[(0,[z0,z1,z2,z3,z993,z6]),(0,[z12,z0,z1,z2,z212,z6]),(0,[z263,z247,z2,z3,z5,z26]),(0,[z0,z1,z2,z3,z159,z6])],[(0,[z85,z51,z2,z3,z5,z6]),(0,[z994,z0,z1,z2,z3,z6]),(0,[z89,z1,z74,z3,z15,z6]),(0,[z0,z995,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z266]),(0,[z0,z996,z2,z3,z5,z6]),(0,[z0,z2,z3,z304,z31,z6]),(0,[z0,z1,z2,z965,z31,z6]),(0,[z0,z1,z146,z517,z5,z68])],[(0,[z0,z1,z2,z3,z997,z6]),(0,[z0,z166,z2,z312,z5,z6]),(0,[z0,z1,z583,z3,z15,z6])]],
   [[(0,[z0,z1,z2,z5,z998,z6]),(0,[z0,z1,z2,z999,z5,z6]),(0,[z0,z1,z2,z3,z6,z1000]),(0,[z1001,z1,z2,z3,z5,z6]),(0,[z263,z0,z2,z3,z31,z26]),(0,[z0,z1,z2,z3,z174,z470])],[(0,[z343,z51,z2,z3,z5,z6]),(0,[z1002,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1003,z6]),(0,[z1,z2,z3,z921,z38,z6]),(0,[z1004,z1,z2,z3,z5,z6])],[(0,[z73,z1,z170,z312,z5,z6]),(0,[z84,z1,z2,z3,z15,z222]),(0,[z0,z1,z2,z3,z1005,z6]),(0,[z0,z1,z502,z128,z5,z6])],[(0,[z0,z1,z2,z3,z1006,z6]),(0,[z0,z261,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z180,z6])],[(0,[z264,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z62,z551]),(0,[z0,z1,z2,z3,z5,z1007]),(0,[z0,z1,z2,z3,z168,z6]),(0,[z0,z1,z2,z3,z31,z455]),(1,[z0,z2,z814,z5,z6]),(0,[z0,z1,z331,z3,z31,z6]),(0,[z0,z1,z2,z3,z15,z356])],[(0,[z0,z1,z2,z3,z1008,z6]),(0,[z0,z1,z2,z3,z5,z1009]),(0,[z1,z2,z3,z5,z719,z6]),(0,[z84,z144,z2,z3,z5,z6]),(0,[z34,z0,z81,z3,z5,z455])],[(0,[z0,z1,z286,z3,z15,z6])],[(0,[z0,z1,z255,z3,z31,z6]),(0,[z0,z1,z2,z517,z5,z6]),(0,[z0,z2,z3,z941,z15,z6])]],
   [[(0,[z1,z51,z2,z358,z3,z6]),(0,[z156,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z187,z3,z5]),(0,[z0,z1,z2,z1010,z5,z6]),(0,[z268,z0,z138,z145,z5,z6]),(0,[z0,z1,z296,z3,z15,z6]),(0,[z943,z0,z2,z3,z15,z6])],[(0,[z149,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1011,z6]),(0,[z0,z1,z205,z3,z31,z6]),(1,[z0,z1,z3,z844,z6])],[(0,[z0,z1,z2,z5,z6,z1012]),(0,[z0,z9,z822,z3,z5,z6]),(0,[z0,z2,z86,z381,z5,z6]),(0,[z0,z2,z814,z28,z5,z6]),(0,[z0,z1,z2,z3,z5,z1013]),(0,[z0,z1,z2,z3,z174,z282])],[(0,[z0,z1,z2,z3,z101,z551]),(0,[z0,z1,z2,z1014,z5,z6]),(0,[z143,z144,z2,z3,z5,z60]),(0,[z268,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z919,z6])],[(0,[z73,z124,z170,z3,z5,z6]),(0,[z0,z1015,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z174,z626]),(0,[z12,z1,z2,z3,z719,z6]),(0,[z0,z1,z2,z1016,z5,z6]),(0,[z0,z1,z2,z3,z15,z288]),(0,[z0,z1,z2,z152,z5,z711])],[(0,[z27,z0,z2,z574,z5,z6]),(0,[z0,z1,z2,z3,z5,z1017]),(0,[z0,z1,z3,z31,z6,z547])],[(0,[z622,z51,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z784,z6]),(0,[z144,z2,z3,z5,z60,z6]),(0,[z0,z1,z2,z3,z5,z1018]),(0,[z0,z1,z127,z128,z15,z6]),(0,[z0,z1,z3,z844,z5,z6]),(0,[z0,z1,z2,z152,z5,z36])],[(0,[z33,z25,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1019,z6]),(0,[z20,z0,z1,z3,z15,z6]),(0,[z0,z1,z2,z526,z97,z6])]],
   [[],[(0,[z569,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1020,z6])],[(0,[z25,z817,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1021,z6]),(0,[z73,z1,z170,z352,z5,z6]),(0,[z0,z1,z2,z3,z1022,z6]),(0,[z0,z2,z3,z304,z15,z6]),(0,[z0,z991,z2,z3,z31,z6]),(0,[z0,z1,z1023,z2,z3,z6])],[(0,[z0,z1,z2,z3,z5,z1024]),(0,[z1025,z0,z1,z2,z3,z6]),(0,[z968,z1,z2,z3,z15,z6]),(1,[z0,z1,z2,z3,z856])],[(0,[z0,z1026,z2,z3,z5,z6]),(0,[z92,z1,z2,z3,z246,z6]),(0,[z263,z0,z2,z3,z15,z26]),(0,[z305,z94,z1,z2,z3,z6]),(0,[z1,z2,z3,z31,z785,z6]),(0,[z1027,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z312,z5,z6]),(0,[z0,z13,z261,z2,z3,z6]),(0,[z0,z1,z2,z3,z31,z266]),(0,[z0,z1,z2,z1028,z3,z6]),(0,[z0,z1,z2,z31,z6,z1029]),(0,[z1,z2,z3,z5,z6,z805]),(0,[z0,z1,z2,z962,z3,z5])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1030,z2,z3,z5,z6]),(0,[z7,z1,z2,z775,z5,z6]),(0,[z27,z70,z2,z3,z5,z6]),(0,[z34,z0,z81,z3,z5,z266]),(0,[z1031,z1,z2,z3,z5,z6]),(0,[z1032,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z841])],[(0,[z0,z1,z2,z3,z1033,z6]),(0,[z92,z1,z2,z3,z158,z6])]],
   [[(0,[z12,z208,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z15,z455]),(0,[z0,z1,z2,z3,z5,z1034]),(0,[z0,z1,z2,z108,z209,z6]),(0,[z0,z1,z2,z5,z742,z6])],[(0,[z1,z2,z3,z54,z101,z6]),(0,[z0,z1,z2,z3,z1035,z6])],[(0,[z0,z1,z2,z3,z1036,z6]),(0,[z0,z1,z2,z1037,z3,z6]),(0,[z1038,z1,z2,z3,z5,z6]),(0,[z0,z338,z2,z3,z5,z56]),(0,[z0,z1,z2,z3,z174,z856])],[(0,[z33,z1,z2,z117,z3,z5]),(0,[z0,z2,z3,z919,z5,z6]),(0,[z94,z816,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1039,z5,z6]),(0,[z0,z1,z2,z3,z5,z1040])],[(0,[z63,z0,z1,z2,z212,z6]),(0,[z0,z1,z2,z3,z1041,z6]),(0,[z0,z1042,z2,z3,z5,z6])],[(0,[z0,z1,z1043,z2,z3,z5]),(0,[z0,z124,z2,z312,z5,z6]),(0,[z0,z166,z2,z3,z5,z551]),(0,[z1,z757,z170,z3,z5,z6]),(0,[z0,z1044,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1045]),(0,[z0,z1,z2,z517,z31,z6]),(0,[z0,z1,z2,z285,z242,z6])],[(0,[z0,z1,z2,z3,z1046,z6]),(0,[z0,z124,z2,z3,z5,z6]),(0,[z0,z1,z2,z1047,z5,z6]),(0,[z0,z1,z2,z3,z6,z1048])]],
   [[(0,[z0,z1,z2,z1049,z5,z6]),(0,[z0,z1,z757,z3,z5,z6]),(0,[z0,z1,z2,z117,z186,z3]),(0,[z0,z806,z2,z3,z5,z6]),(0,[z0,z1,z21,z3,z159,z22])],[(0,[z0,z336,z2,z3,z307,z6]),(0,[z0,z1050,z2,z3,z5,z6]),(0,[z52,z1,z2,z187,z8,z5]),(0,[z7,z59,z2,z53,z5,z6]),(0,[z1,z2,z3,z1051,z5,z6]),(0,[z569,z338,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1052,z6])],[(0,[z421,z51,z2,z3,z5,z6]),(0,[z124,z2,z3,z54,z5,z6]),(0,[z0,z1053,z2,z3,z5,z6]),(0,[z70,z2,z81,z3,z5,z6]),(0,[z1054,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1055,z6]),(0,[z0,z1,z138,z145,z378,z6]),(0,[z268,z0,z2,z3,z31,z6])],[(0,[z0,z1,z1056,z2,z5,z6]),(0,[z92,z1,z2,z207,z5,z6])],[(0,[z0,z1,z3,z31,z600,z6]),(0,[z0,z1,z2,z285,z147,z6])],[(0,[z0,z1,z2,z352,z5,z6]),(0,[z0,z1057,z2,z3,z5,z6]),(0,[z0,z1,z2,z1058,z3,z6]),(0,[z0,z1,z1059,z3,z5,z6]),(0,[z0,z1,z3,z844,z31,z6]),(0,[z0,z1,z2,z44,z3,z213])],[(0,[z33,z25,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z1060,z6]),(0,[z20,z0,z1,z3,z844,z6])],[(0,[z63,z1,z565,z2,z3,z6]),(0,[z0,z1,z2,z3,z1061,z6]),(0,[z0,z9,z14,z3,z135,z6]),(0,[z0,z1,z2,z285,z350,z6]),(0,[z0,z1,z2,z212,z44,z213])]],
   [[(0,[z0,z1,z2,z3,z5,z1062]),(0,[z0,z1,z2,z3,z1063,z6]),(0,[z569,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z1064,z5,z6]),(0,[z94,z1,z2,z3,z6,z477]),(0,[z1,z3,z15,z211,z31,z6]),(0,[z0,z1,z3,z31,z95,z6]),(0,[z0,z1,z533,z3,z15,z6]),(0,[z0,z1,z2,z285,z356,z148])],[(0,[z0,z1,z2,z3,z15,z266])],[(0,[z0,z465,z2,z3,z5,z6]),(0,[z12,z1,z2,z3,z6,z88]),(0,[z143,z1,z2,z3,z5,z60]),(0,[z0,z1,z2,z3,z1065,z6]),(0,[z1066,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1067,z6]),(0,[z0,z322,z2,z3,z353,z6]),(0,[z0,z1068,z2,z3,z5,z6]),(0,[z0,z1,z2,z97,z742,z6]),(0,[z0,z1,z2,z3,z5,z856])],[(0,[z0,z1,z2,z3,z1069,z6]),(0,[z0,z1,z2,z1070,z3,z6]),(0,[z268,z948,z2,z3,z5,z6]),(0,[z0,z1,z2,z43,z5,z440]),(0,[z0,z1,z32,z3,z31,z6])],[(0,[z0,z1,z2,z3,z5,z1071]),(0,[z0,z1,z2,z312,z31,z6]),(0,[z0,z1072,z2,z3,z5,z6]),(0,[z0,z1,z405,z3,z31,z6])],[(0,[z0,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z1073,z6]),(0,[z63,z261,z2,z3,z115,z6]),(0,[z63,z1,z2,z558,z3,z6]),(0,[z92,z1,z2,z239,z5,z6]),(0,[z1074,z1,z2,z3,z5,z6]),(0,[z0,z1,z385,z3,z15,z6])],[(0,[z0,z124,z2,z352,z5,z6]),(0,[z73,z1,z170,z3,z15,z6]),(0,[z0,z1,z2,z3,z1075,z6]),(0,[z34,z0,z81,z3,z5,z6]),(0,[z0,z14,z3,z549,z5,z6]),(0,[z0,z1,z2,z3,z1076,z6])],[(0,[z0,z1,z2,z1077,z5,z6]),(0,[z0,z1,z2,z3,z5,z1078]),(0,[z1079,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1080,z6]),(0,[z0,z1,z2,z44,z129,z213])]],
   [[(0,[z34,z0,z539,z3,z5,z6]),(0,[z0,z1,z2,z3,z1081,z6]),(0,[z0,z1,z2,z3,z1082,z6])],[(0,[z422,z1,z2,z3,z5,z6]),(0,[z63,z18,z2,z3,z115,z6]),(0,[z0,z338,z2,z3,z31,z56]),(0,[z0,z1083,z2,z3,z5,z6])],[(0,[z377,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1084]),(0,[z0,z1,z2,z1085,z5,z6]),(0,[z94,z816,z2,z3,z31,z6]),(0,[z0,z1,z2,z517,z15,z6])],[(0,[z0,z1,z237,z145,z5,z6]),(0,[z0,z1,z2,z285,z613,z6]),(0,[z0,z16,z2,z86,z15,z6]),(0,[z0,z1,z2,z285,z147,z3]),(0,[z0,z1,z2,z147,z97,z5])],[(0,[z0,z1,z2,z1086,z5,z6]),(0,[z0,z1087,z2,z3,z5,z6]),(0,[z176,z0,z1,z3,z15,z6]),(0,[z0,z1,z2,z3,z1088,z6])],[(0,[z1,z2,z3,z5,z6,z1089]),(0,[z0,z1,z2,z3,z15,z1013])],[(0,[z0,z1,z2,z1090,z3,z5]),(0,[z0,z124,z2,z3,z31,z6]),(0,[z0,z1091,z2,z3,z5,z6]),(0,[z140,z0,z571,z2,z3,z6]),(1,[z1,z2,z3,z5,z784]),(0,[z0,z1,z2,z3,z1092,z6]),(0,[z0,z2,z86,z814,z5,z6]),(0,[z268,z0,z2,z3,z15,z6]),(0,[z0,z1,z405,z3,z5,z22])],[(0,[z0,z1,z2,z3,z5,z1093]),(0,[z0,z1,z2,z1094,z5,z6]),(0,[z1095,z1,z2,z3,z5,z6]),(0,[z0,z806,z2,z3,z31,z6]),(0,[z0,z1,z2,z517,z180,z6])]],
   [[(0,[z52,z1,z2,z8,z5,z6]),(0,[z7,z1,z2,z53,z5,z6]),(0,[z0,z1,z2,z3,z5,z1096]),(0,[z63,z208,z1,z2,z3,z6]),(0,[z1,z2,z3,z1051,z31,z6]),(0,[z0,z1,z2,z31,z6,z129])],[(0,[z0,z1,z2,z3,z1097,z6]),(0,[z0,z1,z2,z1098,z3,z6]),(0,[z0,z1,z2,z1099,z3,z6]),(0,[z1054,z1,z2,z3,z31,z6]),(0,[z0,z1,z21,z3,z5,z22])],[(0,[z0,z1,z2,z3,z1100,z6])],[(0,[z0,z1,z1101,z3,z5,z6]),(0,[z0,z1,z3,z5,z1102,z6]),(0,[z0,z2,z3,z1103,z5,z6]),(0,[z0,z1,z1104,z3,z5,z6]),(0,[z1,z2,z3,z54,z719,z6])],[(0,[z50,z817,z2,z3,z5,z6]),(0,[z0,z1,z2,z352,z31,z6]),(0,[z156,z18,z2,z3,z5,z6]),(0,[z277,z1,z2,z3,z211,z6]),(0,[z0,z1,z2,z15,z6,z756])],[(0,[z0,z1,z2,z43,z99,z5]),(0,[z0,z2,z3,z5,z1105,z6])],[(0,[z94,z1,z2,z3,z174,z6]),(0,[z0,z1,z2,z3,z6,z1106]),(0,[z0,z1,z2,z43,z5,z241])],[(0,[z0,z1,z2,z3,z6,z360]),(0,[z0,z1,z2,z814,z5,z6])]],
   [[(0,[z0,z817,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1107,z6]),(0,[z0,z1,z2,z3,z5,z1108]),(0,[z0,z1,z2,z312,z15,z6]),(0,[z0,z1109,z2,z3,z5,z6]),(0,[z1110,z1,z2,z3,z5,z6]),(0,[z0,z1,z192,z3,z5,z68]),(0,[z0,z1111,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z15,z6]),(0,[z52,z1,z2,z775,z5,z6]),(0,[z0,z1,z2,z1112,z3,z6]),(0,[z0,z465,z2,z3,z31,z6]),(0,[z143,z1,z2,z3,z31,z60]),(0,[z0,z1,z2,z3,z5,z1113]),(0,[z0,z1,z2,z3,z1114,z6]),(0,[z0,z1,z2,z3,z1115,z6])],[(0,[z0,z1,z2,z1116,z5,z6])],[(0,[z0,z1,z2,z3,z1117,z6]),(0,[z0,z1118,z2,z3,z5,z6]),(0,[z0,z1119,z2,z3,z5,z6])],[(0,[z466,z1,z2,z3,z5,z6]),(0,[z1074,z1,z2,z3,z31,z6])],[(0,[z0,z1,z2,z358,z187,z3]),(0,[z70,z1,z2,z3,z246,z6]),(0,[z1120,z1,z2,z3,z5,z6]),(0,[z34,z0,z81,z3,z31,z6]),(0,[z0,z338,z2,z3,z15,z56]),(0,[z0,z1,z611,z3,z15,z6])],[(0,[z0,z1,z2,z3,z38,z6]),(0,[z0,z1,z138,z145,z467,z6]),(0,[z1121,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1122,z6]),(0,[z0,z1,z2,z3,z5,z1123])]],
   [[(0,[z50,z336,z51,z2,z3,z6]),(0,[z140,z63,z51,z2,z3,z6]),(0,[z0,z1,z2,z3,z1124,z6]),(0,[z0,z1,z2,z1125,z3,z5]),(0,[z0,z1,z2,z358,z3,z6]),(0,[z70,z1,z2,z3,z158,z6]),(0,[z422,z1,z2,z3,z31,z6]),(0,[z1,z30,z3,z211,z31,z6]),(0,[z0,z1,z2,z285,z147,z148]),(0,[z1126,z1,z2,z3,z5,z6])],[(0,[z0,z1127,z2,z3,z5,z6]),(0,[z0,z2,z3,z1128,z5,z6]),(0,[z0,z1,z2,z3,z1129,z6]),(1,[z0,z1,z2,z285,z147]),(0,[z0,z1,z2,z1130,z3,z6]),(0,[z0,z1,z2,z3,z6,z856])],[(0,[z0,z1,z1131,z3,z5,z6]),(0,[z0,z124,z2,z3,z15,z6]),(0,[z0,z166,z2,z3,z62,z6]),(0,[z92,z1,z2,z3,z5,z455]),(0,[z0,z1,z333,z3,z5,z22]),(0,[z0,z1,z2,z598,z518,z6]),(1,[z0,z1,z2,z212,z44])],[(0,[z0,z1,z2,z3,z5,z1132]),(0,[z0,z1,z2,z3,z1133,z6]),(0,[z1,z2,z3,z54,z17,z6]),(0,[z140,z0,z261,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z724])],[(0,[z1,z2,z3,z211,z17,z6]),(0,[z0,z1,z2,z1134,z5,z6]),(0,[z63,z1,z2,z3,z42,z6]),(0,[z0,z1,z3,z508,z31,z6]),(0,[z0,z1,z2,z43,z5,z515]),(0,[z94,z1,z2,z3,z576,z6]),(0,[z0,z1,z2,z5,z6,z1029])],[(0,[z0,z336,z1,z2,z3,z6]),(0,[z0,z166,z2,z3,z5,z75]),(0,[z73,z1,z170,z3,z62,z6]),(1,[z0,z1,z2,z742,z6])],[(0,[z413,z1,z170,z3,z5,z6]),(0,[z94,z1,z2,z3,z5,z6]),(0,[z0,z1,z1135,z3,z5,z6]),(0,[z1,z2,z3,z15,z211,z6]),(0,[z1095,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z44,z3,z610]),(0,[z0,z1,z2,z43,z242,z5])],[(0,[z63,z1,z2,z3,z109,z6]),(0,[z52,z1,z2,z8,z31,z6]),(0,[z0,z1,z2,z1136,z3,z6]),(0,[z7,z1,z2,z53,z31,z6]),(0,[z0,z1,z2,z3,z5,z1137])]],
   [[(0,[z437,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z352,z15,z6]),(0,[z73,z1,z170,z3,z5,z75]),(0,[z0,z1,z2,z3,z6,z1138]),(0,[z0,z1,z2,z3,z5,z1139]),(0,[z0,z2,z822,z3,z5,z6]),(0,[z140,z0,z2,z3,z171,z6]),(0,[z0,z1,z21,z3,z31,z22])],[(0,[z51,z2,z244,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1140]),(0,[z0,z1,z2,z1141,z3,z6]),(0,[z156,z25,z2,z3,z5,z6]),(0,[z0,z166,z2,z3,z101,z6]),(0,[z0,z2,z3,z5,z26,z811]),(0,[z0,z1,z2,z3,z1142,z6])],[(0,[z0,z1,z2,z1143,z3,z6]),(0,[z0,z1,z2,z3,z1144,z6]),(0,[z268,z1032,z2,z3,z5,z6]),(0,[z0,z1,z2,z43,z122,z5])],[(0,[z501,z1,z2,z8,z5,z6]),(0,[z245,z0,z2,z3,z5,z26]),(0,[z0,z9,z14,z3,z38,z6]),(0,[z1145,z1,z2,z3,z5,z6]),(0,[z0,z1,z686,z3,z31,z6])],[(0,[z635,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1146]),(0,[z0,z1,z2,z3,z1147,z6]),(0,[z178,z25,z2,z3,z5,z6]),(0,[z73,z1,z170,z3,z101,z6]),(0,[z70,z1,z2,z207,z5,z6]),(0,[z151,z1,z2,z3,z394,z6])],[(0,[z0,z1,z2,z1148,z5,z6]),(0,[z0,z465,z2,z3,z15,z6]),(0,[z143,z1,z2,z3,z15,z60]),(0,[z0,z1,z2,z3,z5,z1149]),(0,[z0,z1,z2,z1150,z5,z6]),(0,[z0,z1,z2,z1151,z5,z6]),(0,[z0,z1,z2,z43,z31,z241])],[(0,[z0,z1152,z2,z3,z5,z6]),(0,[z89,z1,z74,z3,z17,z6]),(0,[z0,z1,z2,z1153,z5,z6]),(1,[z0,z1,z746,z5,z6]),(0,[z0,z1,z2,z1154,z3,z6]),(0,[z0,z1,z2,z840,z3,z31]),(0,[z0,z1,z2,z152,z5,z441])],[(0,[z0,z1,z2,z1155,z3,z5]),(0,[z12,z1,z2,z3,z211,z6]),(0,[z0,z1,z2,z1156,z5,z6])]],
   [[(0,[z0,z1,z2,z1157,z5,z6]),(0,[z721,z422,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z844,z6])],[(0,[z34,z0,z81,z3,z15,z6]),(0,[z0,z1,z539,z3,z31,z6]),(0,[z1158,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1159,z6]),(0,[z268,z0,z2,z86,z5,z6]),(0,[z0,z1,z420,z3,z31,z6])],[(0,[z0,z1160,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1161,z6]),(0,[z143,z1,z2,z3,z168,z60]),(0,[z92,z1,z2,z3,z5,z266]),(0,[z466,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z3,z1162,z6]),(0,[z0,z2,z3,z5,z954,z6])],[(0,[z0,z1,z2,z3,z1163,z6]),(0,[z0,z1,z2,z1164,z3,z5]),(0,[z422,z1,z2,z3,z15,z6]),(0,[z0,z13,z2,z3,z919,z6]),(0,[z0,z1,z3,z15,z31,z6]),(0,[z0,z1,z2,z5,z6,z711])],[(0,[z0,z1,z2,z3,z1165,z6]),(0,[z0,z1,z2,z3,z6,z1166]),(0,[z0,z1,z2,z3,z135,z6])],[(0,[z70,z1,z2,z239,z5,z6]),(0,[z94,z322,z1,z2,z3,z6])],[(0,[z698,z51,z2,z3,z5,z6]),(0,[z0,z1,z2,z117,z358,z3]),(0,[z0,z1,z2,z3,z5,z1167]),(0,[z0,z13,z2,z3,z307,z6]),(0,[z0,z1,z146,z108,z5,z68])]],
   [[(0,[z0,z1,z2,z3,z62,z6]),(0,[z0,z1,z1168,z3,z5,z6]),(0,[z0,z1,z2,z3,z1169,z6]),(0,[z94,z1,z2,z478,z3,z6]),(0,[z0,z1,z2,z43,z122,z241]),(0,[z0,z1,z2,z212,z49,z6])],[(0,[z70,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1170,z6]),(0,[z0,z1,z2,z3,z5,z1171]),(0,[z52,z1,z2,z358,z8,z6]),(0,[z0,z1,z11,z3,z31,z6]),(0,[z0,z1,z2,z128,z5,z195])],[(0,[z0,z1,z2,z3,z5,z1172]),(0,[z0,z1,z2,z746,z5,z6]),(0,[z0,z1,z2,z285,z488,z6])],[(0,[z0,z1,z2,z3,z5,z75]),(0,[z52,z1,z2,z8,z15,z6]),(0,[z7,z1,z2,z53,z15,z6]),(0,[z572,z1,z2,z3,z5,z60]),(0,[z0,z1,z2,z3,z1173,z6]),(0,[z0,z1,z2,z1174,z3,z6])],[(0,[z0,z1,z2,z3,z1175,z6]),(0,[z140,z0,z2,z3,z442,z6]),(0,[z73,z1,z170,z3,z5,z551]),(0,[z0,z1,z2,z1176,z3,z6]),(0,[z143,z1,z2,z489,z3,z5]),(0,[z1177,z1,z2,z3,z5,z6]),(0,[z0,z1,z21,z3,z15,z22])],[(0,[z0,z1,z2,z1178,z3,z6]),(0,[z33,z1,z2,z3,z168,z6]),(0,[z0,z1,z2,z3,z1179,z6]),(0,[z0,z1,z2,z1180,z5,z6]),(0,[z94,z1,z2,z3,z31,z6]),(0,[z0,z1,z2,z212,z44,z3])],[(0,[z94,z1,z2,z285,z3,z6])],[(0,[z0,z1,z2,z3,z101,z6]),(0,[z0,z1,z2,z3,z5,z789]),(0,[z0,z1,z2,z207,z246,z6]),(0,[z0,z2,z3,z31,z6,z813])]],
   [[(0,[z245,z1,z2,z3,z5,z60]),(0,[z33,z680,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1181,z6]),(0,[z0,z1,z2,z3,z1182,z6]),(0,[z0,z1,z2,z3,z6,z1183]),(0,[z0,z1,z2,z3,z378,z6]),(0,[z0,z1,z2,z108,z5,z6])],[(0,[z0,z124,z2,z3,z62,z6]),(0,[z0,z1,z2,z43,z15,z241]),(0,[z0,z1,z2,z108,z5,z68])],[(0,[z0,z1,z665,z3,z5,z68]),(0,[z0,z1,z2,z207,z158,z6]),(0,[z1184,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1185,z6]),(0,[z200,z1,z2,z3,z42,z6])],[(0,[z51,z2,z3,z5,z310,z6]),(0,[z0,z1,z2,z3,z1186,z6]),(0,[z63,z1,z2,z3,z115,z6])],[(0,[z0,z1,z2,z1187,z5,z6]),(0,[z0,z149,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1188,z6]),(0,[z0,z1189,z2,z3,z5,z6]),(0,[z1190,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z96,z139,z6]),(0,[z0,z1,z2,z15,z6,z129])],[(0,[z1,z817,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1191,z6]),(0,[z0,z1,z2,z3,z5,z1192]),(0,[z0,z1,z2,z3,z1193,z6]),(0,[z94,z1,z2,z3,z619,z6]),(0,[z0,z1,z2,z122,z3,z6])],[(0,[z0,z1,z2,z352,z62,z6]),(0,[z466,z1,z2,z3,z15,z6]),(0,[z0,z2,z3,z141,z919,z6]),(0,[z869,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z145,z5,z195]),(0,[z0,z1,z2,z147,z3,z15])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 533).take 525) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1058).take 172) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1230)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [533, 525, 172] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 109).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 221).take 35).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [109, 112, 35] = true :=
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

end PEqualNP.Outside.L_meta_38921

theorem PEqualNP.Outside.L_meta_38921 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4242596064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4242596064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38921.solve
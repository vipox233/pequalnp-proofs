import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38801

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4274055360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0002a08ac43c1bc0#64 ++ 0x40002a08ac43c1bc#64 ++ 0xb027e79fc47c3fcf#64 ++ 0xab027e79fc47c3fc#64 : BitVec 256),
   (0x00c98a2605854554#64 ++ 0x800c98a260585455#64 ++ 0xd1d99a66078fc7ff#64 ++ 0x7d1d99a66078fc7f#64 : BitVec 256),
   (0x16161458580aa8a9#64 ++ 0x016161458580aa8a#64 ++ 0xfe1e1c78780ff8fe#64 ++ 0xffe1e1c78780ff8f#64 : BitVec 256),
   (0x2b601f802ad0f60e#64 ++ 0x02b601f802ad0f60#64 ++ 0x7fe01f807ff0ff0d#64 ++ 0xf7fe01f807ff0ff0#64 : BitVec 256),
   (0x4dbfe000776f0000#64 ++ 0x04dbfe000776f000#64 ++ 0x6fffe0007fff000b#64 ++ 0xe6fffe0007fff000#64 : BitVec 256),
   (0x8ffd5f7500000000#64 ++ 0x08ffd5f750000000#64 ++ 0x8fffffff80000007#64 ++ 0xf8fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0002000840080880 0x0000200084008088 0x80060018000c00c2 0x080060018000c00c

def z1 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xb027e79fc47c3fcf 0xab027e79fc47c3fc

def z2 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1d99a66078fc7ff 0x7d1d99a66078fc7f

def z3 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe1e1c78780ff8fe 0xffe1e1c78780ff8f

def z4 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fe01f807ff0ff0d 0xf7fe01f807ff0ff0

def z5 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fffe0007fff000b 0xe6fffe0007fff000

def z6 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8fffffff80000007 0xf8fffffff8000000

def z7 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x30000000447c3fc8 0x030000000447c3fc

def z8 : W := mkw 0x2b601f002ac0e40e 0x02b601f002ac0e40 0x4fe01f803b80c005 0xf4fe01f803b80c00

def z9 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0181860000fc0fe 0x7d0181860000fc0f

def z10 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0x2e06041878003800 0x82e0604187800380

def z11 : W := mkw 0x0614145000000000 0x0061414500000000 0x8e1e1c7800000006 0xf8e1e1c780000000

def z12 : W := mkw 0x10020008580aa8a9 0x010020008580aa8a 0x70000000780ff8f8 0x070000000780ff8f

def z13 : W := mkw 0x2f741fd02ad0f60e 0x02f741fd02ad0f60 0xfffe1ff87ff0ff0f 0xffffe1ff87ff0ff0

def z14 : W := mkw 0x4dffeaaef7ff5fd4 0xc4dffeaaef7ff5fd 0xffffffffffffffff 0xffffffffffffffff

def z15 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1ffffff878fc7ff 0xfd1ffffff878fc7f

def z16 : W := mkw 0x1616b4dadc3ebbe9 0x41616b4dadc3ebbe 0xfe1e1c787c7ffffe 0xffe1e1c787c7ffff

def z17 : W := mkw 0x2b62bf8aeefcffce 0x42b62bf8aeefcffc 0x7fe01f807ffcffcd 0xf7fe01f807ffcffc

def z18 : W := mkw 0x849d407500000000 0x0849d40750000000 0x801fe07f80000002 0x0801fe07f8000000

def z19 : W := mkw 0xcdbfe075776f0000 0x0cdbfe075776f000 0xefffe07fffff000b 0xeefffe07fffff000

def z20 : W := mkw 0x82401f7500000000 0x082401f750000000 0x8027ffff80000007 0xb8027ffff8000000

def z21 : W := mkw 0x2920018022501202 0x0292001802250120 0x0020018000700000 0x0002001800070000

def z22 : W := mkw 0x4dfd4a2433c34414 0x84dfd4a2433c3441 0x4fd818603b83c030 0x54fd818603b83c03

def z23 : W := mkw 0x2b601f802a50b20a 0x02b601f802a50b20 0x2fe01f8078703805 0xf2fe01f807870380

def z24 : W := mkw 0x0002a000442c0000 0x00002a000442c000 0x2027e000447c000b 0xa2027e000447c000

def z25 : W := mkw 0x6fbff5807f7fb20a 0x06fbff5807f7fb20 0x6fffe5807fff380b 0xe6fffe5807fff380

def z26 : W := mkw 0x00022008c0280880 0x400022008c028088 0x0006601980000000 0x0000660198000000

def z27 : W := mkw 0xafffffffeefcffce 0x4afffffffeefcffc 0xfffffffffffcffcf 0xffffffffffffcffc

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0x8027e79f80000007 0xa8027e79f8000000

def z29 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x10001f800000ff04 0x110001f800000ff0

def z30 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x2fe7e0007ff00001 0x82fe7e0007ff0000

def z31 : W := mkw 0x0000000000000000 0x0000000000000000 0x6e00000078000008 0xe6e0000007800000

def z32 : W := mkw 0x0920000022400000 0x0092000002240000 0x6fe000007ff00009 0xe6fe000007ff0000

def z33 : W := mkw 0x8ffd5f7522400000 0x08ffd5f752240000 0xeffffffffff0000f 0xfeffffffffff0000

def z34 : W := mkw 0x220015800810b20a 0x0220015800810b20 0x0000058000003800 0x0000005800000380

def z35 : W := mkw 0x0000008a80101bc0 0x40000008a80101bc 0x9000079f80003fc4 0x09000079f80003fc

def z36 : W := mkw 0x0089800005050000 0x0008980000505000 0x41d98000078f000b 0x641d98000078f000

def z37 : W := mkw 0x2b2015802a50b20a 0x02b2015802a50b20 0x2e20058078703800 0x82e2005807870380

def z38 : W := mkw 0x3f761fd87adafeaf 0x03f761fd87adafea 0xfffe1ff87fffffff 0xffffe1ff87ffffff

def z39 : W := mkw 0x89ebebafc43c1bc0 0x489ebebafc43c1bc 0xb1e7e79fc47c3fcf 0xab1e7e79fc47c3fc

def z40 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x4fe01b803ff0c701 0x54fe01b803ff0c70

def z41 : W := mkw 0x00400a2600804554 0x800400a260080455 0x90001a660000c7f4 0x190001a660000c7f

def z42 : W := mkw 0x8ffd5f7501814414 0x88ffd5f750181441 0xcfffffff8383c037 0xfcfffffff8383c03

def z43 : W := mkw 0x0000008000101200 0x0000000800010120 0x1000078000003f04 0x01000078000003f0

def z44 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001820600000007 0x2800182060000000

def z45 : W := mkw 0x949f407d500a08a1 0x0949f407d500a08a 0x801fe07f800f00f2 0x0801fe07f800f00f

def z46 : W := mkw 0x6f3675807a7ab20a 0x06f3675807a7ab20 0x2e26658078703800 0x82e2665807870380

def z47 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xb007e01fc47c3fca 0x0b007e01fc47c3fc

def z48 : W := mkw 0x1002a08adc3ebbe9 0x41002a08adc3ebbe 0x700000007c7ffff8 0x0700000007c7ffff

def z49 : W := mkw 0x2002a08aeefcffce 0x42002a08aeefcffc 0x700000007ffcffc8 0x0700000007ffcffc

def z50 : W := mkw 0x6fffff007fefe40e 0x06fffff007fefe40 0x6ffff8007fffc00b 0xf6ffff8007fffc00

def z51 : W := mkw 0x4dbfe08af77f1bc0 0x44dbfe08af77f1bc 0xffffe79fffff3fcf 0xeffffe79fffff3fc

def z52 : W := mkw 0x4dffea2677ef4554 0x84dffea2677ef455 0xfffffa667fffc7ff 0xffffffa667fffc7f

def z53 : W := mkw 0x4dbd400033430000 0x04dbd40003343000 0x4fffe0003b830003 0xe4fffe0003b83000

def z54 : W := mkw 0x16df9e7e5d8fedfd 0x816df9e7e5d8fedf 0xffdf9e7e7f8fffff 0xfffdf9e7e7f8ffff

def z55 : W := mkw 0x00c90a2400000000 0x000c90a240000000 0x81d99a6600000007 0x781d99a660000000

def z56 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x0fe01f8000000005 0xf0fe01f800000000

def z57 : W := mkw 0xaffd5ff52ad0f60e 0x0affd5ff52ad0f60 0xfffffffffff0ff0f 0xffffffffffff0ff0

def z58 : W := mkw 0x292000802ad0f60e 0x0292000802ad0f60 0x7fe000007ff0ff09 0xe7fe000007ff0ff0

def z59 : W := mkw 0x00c90a2400000000 0x000c90a240000000 0x81ffffff80000007 0xf81ffffff8000000

def z60 : W := mkw 0x2b601f002ac0e40e 0x02b601f002ac0e40 0x4fc018003b80c000 0x54fc018003b80c00

def z61 : W := mkw 0x849d407500000000 0x0849d40750000000 0x803fe7ff80000007 0xa803fe7ff8000000

def z62 : W := mkw 0x6fffff807ffff60e 0x06fffff807ffff60 0x7fffff807fffff0f 0xf7fffff807fffff0

def z63 : W := mkw 0x4dbfe002776f0140 0x04dbfe002776f014 0xffffe2067fff07cf 0xeffffe2067fff07c

def z64 : W := mkw 0x161414501802a029 0x0161414501802a02 0x7e181c607803f83c 0xf7e181c607803f83

def z65 : W := mkw 0x00022088c0381a80 0x400022088c0381a8 0x2000000040703800 0x0200000004070380

def z66 : W := mkw 0x0000002600000150 0x8000000260000015 0x80000066000000f0 0x080000066000000f

def z67 : W := mkw 0x14160058500a08a1 0x014160058500a08a 0x801e0078000f00f2 0x0801e0078000f00f

def z68 : W := mkw 0x49a9e00027650000 0x049a9e0002765000 0x6fe1e0007ff00009 0xe6fe1e0007ff0000

def z69 : W := mkw 0x2000008022d05606 0x02000008022d0560 0x0000000007f00700 0x00000000007f0070

def z70 : W := mkw 0x3b621f887adafeaf 0x03b621f887adafea 0x7fe01f807ffffffd 0xf7fe01f807ffffff

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x41c0000007800009 0x641c000000780000

def z72 : W := mkw 0x0000800204040140 0x0000080020404014 0x90018206040c07cf 0x290018206040c07c

def z73 : W := mkw 0x22401f8a8890ffce 0x422401f8a8890ffc 0x90001f9f8000ffc4 0x190001f9f8000ffc

def z74 : W := mkw 0x00400a0000804404 0x000400a000080440 0x10001a000000c704 0x110001a000000c70

def z75 : W := mkw 0x120014580800a8a9 0x0120014580800a8a 0x90001c780000f8f4 0x190001c780000f8f

def z76 : W := mkw 0x5fbff4587f6fa8a9 0x05fbff4587f6fa8a 0xfffffc787ffff8ff 0xffffffc787ffff8f

def z77 : W := mkw 0x2b223588ea78ba8a 0x42b223588ea78ba8 0x2e266599f8703800 0x82e266599f870380

def z78 : W := mkw 0x49a9e00027650000 0x049a9e0002765000 0x01e1e00007f00001 0x001e1e00007f0000

def z79 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x51d81860078fc7f8 0x551d81860078fc7f

def z80 : W := mkw 0x00c90a2401814414 0x800c90a240181441 0x41d818600383c030 0x541d818600383c03

def z81 : W := mkw 0x0089000000000000 0x0008900000000000 0x01d9800000000003 0x601d980000000000

def z82 : W := mkw 0xcfbff551776f0000 0x0cfbff551776f000 0x6fffe599ffff000b 0xe6fffe599ffff000

def z83 : W := mkw 0x0920000000000000 0x0092000000000000 0x0fe0000000000001 0xe0fe000000000000

def z84 : W := mkw 0x02401f0000000000 0x002401f000000000 0x00001f8000000004 0x100001f800000000

def z85 : W := mkw 0x0002a00ac42c09c0 0x40002a00ac42c09c 0x8007e01f800c00c2 0x08007e01f800c00c

def z86 : W := mkw 0x0089802605050150 0x8008980260505015 0x0001800600000000 0x0000180060000000

def z87 : W := mkw 0x29e98ba627d55756 0x829e98ba627d5575 0xd1f99be607ffc7ff 0x7d1f99be607ffc7f

def z88 : W := mkw 0x449fe000552f0000 0x0449fe000552f000 0x6e1fe000780f000a 0xe6e1fe000780f000

def z89 : W := mkw 0x2f761f807adaf60e 0x02f761f807adaf60 0x7ffe1f807fffff0f 0xf7ffe1f807fffff0

def z90 : W := mkw 0x0000a08284341340 0x40000a0828434134 0x0021e38784700701 0x00021e3878470070

def z91 : W := mkw 0x00cbaa2ec5ad4dd4 0xc00cbaa2ec5ad4dd 0xd1dffa7f878fc7ff 0x7d1dffa7f878fc7f

def z92 : W := mkw 0x200080822fd5f75e 0x8200080822fd5f75 0x700000007ffffff8 0x0700000007ffffff

def z93 : W := mkw 0x161414580800a8a9 0x0161414580800a8a 0x9e1e1c780000f8f6 0xf9e1e1c780000f8f

def z94 : W := mkw 0x4002a000776f0000 0x04002a000776f000 0x600000007fff0008 0x0600000007fff000

def z95 : W := mkw 0x82401f7500000000 0x082401f750000000 0x80001fff80000004 0x180001fff8000000

def z96 : W := mkw 0x00c90a2400000000 0x000c90a240000000 0x01d8186000000000 0x501d818600000000

def z97 : W := mkw 0x1616b4dadc3ebbe9 0x41616b4dadc3ebbe 0xfe3ffffffc7fffff 0xffe3ffffffc7ffff

def z98 : W := mkw 0x2b601f002ac0e40e 0x02b601f002ac0e40 0x7fc01c007b80f80c 0xf7fc01c007b80f80

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0x8007e01f80000002 0x08007e01f8000000

def z100 : W := mkw 0x0089802605050150 0x8008980260505015 0x90198266040f07ff 0x290198266040f07f

def z101 : W := mkw 0x02c99e260d85e55c 0x802c99e260d85e55 0xffd99e667f8fffff 0xfffd99e667f8ffff

def z102 : W := mkw 0x8dfd4b7500000000 0x08dfd4b750000000 0x81ffe3ff80000003 0x081ffe3ff8000000

def z103 : W := mkw 0x020014000800a008 0x0020014000800a00 0x7e001c007800f80c 0xf7e001c007800f80

def z104 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x9007e79f800c3fc6 0x09007e79f800c3fc

def z105 : W := mkw 0x96561f7d580aa8a9 0x096561f7d580aa8a 0xfe1e1ffff80ff8fe 0xffe1e1ffff80ff8f

def z106 : W := mkw 0x00cbaaaec5bd5fd4 0xc00cbaaaec5bd5fd 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z107 : W := mkw 0x449fe00ad52f09c0 0x4449fe00ad52f09c 0x801fe01f800f00c2 0x0801fe01f800f00c

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x900018600000c0f4 0x1900018600000c0f

def z109 : W := mkw 0x2be99fa62fd5f75e 0x82be99fa62fd5f75 0xfff99fe67fffffff 0xffff99fe67ffffff

def z110 : W := mkw 0x40cbaa2677ef4554 0x840cbaa2677ef455 0xf1d99a667fffc7ff 0x7f1d99a667fffc7f

def z111 : W := mkw 0x8f34555100000000 0x08f3455510000000 0x0e26659980000000 0x80e2665998000000

def z112 : W := mkw 0x00400a0000804404 0x000400a000080440 0x51c01a000780c70d 0x751c01a000780c70

def z113 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x3e201f807870ff04 0x93e201f807870ff0

def z114 : W := mkw 0x2bebbfaeeffdffde 0xc2bebbfaeeffdffd 0xffffffffffffffff 0xffffffffffffffff

def z115 : W := mkw 0x00400aae80905fd4 0xc00400aae80905fd 0x90001fff8000fff4 0x190001fff8000fff

def z116 : W := mkw 0x161414501802a029 0x0161414501802a02 0x4e1818603803c030 0x54e1818603803c03

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0x2020000044700009 0xa202000004470000

def z118 : W := mkw 0x2b62bf8aeefcffce 0x42b62bf8aeefcffc 0xffe7ff9ffffcffcf 0xfffe7ff9ffffcffc

def z119 : W := mkw 0x29600b8022d05606 0x029600b8022d0560 0x01e0038007f00701 0x001e0038007f0070

def z120 : W := mkw 0x89e94b2500000000 0x089e94b250000000 0x01e1e38780000001 0x001e1e3878000000

def z121 : W := mkw 0x89e9eba784341340 0x489e9eba78434134 0x01e1e38784700701 0x001e1e3878470070

def z122 : W := mkw 0x29e98ba627d55756 0x829e98ba627d5575 0x01e1838607f00701 0x001e1838607f0070

def z123 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x3027e000447c3fcb 0xa3027e000447c3fc

def z124 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0x6e1e0418780f380a 0xe6e1e0418780f380

def z125 : W := mkw 0x0dbd400000000000 0x00dbd40000000000 0x0fffe00000000003 0xe0fffe0000000000

def z126 : W := mkw 0x020014000800a008 0x0020014000800a00 0x2e00040078003800 0x82e0004007800380

def z127 : W := mkw 0x0be91f2400000000 0x00be91f240000000 0x8ff99fe600000007 0xf8ff99fe60000000

def z128 : W := mkw 0x0089802605050150 0x8008980260505015 0x80198066000f00f2 0x080198066000f00f

def z129 : W := mkw 0xcf367551726a0000 0x0cf367551726a000 0x2e266599f8700000 0x82e266599f870000

def z130 : W := mkw 0x0002200040280000 0x0000220004028000 0x2026600040700000 0x8202660004070000

def z131 : W := mkw 0x4002a08af77f1bc0 0x44002a08af77f1bc 0x700000007fff3fc8 0x0700000007fff3fc

def z132 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0xefffe79fffff000f 0xeefffe79fffff000

def z133 : W := mkw 0x849fe07fc42c09c0 0x4849fe07fc42c09c 0x801fe07f800c00c2 0x0801fe07f800c00c

def z134 : W := mkw 0x0f741f5000000000 0x00f741f500000000 0x8ffe1ff800000007 0xf8ffe1ff80000000

def z135 : W := mkw 0xcfffff75776f0000 0x0cfffff75776f000 0xefffffffffff000f 0xfefffffffffff000

def z136 : W := mkw 0x00c90a2600804554 0x800c90a260080455 0x91d99a660000c7f7 0x791d99a660000c7f

def z137 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xc1d99866038fc0f2 0x5c1d99866038fc0f

def z138 : W := mkw 0x0000008000101200 0x0000000800010120 0x3020078044703f0d 0xa3020078044703f0

def z139 : W := mkw 0x00022088c0381a80 0x400022088c0381a8 0x20266599c0703800 0x820266599c070380

def z140 : W := mkw 0x0000800205854554 0x8000080020585455 0xd0018206078fc7ff 0x2d0018206078fc7f

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0x0027e00000000003 0xa0027e0000000000

def z142 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x01c1820607800701 0x001c182060780070

def z143 : W := mkw 0x0002a08ac5bd5fd4 0xc0002a08ac5bd5fd 0xf027e79fc7ffffff 0xaf027e79fc7fffff

def z144 : W := mkw 0x00c90a2400000000 0x000c90a240000000 0xd1d99a66000fc0ff 0x7d1d99a66000fc0f

def z145 : W := mkw 0x0000000a800009c0 0x40000000a800009c 0x8000001f800000c0 0x08000001f800000c

def z146 : W := mkw 0x8fffffffc43c1bc0 0x48fffffffc43c1bc 0xbfffffffc47c3fcf 0xfbfffffffc47c3fc

def z147 : W := mkw 0x8ffddf7705854554 0x88ffddf770585455 0xdfffffff878fc7ff 0xfdfffffff878fc7f

def z148 : W := mkw 0x9fff5f7d580aa8a9 0x09fff5f7d580aa8a 0xfffffffff80ff8ff 0xffffffffff80ff8f

def z149 : W := mkw 0x0614145000000000 0x0061414500000000 0x8e3fffff80000007 0xf8e3fffff8000000

def z150 : W := mkw 0x0000808a84141bc0 0x40000808a84141bc 0x9001879f840c3fcf 0x29001879f840c3fc

def z151 : W := mkw 0x4002a08af77f1bc0 0x44002a08af77f1bc 0xf027e79fffff3fcf 0xaf027e79fffff3fc

def z152 : W := mkw 0x22401fa60890f75e 0x822401fa60890f75 0x90001fe60000fff4 0x190001fe60000fff

def z153 : W := mkw 0x200000802ad0f60e 0x0200000802ad0f60 0x700000007ff0ff08 0x0700000007ff0ff0

def z154 : W := mkw 0x0002000040080000 0x0000200004008000 0x20060000400c000a 0xa20060000400c000

def z155 : W := mkw 0x4dbd400033430000 0x04dbd40003343000 0x4fd800003b830000 0x44fd800003b83000

def z156 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe3ffffff80ff8ff 0xffe3ffffff80ff8f

def z157 : W := mkw 0x1002800a5d8fedfd 0x81002800a5d8fedf 0x700000007f8ffff8 0x0700000007f8ffff

def z158 : W := mkw 0x0002a00ac42c09c0 0x40002a00ac42c09c 0x9007e21f840c07cf 0x29007e21f840c07c

def z159 : W := mkw 0x0002208ac0381bc0 0x40002208ac0381bc 0xb026679fc0703fc4 0x8b026679fc0703fc

def z160 : W := mkw 0x449fe026552f0150 0x8449fe026552f015 0x801fe066000f00f2 0x0801fe066000f00f

def z161 : W := mkw 0x0dfd4a2400000000 0x00dfd4a240000000 0x8ffffa6600000007 0xf8ffffa660000000

def z162 : W := mkw 0x2b623f88eaf8fe8e 0x42b623f88eaf8fe8 0x7fe67f99fff0ff0d 0xf7fe67f99fff0ff0

def z163 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fd800007fff0008 0x46fd800007fff000

def z164 : W := mkw 0x04df8a26558f4554 0x804df8a26558f455 0xffdf9a667f8fc7ff 0xfffdf9a667f8fc7f

def z165 : W := mkw 0x0d360000724a0000 0x00d360000724a000 0x6ffe00007fff000b 0xe6ffe00007fff000

def z166 : W := mkw 0x00408a2605854554 0x800408a260585455 0xd0001a66078fc7fc 0x1d0001a66078fc7f

def z167 : W := mkw 0x0000000000000000 0x0000000000000000 0x300004004000380c 0xa300004004000380

def z168 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0x7e181860780ff8f8 0x57e181860780ff8f

def z169 : W := mkw 0x9f365559580aa8a9 0x09f365559580aa8a 0xfe3e7df9f80ff8fe 0xffe3e7df9f80ff8f

def z170 : W := mkw 0x6fffff8affffffce 0x46fffff8affffffc 0xffffff9fffffffcf 0xfffffff9fffffffc

def z171 : W := mkw 0x120014580800a8a9 0x0120014580800a8a 0xd0181c78000ff8fe 0x7d0181c78000ff8f

def z172 : W := mkw 0x0089802605050150 0x8008980260505015 0xc1d98066078f00fb 0x6c1d98066078f00f

def z173 : W := mkw 0x4dbfe080777f1200 0x04dbfe080777f120 0x7fffe7807fff3f0f 0xe7fffe7807fff3f0

def z174 : W := mkw 0x161414581802a8a9 0x0161414581802a8a 0xde181c783803f8f4 0x5de181c783803f8f

def z175 : W := mkw 0x6ffd5f003bc3e40e 0x06ffd5f003bc3e40 0x4fd818003b83c000 0x54fd818003b83c00

def z176 : W := mkw 0x1002a08adc3ebbe9 0x41002a08adc3ebbe 0xf027e79ffc7fffff 0xaf027e79ffc7ffff

def z177 : W := mkw 0x40022000726a0000 0x040022000726a000 0x2000000078700000 0x0200000007870000

def z178 : W := mkw 0x061414500800a008 0x0061414500800a00 0xfe1e1c787800f80e 0xffe1e1c787800f80

def z179 : W := mkw 0xc9e9eb2527650000 0x0c9e9eb252765000 0x01e1e38787f00001 0x001e1e38787f0000

def z180 : W := mkw 0x8f34555100000000 0x08f3455510000000 0x8e27e79f80000007 0xa8e27e79f8000000

def z181 : W := mkw 0x16161450580aa029 0x016161450580aa02 0x6e1e1860780fc03a 0xf6e1e1860780fc03

def z182 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0xdfffffff800fc0ff 0xfdfffffff800fc0f

def z183 : W := mkw 0x04160000500a0000 0x004160000500a000 0x6e1e0000780f000a 0xe6e1e0000780f000

def z184 : W := mkw 0x2b601f002ac0e40e 0x02b601f002ac0e40 0x5fc01a003f80c70d 0x75fc01a003f80c70

def z185 : W := mkw 0x4dbfe00af76f09c0 0x44dbfe00af76f09c 0xefffe01fffff00cb 0xeefffe01fffff00c

def z186 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x2e3fe000787f0002 0x82e3fe000787f000

def z187 : W := mkw 0x4dffea0077ef4404 0x04dffea0077ef440 0x7ffffa007fffc70f 0xf7ffffa007fffc70

def z188 : W := mkw 0x89e94b2500000000 0x089e94b250000000 0x81e7e79f80000007 0xa81e7e79f8000000

def z189 : W := mkw 0xaffd5f752ac0e40e 0x0affd5f752ac0e40 0xcfffffffbb80c007 0xfcfffffffbb80c00

def z190 : W := mkw 0x00c90a2401814414 0x800c90a240181441 0xc1d99a660383c037 0x7c1d99a660383c03

def z191 : W := mkw 0x0000800205854554 0x8000080020585455 0x50000000078fc7f8 0x050000000078fc7f

def z192 : W := mkw 0x22c99fa60d95f75e 0x822c99fa60d95f75 0xd1d99fe6078fffff 0x7d1d99fe6078ffff

def z193 : W := mkw 0x4922a000776f0000 0x04922a000776f000 0x6fe000007fff0009 0xe6fe000007fff000

def z194 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000000000fc0f8 0x050000000000fc0f

def z195 : W := mkw 0xaffd5ff50890f60e 0x0affd5ff50890f60 0x9fffffff8000ff07 0xf9fffffff8000ff0

def z196 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x6fe01d807bf0f800 0xd6fe01d807bf0f80

def z197 : W := mkw 0x00c90a2401814414 0x800c90a240181441 0xd1d81860038fc0fe 0x7d1d81860038fc0f

def z198 : W := mkw 0x2b601f002ac0e40e 0x02b601f002ac0e40 0x6fe018007ff0c009 0xf6fe018007ff0c00

def z199 : W := mkw 0x4d36e000766e0000 0x04d36e000766e000 0x2e27e0007c7c000b 0xa2e27e0007c7c000

def z200 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x0fd8186000000000 0x50fd818600000000

def z201 : W := mkw 0x8fbd557500000000 0x08fbd55750000000 0x8e3fe5ff80000002 0x88e3fe5ff8000000

def z202 : W := mkw 0x0fbd545000000000 0x00fbd54500000000 0x8ffffc7800000007 0xf8ffffc780000000

def z203 : W := mkw 0x449fe000552f0000 0x0449fe000552f000 0x001fe000000f0002 0x0001fe000000f000

def z204 : W := mkw 0x0002000840080880 0x0000200084008088 0xb0060418400c38ce 0xab0060418400c38c

def z205 : W := mkw 0x4dbde00037670000 0x04dbde0003767000 0x4ff9e0003ff30001 0x44ff9e0003ff3000

def z206 : W := mkw 0x0000808204141340 0x0000080820414134 0xb0218786447c3fcf 0xab0218786447c3fc

def z207 : W := mkw 0x2ffd5f802ad0f60e 0x02ffd5f802ad0f60 0x7fffff807ff0ff0f 0xf7fffff807ff0ff0

def z208 : W := mkw 0x0002a082c43c1340 0x40002a082c43c134 0x2027e387c47c070b 0xa2027e387c47c070

def z209 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x0fc0180000000000 0x50fc018000000000

def z210 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8fd81fff80000004 0x58fd81fff8000000

def z211 : W := mkw 0x0002a002442c0140 0x00002a002442c014 0xb027e206447c07cf 0xab027e206447c07c

def z212 : W := mkw 0x16df1e7c580aa8a9 0x016df1e7c580aa8a 0xffdf9e7e780ff8ff 0xfffdf9e7e780ff8f

def z213 : W := mkw 0x4dffea2677ef4554 0x84dffea2677ef455 0x6fffe2067fff070b 0xe6fffe2067fff070

def z214 : W := mkw 0x020014000800a008 0x0020014000800a00 0xfe181c60780ff8fe 0xffe181c60780ff8f

def z215 : W := mkw 0x0089802605854554 0x8008980260585455 0xd0198066078fc7fa 0x0d0198066078fc7f

def z216 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x0fe7e79f80000001 0x80fe7e79f8000000

def z217 : W := mkw 0x2be91f242bc1e41e 0x82be91f242bc1e41 0x4fd818603b83c030 0x54fd818603b83c03

def z218 : W := mkw 0x14160058500a08a1 0x014160058500a08a 0xd01e1878000fc0fe 0x7d01e1878000fc0f

def z219 : W := mkw 0x3f3615d87a5abaab 0x03f3615d87a5abaa 0x2e26059878703800 0x82e2605987870380

def z220 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x41d99a660783c731 0x541d99a660783c73

def z221 : W := mkw 0x00400a2600804554 0x800400a260080455 0x0000020600000700 0x0000002060000070

def z222 : W := mkw 0x82c91f7500000000 0x082c91f750000000 0x81d99fff80000007 0x781d99fff8000000

def z223 : W := mkw 0x4d366000726a0000 0x04d366000726a000 0x2e26600078700000 0x82e2660007870000

def z224 : W := mkw 0x49abe08ae77d1bc0 0x449abe08ae77d1bc 0xb1e7e79fc7fc3fcf 0xab1e7e79fc7fc3fc

def z225 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x0ff81fe000000005 0xf0ff81fe00000000

def z226 : W := mkw 0x4dfdca2637c74554 0x84dfdca2637c7455 0xdfd99a663f8fc7ff 0x7dfd99a663f8fc7f

def z227 : W := mkw 0x20400a802ad0f60e 0x020400a802ad0f60 0x71c01a007ff0ff0d 0x771c01a007ff0ff0

def z228 : W := mkw 0x120014580800a8a9 0x0120014580800a8a 0x0000041800003800 0x0000004180000380

def z229 : W := mkw 0x0089800005050000 0x0008980000505000 0x00198000000f0002 0x000198000000f000

def z230 : W := mkw 0x06dd1e7400000000 0x006dd1e740000000 0x8fdf9e7e00000007 0xf8fdf9e7e0000000

def z231 : W := mkw 0x89e94b2500000000 0x089e94b250000000 0x81f9fbe780000007 0x781f9fbe78000000

def z232 : W := mkw 0x0b601f000800a008 0x00b601f000800a00 0x7fe01f807800f80d 0xf7fe01f807800f80

def z233 : W := mkw 0x0dbf4000500a0000 0x00dbf4000500a000 0x6fffe000780f000b 0xe6fffe000780f000

def z234 : W := mkw 0x0000800205854554 0x8000080020585455 0xd0181860078fc7fe 0x7d0181860078fc7f

def z235 : W := mkw 0x6f767f807afaf60e 0x06f767f807afaf60 0x7fe67f807ff0ff0d 0xf7fe67f807ff0ff0

def z236 : W := mkw 0x1f3614587a4aa8a9 0x01f3614587a4aa8a 0xfffe1c787ffff8ff 0xffffe1c787ffff8f

def z237 : W := mkw 0xeffffff57ffff60e 0x0effffff57ffff60 0xffffffffffffff0f 0xfffffffffffffff0

def z238 : W := mkw 0x89e9cb2705854554 0x889e9cb270585455 0x01e1e38787800701 0x001e1e3878780070

def z239 : W := mkw 0x1f761f58580aa8a9 0x01f761f58580aa8a 0xfffe1ff8780ff8ff 0xffffe1ff8780ff8f

def z240 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xf03fffffc47fffff 0xff03fffffc47ffff

def z241 : W := mkw 0x0000000001814414 0x8000000000181441 0x400000000383c030 0x0400000000383c03

def z242 : W := mkw 0x4d366088f27a1a80 0x44d366088f27a1a8 0x2e266599f8703800 0x82e266599f870380

def z243 : W := mkw 0x7fffffd87ffffeaf 0x07fffffd87ffffea 0xfffffff87fffffff 0xffffffff87ffffff

def z244 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0x901e1c78000ff8f6 0x1901e1c78000ff8f

def z245 : W := mkw 0x4000000033430000 0x0400000003343000 0x400000003b830000 0x0400000003b83000

def z246 : W := mkw 0x0000000000000000 0x0000000000000000 0x90000000000c00ce 0x290000000000c00c

def z247 : W := mkw 0x6fffffa67ffff75e 0x86fffffa67ffff75 0xffffffe67fffffff 0xfffffffe67ffffff

def z248 : W := mkw 0x0000008000101200 0x0000000800010120 0xb027e79fc4703f0f 0xab027e79fc4703f0

def z249 : W := mkw 0x0000008880101a80 0x40000008880101a8 0x0000059980003800 0x0000005998000380

def z250 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xce1e1878380fc0f2 0x5ce1e1878380fc0f

def z251 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xbe061c787800f8f4 0x9be061c787800f8f

def z252 : W := mkw 0x0000000800000880 0x0000000080000088 0x90000418000038c4 0x090000418000038c

def z253 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fc018007ff0ff08 0x57fc018007ff0ff0

def z254 : W := mkw 0x8ffd5f750800a008 0x08ffd5f750800a00 0xfffffffff800f80f 0xffffffffff800f80

def z255 : W := mkw 0x0b601f0000804404 0x00b601f000080440 0x5fe01f800780c70d 0xf5fe01f800780c70

def z256 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x41d98206078f070b 0x641d98206078f070

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0x80180060000f00f2 0x080180060000f00f

def z258 : W := mkw 0x16561e58588aecad 0x016561e58588aeca 0xffde1e787f8fffff 0xfffde1e787f8ffff

def z259 : W := mkw 0x14df8a7e558f4df5 0x814df8a7e558f4df 0xd1df9a7e078fc7ff 0x7d1df9a7e078fc7f

def z260 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x90199a66000fc7f6 0x190199a66000fc7f

def z261 : W := mkw 0x89e94b2500000000 0x089e94b250000000 0x01c0000000000000 0x001c000000000000

def z262 : W := mkw 0x2b601f8aaad0ffce 0x42b601f8aaad0ffc 0xffe01f9ffff0ffcd 0xfffe01f9ffff0ffc

def z263 : W := mkw 0x0920000022400000 0x0092000002240000 0x2e20000078700000 0x82e2000007870000

def z264 : W := mkw 0x120014da8810bbe9 0x4120014da8810bbe 0x90001fff8000fff4 0x190001fff8000fff

def z265 : W := mkw 0x161414501802a029 0x0161414501802a02 0xce1e1c783803c036 0xfce1e1c783803c03

def z266 : W := mkw 0x849fe0ffc43c1bc0 0x4849fe0ffc43c1bc 0xb03fe7ffc47c3fcf 0xab03fe7ffc47c3fc

def z267 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8fde1c7800000006 0xf8fde1c780000000

def z268 : W := mkw 0x3f741fd03ad2f62f 0x03f741fd03ad2f62 0x7ff81fe07ff3ff3d 0xf7ff81fe07ff3ff3

def z269 : W := mkw 0x0089800205050140 0x0008980020505014 0xd1d98206078f07cf 0x6d1d98206078f07c

def z270 : W := mkw 0x4dbfe08af77f1bc0 0x44dbfe08af77f1bc 0x7fffe0007fff3fcb 0xe7fffe0007fff3fc

def z271 : W := mkw 0x8ffd5f7500804404 0x08ffd5f750080440 0xdfffffff8780c70f 0xfdfffffff8780c70

def z272 : W := mkw 0x1616b4585c2ea8a9 0x01616b4585c2ea8a 0xfe3ffc787c7ff8ff 0xffe3ffc787c7ff8f

def z273 : W := mkw 0x0089800205854554 0x8008980020585455 0x51d98000078fc7fb 0x651d98000078fc7f

def z274 : W := mkw 0x00c90a2401814414 0x800c90a240181441 0x51d81a600783c73d 0x751d81a600783c73

def z275 : W := mkw 0x14160058500a08a1 0x014160058500a08a 0x0006001800000000 0x0000600180000000

def z276 : W := mkw 0x5f3674587a6aa8a9 0x05f3674587a6aa8a 0xfe3e7c78787ff8fe 0xffe3e7c78787ff8f

def z277 : W := mkw 0x14160058500a08a1 0x014160058500a08a 0xb01e0478400f38fe 0xab01e0478400f38f

def z278 : W := mkw 0x29600b802ad0f60e 0x029600b802ad0f60 0x71e003807ff0ff09 0x071e003807ff0ff0

def z279 : W := mkw 0x0ffd5f0000000000 0x00ffd5f000000000 0x0fffff8000000007 0xf0fffff800000000

def z280 : W := mkw 0x120014500800a029 0x0120014500800a02 0x000018600000c030 0x1000018600000c03

def z281 : W := mkw 0x008ba0aec53d1bd0 0xc008ba0aec53d1bd 0xb03fe7ffc47f3fff 0xab03fe7ffc47f3ff

def z282 : W := mkw 0x0920008022501200 0x0092000802250120 0x7fe007807ff03f0d 0xe7fe007807ff03f0

def z283 : W := mkw 0xcfffff75776f0000 0x0cfffff75776f000 0x6ffff8607fff000b 0xf6ffff8607fff000

def z284 : W := mkw 0x8fff7ffdc0381a80 0x48fff7ffdc0381a8 0xafffffffc0703807 0xfafffffffc070380

def z285 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0xfff81fe07fffffff 0xffff81fe07ffffff

def z286 : W := mkw 0x16dd1e741983e43d 0x816dd1e741983e43 0x4fd818603b83c030 0x54fd818603b83c03

def z287 : W := mkw 0x9fff5f7d580aa8a9 0x09fff5f7d580aa8a 0xaffffffff8003807 0xfaffffffff800380

def z288 : W := mkw 0x449fe000552f0000 0x0449fe000552f000 0x41dfe000078f000b 0x641dfe000078f000

def z289 : W := mkw 0xab601ff52ad0f60e 0x0ab601ff52ad0f60 0xffe01ffffff0ff0d 0xfffe01ffffff0ff0

def z290 : W := mkw 0x12401e7e0880edfd 0x812401e7e0880edf 0x90001e7e0000fff4 0x190001e7e0000fff

def z291 : W := mkw 0x16561e7e588aedfd 0x816561e7e588aedf 0xfe1e1e7e780ffffe 0xffe1e1e7e780ffff

def z292 : W := mkw 0xa2401ff50890f60e 0x0a2401ff50890f60 0x90001fff8000ff04 0x190001fff8000ff0

def z293 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x8fe7ff9f80000007 0xf8fe7ff9f8000000

def z294 : W := mkw 0x0616145840080880 0x0061614584008088 0xbe1e1c78400c38ce 0xfbe1e1c78400c38c

def z295 : W := mkw 0xaf745fd12ad0f60e 0x0af745fd12ad0f60 0x7fe67f99fff0ff0d 0xf7fe67f99fff0ff0

def z296 : W := mkw 0x86dd5f7500000000 0x086dd5f750000000 0x801fffff80000006 0x1801fffff8000000

def z297 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x8027e39f847c07c3 0x08027e39f847c07c

def z298 : W := mkw 0x9ffd5f751802a029 0x09ffd5f751802a02 0x4fd818603803c030 0x54fd818603803c03

def z299 : W := mkw 0x120014580800a8a9 0x0120014580800a8a 0xfe001c787800f8fc 0xffe001c787800f8f

def z300 : W := mkw 0x0000800204040140 0x0000080020404014 0x10000000040c07c8 0x010000000040c07c

def z301 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0xfffff8607fffc0ff 0xffffff8607fffc0f

def z302 : W := mkw 0x00400a0000804404 0x000400a000080440 0xd1d81a60078fc7ff 0x7d1d81a60078fc7f

def z303 : W := mkw 0x0000800004040000 0x0000080000404000 0x00018000040c000b 0x200018000040c000

def z304 : W := mkw 0x0000008000101200 0x0000000800010120 0x2020058040703800 0x8202005804070380

def z305 : W := mkw 0x6ffd5f803bd3f60e 0x06ffd5f803bd3f60 0x7ff81f807ff3ff0d 0xf7ff81f807ff3ff0

def z306 : W := mkw 0x0000a08a84341bc0 0x40000a08a84341bc 0x9021e79f84703fc5 0x09021e79f84703fc

def z307 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x7e001f807800ff0c 0xf7e001f807800ff0

def z308 : W := mkw 0x2b62bf806efcf60e 0x02b62bf806efcf60 0x7fe7ff807ffcff0f 0xf7fe7ff807ffcff0

def z309 : W := mkw 0x2b601fa62ad0f75e 0x82b601fa62ad0f75 0xffe01fe67ff0fffd 0xfffe01fe67ff0fff

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z311 : W := mkw 0x8f3675d9c0381a80 0x48f3675d9c0381a8 0x2e266599c0703800 0x82e266599c070380

def z312 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8fd99a6600000007 0x78fd99a660000000

def z313 : W := mkw 0x1414005010020021 0x0141400501002002 0x0018006000030030 0x0001800600003003

def z314 : W := mkw 0x4dbd400033430000 0x04dbd40003343000 0x6ff800007ff30009 0xe6ff800007ff3000

def z315 : W := mkw 0x9fff5f7d580aa8a9 0x09fff5f7d580aa8a 0xffde1c78780ff8fe 0xfffde1c78780ff8f

def z316 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x2fe007807ff03f01 0x82fe007807ff03f0

def z317 : W := mkw 0x4d366000726a0000 0x04d366000726a000 0x6fe660007ff00009 0xe6fe660007ff0000

def z318 : W := mkw 0x0002a080443c1200 0x00002a080443c120 0x3027e780447c3f0f 0xa3027e780447c3f0

def z319 : W := mkw 0x0002a08ac5bd5fd4 0xc0002a08ac5bd5fd 0x7000000047fffff8 0x07000000047fffff

def z320 : W := mkw 0x4dbdc00037470000 0x04dbdc0003747000 0x4fd980003f8f000b 0x64fd980003f8f000

def z321 : W := mkw 0x09600a0022c04404 0x009600a0022c0440 0x7fe01a007ff0c70d 0xf7fe01a007ff0c70

def z322 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xb000079fc47c3fcc 0x0b000079fc47c3fc

def z323 : W := mkw 0x49a9400023410000 0x049a940002341000 0x01c0000003800000 0x001c000000380000

def z324 : W := mkw 0x5dbfe058776f08a1 0x05dbfe058776f08a 0xefffe0787fff00fb 0xeefffe0787fff00f

def z325 : W := mkw 0x14160008580aa8a9 0x014160008580aa8a 0x7e1e0000780ff8fa 0xe7e1e0000780ff8f

def z326 : W := mkw 0x32401fd80890feaf 0x032401fd80890fea 0x90001ff80000fff4 0x190001ff80000fff

def z327 : W := mkw 0x5dbfe0087f6fa8a9 0x05dbfe0087f6fa8a 0x7fffe0007ffff8fb 0xe7fffe0007ffff8f

def z328 : W := mkw 0x0614145000000000 0x0061414500000000 0x0e18186000000000 0x50e1818600000000

def z329 : W := mkw 0x4dbfe026776f0150 0x84dbfe026776f015 0xefffe0667fff00fb 0xeefffe0667fff00f

def z330 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0x7e060418780ff8f8 0x87e060418780ff8f

def z331 : W := mkw 0x549fe058552f08a1 0x0549fe058552f08a 0x801fe078000f00f2 0x0801fe078000f00f

def z332 : W := mkw 0x0dbd400022400000 0x00dbd40002240000 0x6fffe0007ff0000b 0xe6fffe0007ff0000

def z333 : W := mkw 0x0b62bf8ac43c1bc0 0x40b62bf8ac43c1bc 0xbfe7ff9fc47c3fcf 0xfbfe7ff9fc47c3fc

def z334 : W := mkw 0xaffd5f752ac0e40e 0x0affd5f752ac0e40 0x4fd818603b80c000 0x54fd818603b80c00

def z335 : W := mkw 0x06161400580aa008 0x006161400580aa00 0x7e1e1c00780ff80e 0xf7e1e1c00780ff80

def z336 : W := mkw 0x36561fd8589afeaf 0x036561fd8589afea 0xfe1e1ff8780ffffe 0xffe1e1ff8780ffff

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000079f80000004 0x08000079f8000000

def z338 : W := mkw 0x0dbd400000000000 0x00dbd40000000000 0x0fd8000000000000 0x40fd800000000000

def z339 : W := mkw 0x200000800890f60e 0x0200000800890f60 0x100000000000ff00 0x0100000000000ff0

def z340 : W := mkw 0x09a9800027450000 0x009a980002745000 0x6ff980007fff000b 0xe6ff980007fff000

def z341 : W := mkw 0x3f3615d87a5abaab 0x03f3615d87a5abaa 0xfe3e1df8787ff8fe 0xffe3e1df8787ff8f

def z342 : W := mkw 0x16df1e7c598becbd 0x816df1e7c598becb 0xffde1c787b8ff8fe 0xfffde1c787b8ff8f

def z343 : W := mkw 0x8fffff75442c0000 0x08fffff75442c000 0xafffffffc47c000f 0xfafffffffc47c000

def z344 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x30200780447c3fcd 0xa30200780447c3fc

def z345 : W := mkw 0x5fbf54587b4ba8a9 0x05fbf54587b4ba8a 0xffde1c787b8ff8fe 0xfffde1c787b8ff8f

def z346 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0xffe7ff9ffff0ff0f 0xfffe7ff9ffff0ff0

def z347 : W := mkw 0x69e9eb8027f55606 0x069e9eb8027f5560 0x01e1e38007f00701 0x001e1e38007f0070

def z348 : W := mkw 0x6b62bf807ffff60e 0x06b62bf807ffff60 0x7fe01f807fffff0d 0xf7fe01f807fffff0

def z349 : W := mkw 0x9ffd5f751802a029 0x09ffd5f751802a02 0xcfffffffb803c037 0xfcfffffffb803c03

def z350 : W := mkw 0x5002a0087f6fa8a9 0x05002a0087f6fa8a 0x700000007ffff8f8 0x0700000007ffff8f

def z351 : W := mkw 0x14160058580aa8a9 0x014160058580aa8a 0xf01e0078780ff8fa 0x0f01e0078780ff8f

def z352 : W := mkw 0x8ffddf7705050150 0x88ffddf770505015 0x8fffffff800f00f7 0xf8fffffff800f00f

def z353 : W := mkw 0x16161458500a08a1 0x016161458500a08a 0x8e1e1c78000f00f6 0xf8e1e1c78000f00f

def z354 : W := mkw 0x8ffddf7704040140 0x08ffddf770404014 0x9fffffff840c07cf 0xf9fffffff840c07c

def z355 : W := mkw 0x0922a08ae67c1bc0 0x40922a08ae67c1bc 0xffe7e79ffffc3fcf 0xeffe7e79ffffc3fc

def z356 : W := mkw 0x5616b4587f6fa8a9 0x05616b4587f6fa8a 0xfe1e1c787ffff8fe 0xffe1e1c787ffff8f

def z357 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x01ffe00007ff0003 0x001ffe00007ff000

def z358 : W := mkw 0x09e98a2627c54554 0x809e98a2627c5455 0xfff99a667fffc7ff 0xffff99a667fffc7f

def z359 : W := mkw 0x0089002401010010 0x8008900240101001 0x0018006000030030 0x0001800600003003

def z360 : W := mkw 0x8fffff7fc42c09c0 0x48fffff7fc42c09c 0x8fffffff800c00c7 0xf8fffffff800c00c

def z361 : W := mkw 0x8fff5f75500a0000 0x08fff5f75500a000 0xeffffffff80f000f 0xfeffffffff80f000

def z362 : W := mkw 0x161634d8d83abaa9 0x4161634d8d83abaa 0x2e266599f8703800 0x82e266599f870380

def z363 : W := mkw 0x10020008580aa8a9 0x010020008580aa8a 0x2000000078003800 0x0200000007800380

def z364 : W := mkw 0x2b2015002a40a00a 0x02b2015002a40a00 0x0e00000038000000 0x00e0000003800000

def z365 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020078000000005 0xa002007800000000

def z366 : W := mkw 0x0089800005050000 0x0008980000505000 0x01c1800007800001 0x001c180000780000

def z367 : W := mkw 0x0002a00ac42c09c0 0x40002a00ac42c09c 0xa027e01fc47c00cb 0xaa027e01fc47c00c

def z368 : W := mkw 0x0922a000666c0000 0x00922a000666c000 0x6fe7e0007ffc000b 0xe6fe7e0007ffc000

def z369 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x2027e79fc4703f01 0x82027e79fc4703f0

def z370 : W := mkw 0x29600b8022d05606 0x029600b8022d0560 0x6fe003807ff00709 0xe6fe003807ff0070

def z371 : W := mkw 0xcffd5f7533430000 0x0cffd5f753343000 0x4fd818603b830000 0x54fd818603b83000

def z372 : W := mkw 0x8f745f5100000000 0x08f745f510000000 0x0fe67f9980000005 0xf0fe67f998000000

def z373 : W := mkw 0xaffd5ff52a50b20a 0x0affd5ff52a50b20 0xaffffffff8703807 0xfaffffffff870380

def z374 : W := mkw 0x569ff4585d2fa8a9 0x0569ff4585d2fa8a 0xfe1ffc78780ff8fe 0xffe1ffc78780ff8f

def z375 : W := mkw 0x0dbd400000000000 0x00dbd40000000000 0x8fffe79f80000007 0xe8fffe79f8000000

def z376 : W := mkw 0x8b601f7500000000 0x08b601f750000000 0x8fe01fff80000005 0xf8fe01fff8000000

def z377 : W := mkw 0x80400b2500000000 0x080400b250000000 0x0000038780000000 0x0000003878000000

def z378 : W := mkw 0x161414501802a029 0x0161414501802a02 0xde181860380fc0fe 0x7de181860380fc0f

def z379 : W := mkw 0x5fbff4daff7fbbe9 0x45fbff4daff7fbbe 0xffffffffffffffff 0xffffffffffffffff

def z380 : W := mkw 0x2b2015802a50b20a 0x02b2015802a50b20 0x3e2007807c703f0d 0xa3e2007807c703f0

def z381 : W := mkw 0x0000a08284341340 0x40000a0828434134 0x3021e787c4703f0d 0xa3021e787c4703f0

def z382 : W := mkw 0xaffd5ff522d05606 0x0affd5ff522d0560 0x8fffffff87f00707 0xf8fffffff87f0070

def z383 : W := mkw 0x12c99e7e0d85edfd 0x812c99e7e0d85edf 0xd1d99e7e078fffff 0x7d1d99e7e078ffff

def z384 : W := mkw 0x86541f7500000000 0x086541f750000000 0x8e1e1fff80000006 0xf8e1e1fff8000000

def z385 : W := mkw 0x169f94585d0fa8a9 0x0169f94585d0fa8a 0xffdf9c787f8ff8ff 0xfffdf9c787f8ff8f

def z386 : W := mkw 0x8be95f7500000000 0x08be95f750000000 0x81e1ffff80000005 0x181e1ffff8000000

def z387 : W := mkw 0x0b601f0022400000 0x00b601f002240000 0x6fe01f807ff0000d 0xf6fe01f807ff0000

def z388 : W := mkw 0x16dfbefeddbffffd 0xc16dfbefeddbffff 0xffffffffffffffff 0xffffffffffffffff

def z389 : W := mkw 0x4fffff00776f0000 0x04fffff00776f000 0x6fffff807fff000f 0xf6fffff807fff000

def z390 : W := mkw 0x4002a000776f0000 0x04002a000776f000 0x6027e0007fff000b 0xa6027e0007fff000

def z391 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x91c19a660780c7f5 0x191c19a660780c7f

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0x100002000400070d 0x2100002000400070

def z393 : W := mkw 0x8ffdfff784341340 0x48ffdfff78434134 0x8fffffff84700707 0xf8fffffff8470070

def z394 : W := mkw 0x6be9ff802ff5f60e 0x06be9ff802ff5f60 0x7fe1ff807ff0ff0d 0xf7fe1ff807ff0ff0

def z395 : W := mkw 0x14160058500a08a1 0x014160058500a08a 0xee1e0078780f00fa 0xeee1e0078780f00f

def z396 : W := mkw 0x00cbaaaec5bd5fd4 0xc00cbaaaec5bd5fd 0xf1d99a6647ffffff 0x7f1d99a6647fffff

def z397 : W := mkw 0x200000802a50b20a 0x0200000802a50b20 0x2000000078703800 0x0200000007870380

def z398 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xbe060418780c38ce 0xabe060418780c38c

def z399 : W := mkw 0x8fff5f7d40080880 0x08fff5f7d4008088 0xbfffffffc00c38cf 0xfbfffffffc00c38c

def z400 : W := mkw 0x0042aaaec4bc5fd4 0xc0042aaaec4bc5fd 0xb027ffffc47cffff 0xbb027ffffc47cfff

def z401 : W := mkw 0x0000800204040140 0x0000080020404014 0xd0199a66040fc7ff 0x7d0199a66040fc7f

def z402 : W := mkw 0x00022088c0381a80 0x400022088c0381a8 0xb0266599c07c38ce 0xab0266599c07c38c

def z403 : W := mkw 0x8414405100000000 0x0841440510000000 0x0006601980000000 0x0000660198000000

def z404 : W := mkw 0x169f947e5d0fa9f9 0x8169f947e5d0fa9f 0xfe1f9c7e780ff8fe 0xffe1f9c7e780ff8f

def z405 : W := mkw 0x100000080800a8a9 0x0100000080800a8a 0x100000000000f8f0 0x0100000000000f8f

def z406 : W := mkw 0x8dbd407500000000 0x08dbd40750000000 0x8fffe07f80000003 0xe8fffe07f8000000

def z407 : W := mkw 0x00408a2604844554 0x800408a260484455 0x90019a66040cc7ff 0x390019a66040cc7f

def z408 : W := mkw 0x00020000500a0000 0x000020000500a000 0x60000000780f0008 0x060000000780f000

def z409 : W := mkw 0x120214584808a8a9 0x0120214584808a8a 0xb0061c78400cf8fe 0xbb0061c78400cf8f

def z410 : W := mkw 0xbfff5ffd7adafeaf 0x0bfff5ffd7adafea 0xffffffffffffffff 0xffffffffffffffff

def z411 : W := mkw 0x0000000022400000 0x0000000002240000 0x600000007ff00008 0x0600000007ff0000

def z412 : W := mkw 0x8000007500000000 0x0800000750000000 0x8000007f80000000 0x08000007f8000000

def z413 : W := mkw 0x4002a00277ef4554 0x84002a00277ef455 0x700000007fffc7f8 0x0700000007fffc7f

def z414 : W := mkw 0xcffd5f7533430000 0x0cffd5f753343000 0xcfffffffbb830007 0xfcfffffffbb83000

def z415 : W := mkw 0x1416a0dad43e1be1 0x41416a0dad43e1be 0xb03fe7ffc47f3fff 0xab03fe7ffc47f3ff

def z416 : W := mkw 0xcffdff7527650000 0x0cffdff752765000 0x8fffffff87f00007 0xf8fffffff87f0000

def z417 : W := mkw 0x2b2015802a50b20a 0x02b2015802a50b20 0x7e201d807870f80c 0xf7e201d807870f80

def z418 : W := mkw 0x2b601f8022d05606 0x02b601f8022d0560 0x0fe01f8007f00705 0xf0fe01f8007f0070

def z419 : W := mkw 0x008ba08ac53d1bc0 0x4008ba08ac53d1bc 0xf1ffe79fc7ff3fcf 0xef1ffe79fc7ff3fc

def z420 : W := mkw 0x849dc07705050150 0x8849dc0770505015 0x801fe07f800f00f2 0x0801fe07f800f00f

def z421 : W := mkw 0x020014000800a008 0x0020014000800a00 0x10001c000000f804 0x110001c000000f80

def z422 : W := mkw 0x3f76bfdafefeffef 0x43f76bfdafefeffe 0xffffffffffffffff 0xffffffffffffffff

def z423 : W := mkw 0x4fbff450776f0000 0x04fbff450776f000 0xeffffc787fff000f 0xfeffffc787fff000

def z424 : W := mkw 0x9fffffffdc3ebbe9 0x49fffffffdc3ebbe 0xfffffffffc7fffff 0xffffffffffc7ffff

def z425 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x91c18206078c07cf 0x291c18206078c07c

def z426 : W := mkw 0x408ba000776f0000 0x0408ba000776f000 0x61d980007fff000b 0x661d980007fff000

def z427 : W := mkw 0x4fbff4007f6fa008 0x04fbff4007f6fa00 0x7ffffc007ffff80f 0xf7ffffc007ffff80

def z428 : W := mkw 0x0920000022400000 0x0092000002240000 0x01e0000007f00001 0x001e0000007f0000

def z429 : W := mkw 0x008ba02ec52d09d0 0xc008ba02ec52d09d 0x801fe07f800f00f2 0x0801fe07f800f00f

def z430 : W := mkw 0x849d407500000000 0x0849d40750000000 0x0018006000000000 0x0001800600000000

def z431 : W := mkw 0x8ffddf7705854554 0x88ffddf770585455 0x8fffffff87800707 0xf8fffffff8780070

def z432 : W := mkw 0x09600b0000000000 0x009600b000000000 0x01e0038000000001 0x001e003800000000

def z433 : W := mkw 0x0616b4dac43c1bc0 0x40616b4dac43c1bc 0xbe3fffffc47c3fcf 0xfbe3fffffc47c3fc

def z434 : W := mkw 0x20c98aa62fd5f75e 0x820c98aa62fd5f75 0xf1d99a667fffffff 0x7f1d99a667ffffff

def z435 : W := mkw 0x161414501802a029 0x0161414501802a02 0x0e00000038000000 0x00e0000003800000

def z436 : W := mkw 0x4dbfe008776f0880 0x04dbfe008776f088 0xffffe4187fff38cf 0xeffffe4187fff38c

def z437 : W := mkw 0x02401e000880e40c 0x002401e000880e40 0x7fc01e007f80ff0d 0xf7fc01e007f80ff0

def z438 : W := mkw 0x0000a00004240000 0x00000a0000424000 0x0021e00004700001 0x00021e0000470000

def z439 : W := mkw 0x161614dad81abbe9 0x4161614dad81abbe 0xfe1e1ffff80ffffe 0xffe1e1ffff80ffff

def z440 : W := mkw 0x8ffddf7505050000 0x08ffddf750505000 0xcfffffff878f000f 0xfcfffffff878f000

def z441 : W := mkw 0x12021408580aa8a9 0x012021408580aa8a 0x7e001c00780ff8fc 0xf7e001c00780ff8f

def z442 : W := mkw 0x4920600022600000 0x0492060002260000 0x0020600000700000 0x0002060000070000

def z443 : W := mkw 0x8f36f5dbc43c1bc0 0x48f36f5dbc43c1bc 0xbe27e79fc47c3fcf 0xabe27e79fc47c3fc

def z444 : W := mkw 0x220014802ad0f60e 0x0220014802ad0f60 0x7e001c007ff0ff0c 0xf7e001c007ff0ff0

def z445 : W := mkw 0x4dbf4000734b0000 0x04dbf4000734b000 0x6fde00007b8f000a 0xe6fde00007b8f000

def z446 : W := mkw 0x8ffd5ff500101200 0x08ffd5ff50010120 0xbfffffffc4703f0f 0xfbfffffffc4703f0

def z447 : W := mkw 0x200000002ac0e40e 0x0200000002ac0e40 0x400000003b80c000 0x0400000003b80c00

def z448 : W := mkw 0x4dffea24776f0000 0x04dffea24776f000 0xeffffa667fff000f 0xfeffffa667fff000

def z449 : W := mkw 0x0dbfe08ac43c1bc0 0x40dbfe08ac43c1bc 0xbfffe79fc47c3fcf 0xebfffe79fc47c3fc

def z450 : W := mkw 0x0089802605050150 0x8008980260505015 0xd0199866000fc0fe 0x7d0199866000fc0f

def z451 : W := mkw 0x0002a000442c0000 0x00002a000442c000 0x20000000447c0008 0x020000000447c000

def z452 : W := mkw 0x5fbff4587f6fa8a9 0x05fbff4587f6fa8a 0x6fffe4187fff380b 0xe6fffe4187fff380

def z453 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xb0018206447c3fcf 0x2b0018206447c3fc

def z454 : W := mkw 0x49abe000676d0000 0x049abe000676d000 0x21e7e00047fc000b 0xa21e7e00047fc000

def z455 : W := mkw 0x00c90a2400000000 0x000c90a240000000 0x01c1820600000001 0x001c182060000000

def z456 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x30266599c47c3fc8 0x830266599c47c3fc

def z457 : W := mkw 0x8242bfffc43c1bc0 0x48242bfffc43c1bc 0xb027ffffc47c3fcf 0xbb027ffffc47c3fc

def z458 : W := mkw 0x0dbfe000442c0000 0x00dbfe000442c000 0x2fffe000447c000b 0xe2fffe000447c000

def z459 : W := mkw 0x0000a08284341340 0x40000a0828434134 0x9021e387847c07cf 0x29021e387847c07c

def z460 : W := mkw 0x0002a088c43c1a80 0x40002a088c43c1a8 0x2027e599c47c380b 0xa2027e599c47c380

def z461 : W := mkw 0x5f3674587a6aa8a9 0x05f3674587a6aa8a 0x2e26641878703800 0x82e2664187870380

def z462 : W := mkw 0x8ffd5fff80101bc0 0x48ffd5fff80101bc 0x9fffffff80003fc7 0xf9fffffff80003fc

def z463 : W := mkw 0x0614145000000000 0x0061414500000000 0xde1e1c78000fc0fe 0xfde1e1c78000fc0f

def z464 : W := mkw 0x0002a008442c0880 0x00002a008442c088 0xb027e418447c38cf 0xab027e418447c38c

def z465 : W := mkw 0x92401f7d0800a8a9 0x092401f7d0800a8a 0x90001fff8000f8f4 0x190001fff8000f8f

def z466 : W := mkw 0x200000802ad0f60e 0x0200000802ad0f60 0x702007807ff0ff0d 0xa702007807ff0ff0

def z467 : W := mkw 0x2b22b58aee7cbbca 0x42b22b58aee7cbbc 0xbe27e79ffc7c3fcf 0xabe27e79ffc7c3fc

def z468 : W := mkw 0x4dbfe000552f0000 0x04dbfe000552f000 0x0fffe000000f0003 0xe0fffe000000f000

def z469 : W := mkw 0x00c9aaa685b55754 0xc00c9aaa685b5575 0xd1f9fbe787ffc7ff 0x7d1f9fbe787ffc7f

def z470 : W := mkw 0x8ffddf7705854554 0x88ffddf770585455 0xdfd99a66078fc7ff 0x7dfd99a66078fc7f

def z471 : W := mkw 0x3fff9ffe7fdfffff 0x83fff9ffe7fdffff 0xffff9ffe7fffffff 0xfffff9ffe7ffffff

def z472 : W := mkw 0x9fffdf7f5d8fedfd 0x89fffdf7f5d8fedf 0xffffffffff8fffff 0xfffffffffff8ffff

def z473 : W := mkw 0x00400a0000804404 0x000400a000080440 0x01c0020007800701 0x001c002000780070

def z474 : W := mkw 0x10020008580aa8a9 0x010020008580aa8a 0xf0181860780ff8fe 0x7f0181860780ff8f

def z475 : W := mkw 0x22401f000880e40e 0x022401f000880e40 0x000018000000c000 0x1000018000000c00

def z476 : W := mkw 0x5fbff4507f6fa029 0x05fbff4507f6fa02 0x6ffff8607fffc03b 0xf6ffff8607fffc03

def z477 : W := mkw 0x0000800005050000 0x0000080000505000 0x40000000078f0008 0x040000000078f000

def z478 : W := mkw 0x20400b8000905606 0x020400b800090560 0x0000038000000700 0x0000003800000070

def z479 : W := mkw 0x12021458580aa8a9 0x012021458580aa8a 0xf0001c78780ff8fc 0x1f0001c78780ff8f

def z480 : W := mkw 0x00400a8000905604 0x000400a800090560 0x71e01f8047f0ff0d 0xf71e01f8047f0ff0

def z481 : W := mkw 0x00c98aa605955754 0x800c98aa60595575 0xf1f99fe647ffffff 0xff1f99fe647fffff

def z482 : W := mkw 0x0002a000442c0000 0x00002a000442c000 0x0007e000000c0002 0x00007e000000c000

def z483 : W := mkw 0x300200887adafeaf 0x0300200887adafea 0x700000007ffffff8 0x0700000007ffffff

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0x0026659980000000 0x8002665998000000

def z485 : W := mkw 0x020014800810b208 0x0020014800810b20 0x7e201f807c70ff0d 0xf7e201f807c70ff0

def z486 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xae1e0478780f38f2 0x8ae1e0478780f38f

def z487 : W := mkw 0x6dffeb8077ff5606 0x06dffeb8077ff560 0x6fffe3807fff070b 0xe6fffe3807fff070

def z488 : W := mkw 0x00400a2400804414 0x800400a240080441 0x000018600000c030 0x1000018600000c03

def z489 : W := mkw 0x0000a08284341340 0x40000a0828434134 0x0000000004700700 0x0000000000470070

def z490 : W := mkw 0x00cbaaaec43c1bc0 0x400cbaaaec43c1bc 0xb1ffffffc47c3fcf 0xfb1ffffffc47c3fc

def z491 : W := mkw 0x2b609f822fd5f75e 0x82b609f822fd5f75 0x7fe01f807ffffffd 0xf7fe01f807ffffff

def z492 : W := mkw 0x0920000022400000 0x0092000002240000 0x4fc000003b800000 0x44fc000003b80000

def z493 : W := mkw 0x00cbaaaec5bd5fd4 0xc00cbaaaec5bd5fd 0xb1e7e79fc7fc3fcf 0xab1e7e79fc7fc3fc

def z494 : W := mkw 0x8fbd555100000000 0x08fbd55510000000 0x0fffe59980000003 0xe0fffe5998000000

def z495 : W := mkw 0x8ffd5f7501814414 0x88ffd5f750181441 0x4fd818600383c030 0x54fd818600383c03

def z496 : W := mkw 0x8be95f2500000000 0x08be95f250000000 0x0fe1ff8780000005 0xf0fe1ff878000000

def z497 : W := mkw 0x09a9400000000000 0x009a940000000000 0x01e1e00000000001 0x001e1e0000000000

def z498 : W := mkw 0x1616945a5c0ea9e9 0x01616945a5c0ea9e 0xfe1f9e7e7c0fffff 0xffe1f9e7e7c0ffff

def z499 : W := mkw 0x0000008000101200 0x0000000800010120 0x3000000044703f08 0x03000000044703f0

def z500 : W := mkw 0x4dbde00027650000 0x04dbde0002765000 0x0fffe00007f00003 0xe0fffe00007f0000

def z501 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x0ffe7df980000000 0xd0ffe7df98000000

def z502 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x11e01f8007f0ff05 0x111e01f8007f0ff0

def z503 : W := mkw 0x0000000000000000 0x0000000000000000 0x401818600003c030 0x5401818600003c03

def z504 : W := mkw 0x0089000001010000 0x0008900000101000 0x41d8000003830000 0x441d800000383000

def z505 : W := mkw 0x0000800205050150 0x8000080020505015 0x00000000000f00f0 0x000000000000f00f

def z506 : W := mkw 0xcfff7f75726a0000 0x0cfff7f75726a000 0xaffffffff8700007 0xfaffffffff870000

def z507 : W := mkw 0xcfffff75552f0000 0x0cfffff75552f000 0x8fffffff800f0007 0xf8fffffff800f000

def z508 : W := mkw 0xcffffffff77f1bc0 0x4cffffffff77f1bc 0xffffffffffff3fcf 0xfffffffffffff3fc

def z509 : W := mkw 0x3f761fd87adafeaf 0x03f761fd87adafea 0x7fe61f987ff0ff0d 0xf7fe61f987ff0ff0

def z510 : W := mkw 0x06dd9e7605854554 0x806dd9e760585455 0xdfdf9e7e078fc7ff 0xfdfdf9e7e078fc7f

def z511 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x51c01f800780ff0d 0x751c01f800780ff0

def z512 : W := mkw 0x2be91fa42ad0f60e 0x02be91fa42ad0f60 0xfff99fe67ff0ff0f 0xffff99fe67ff0ff0

def z513 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xb0060418447c3fce 0xab0060418447c3fc

def z514 : W := mkw 0x449fe08ad53f1bc0 0x4449fe08ad53f1bc 0xb03fe79fc47f3fcf 0xab03fe79fc47f3fc

def z515 : W := mkw 0x0002a00ac42c09c0 0x40002a00ac42c09c 0x00000000000c00c0 0x000000000000c00c

def z516 : W := mkw 0x0000800205854554 0x8000080020585455 0x0000000007800700 0x0000000000780070

def z517 : W := mkw 0x10cb8a2e5d8fedfd 0x810cb8a2e5d8fedf 0xf1d99a667f8fffff 0x7f1d99a667f8ffff

def z518 : W := mkw 0x8dfd4b2500000000 0x08dfd4b250000000 0x0fffe38780000003 0xe0fffe3878000000

def z519 : W := mkw 0x2242bf8accbcffce 0x42242bf8accbcffc 0xb027ff9fc47cffcf 0xbb027ff9fc47cffc

def z520 : W := mkw 0x0414000000000000 0x0041400000000000 0x0e1e000000000002 0xe0e1e00000000000

def z521 : W := mkw 0x49abe000776f0000 0x049abe000776f000 0x61e1e0007fff0009 0x061e1e0007fff000

def z522 : W := mkw 0x3f741f503ac2e42f 0x03f741f503ac2e42 0x4fd818603b83c030 0x54fd818603b83c03

def z523 : W := mkw 0x0000800204040140 0x0000080020404014 0x0001820604000701 0x0000182060400070

def z524 : W := mkw 0x00c98aae85955fd4 0xc00c98aae85955fd 0xd1d99fff878fffff 0x7d1d99fff878ffff

def z525 : W := mkw 0x00c98a2405854414 0x800c98a240585441 0x41d99860078fc03b 0x741d99860078fc03

def z526 : W := mkw 0x00c98a2604040140 0x000c98a260404014 0x91d99a66040c07cf 0x791d99a66040c07c

def z527 : W := mkw 0x0614145000000000 0x0061414500000000 0x0e06041800000000 0x80e0604180000000

def z528 : W := mkw 0x0002000840080880 0x0000200084008088 0x30000000400c38c8 0x030000000400c38c

def z529 : W := mkw 0x6dbfe0807ffff60e 0x06dbfe0807ffff60 0x7fffe0007fffff0b 0xe7fffe0007fffff0

def z530 : W := mkw 0x0002000840080880 0x0000200084008088 0xf01e1c78400ff8fe 0xff01e1c78400ff8f

def z531 : W := mkw 0x00c9aaa685b55754 0xc00c9aaa685b5575 0x01e1e38787f00701 0x001e1e38787f0070

def z532 : W := mkw 0x0000008000101200 0x0000000800010120 0x0020038004700701 0x0002003800470070

def z533 : W := mkw 0x8200155100000000 0x0820015510000000 0x0000059980000000 0x0000005998000000

def z534 : W := mkw 0x4dbf6000736b0000 0x04dbf6000736b000 0x6ffe60007bf30000 0xc6ffe60007bf3000

def z535 : W := mkw 0x4416a000776f0000 0x04416a000776f000 0x6e1e00007fff000a 0xe6e1e00007fff000

def z536 : W := mkw 0x4002a000552f0000 0x04002a000552f000 0x00000000000f0000 0x000000000000f000

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x8006041800000006 0xa800604180000000

def z538 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x4fdfe0003b8f0002 0x44fdfe0003b8f000

def z539 : W := mkw 0x00c90a2601814554 0x800c90a260181455 0xd1d81a660383c7f4 0x5d1d81a660383c7f

def z540 : W := mkw 0x82401fff80101bc0 0x482401fff80101bc 0x90001fff80003fc4 0x190001fff80003fc

def z541 : W := mkw 0xaffd5ff52ad0f60e 0x0affd5ff52ad0f60 0x7ff81fe07ff0ff0d 0xf7ff81fe07ff0ff0

def z542 : W := mkw 0x8920410100000000 0x0892041010000000 0x0020618180000000 0x0002061818000000

def z543 : W := mkw 0x8089402500000000 0x0808940250000000 0x0001e00780000000 0x00001e0078000000

def z544 : W := mkw 0x0000800204040140 0x0000080020404014 0x80018006000c00c2 0x080018006000c00c

def z545 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x0ff9fbe780000001 0x50ff9fbe78000000

def z546 : W := mkw 0x0002a000442c0000 0x00002a000442c000 0xa027e79fc47c000f 0xaa027e79fc47c000

def z547 : W := mkw 0x00cbaa2645ad4554 0x800cbaa2645ad455 0xf1fffa6647ffc7ff 0xff1fffa6647ffc7f

def z548 : W := mkw 0x04160008500a0880 0x004160008500a088 0xfe1e0418780f38ce 0xefe1e0418780f38c

def z549 : W := mkw 0x0002800a440c09c0 0x00002800a440c09c 0xb007861e440c3fcf 0xab007861e440c3fc

def z550 : W := mkw 0x8f34555100000000 0x08f3455510000000 0x8e3e7df980000006 0xf8e3e7df98000000

def z551 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0x7e061c187800f80c 0xf7e061c187800f80

def z552 : W := mkw 0x869d547500000000 0x0869d54750000000 0x8e1ffc7f80000006 0xf8e1ffc7f8000000

def z553 : W := mkw 0x020014000800a008 0x0020014000800a00 0x4e0018003800c000 0x54e0018003800c00

def z554 : W := mkw 0x29600b8022d05606 0x029600b8022d0560 0x51e01b8007f0c70d 0x751e01b8007f0c70

def z555 : W := mkw 0x0dbdc00005050000 0x00dbdc0000505000 0x4fffe000078f000b 0xe4fffe000078f000

def z556 : W := mkw 0x0002008840181a80 0x00002008840181a8 0xb0260798447c3fcf 0xab0260798447c3fc

def z557 : W := mkw 0x0414005000000000 0x0041400500000000 0x801e007800000002 0x0801e00780000000

def z558 : W := mkw 0x5fbd54503b43a029 0x05fbd54503b43a02 0x4fd818603b83c030 0x54fd818603b83c03

def z559 : W := mkw 0x0000a00284240140 0x40000a0028424014 0x0001e00780000000 0x00001e0078000000

def z560 : W := mkw 0x0000800204040140 0x0000080020404014 0x9027e79f840c07cf 0xa9027e79f840c07c

def z561 : W := mkw 0x2002a08aeefcffce 0x42002a08aeefcffc 0xf027e79ffffcffcf 0xaf027e79ffffcffc

def z562 : W := mkw 0x0042aa8ac4bc5fc4 0x40042aa8ac4bc5fc 0xf1e7ff9fc7fcffcf 0xff1e7ff9fc7fcffc

def z563 : W := mkw 0xaffddff72fd5f75e 0x8affddff72fd5f75 0xffffffffffffffff 0xffffffffffffffff

def z564 : W := mkw 0x49e9ea2627e54554 0x849e9ea2627e5455 0xd1f9fa6607ffc7ff 0x7d1f9fa6607ffc7f

def z565 : W := mkw 0x00400a2600804554 0x800400a260080455 0xd0181a66000fc7fe 0x7d0181a66000fc7f

def z566 : W := mkw 0x9f365559580aa8a9 0x09f365559580aa8a 0x2e266599f8003800 0x82e266599f800380

def z567 : W := mkw 0x6002a0807ffff60e 0x06002a0807ffff60 0x700000007fffff08 0x0700000007fffff0

def z568 : W := mkw 0x0000208080301200 0x4000020808030120 0x0020618180700000 0x0002061818070000

def z569 : W := mkw 0x2b621f886ad8fe8e 0x02b621f886ad8fe8 0xffe61f987ffcffcf 0xfffe61f987ffcffc

def z570 : W := mkw 0xc49fe075552f0000 0x0c49fe075552f000 0x801fe07f800f0002 0x0801fe07f800f000

def z571 : W := mkw 0x4dbfe088f77f1a80 0x44dbfe088f77f1a8 0x6fffe599ffff380b 0xe6fffe599ffff380

def z572 : W := mkw 0x0000008a80101bc0 0x40000008a80101bc 0x1000000000003fc0 0x01000000000003fc

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018186000000006 0x7801818600000000

def z574 : W := mkw 0x00022088c0381a80 0x400022088c0381a8 0x30266799c4703f0d 0xa30266799c4703f0

def z575 : W := mkw 0x00408a0204844544 0x000408a020484454 0xd1c19a06078cc7cf 0x7d1c19a06078cc7c

def z576 : W := mkw 0x000000000800a008 0x0000000000800a00 0x700000007800f808 0x0700000007800f80

def z577 : W := mkw 0x1202b4dacc3cbbe9 0x41202b4dacc3cbbe 0xb027ffffc47cffff 0xbb027ffffc47cfff

def z578 : W := mkw 0x4000a00027650000 0x04000a0002765000 0x0000000007f00000 0x00000000007f0000

def z579 : W := mkw 0xabe95fa52ad0f60e 0x0abe95fa52ad0f60 0x7fe1ff87fff0ff0d 0xf7fe1ff87fff0ff0

def z580 : W := mkw 0x161614d8581abaa9 0x0161614d8581abaa 0xfe3e1ff87c7fffff 0xffe3e1ff87c7ffff

def z581 : W := mkw 0x84ddca7705854554 0x884ddca770585455 0xd1dffa7f878fc7ff 0x7d1dffa7f878fc7f

def z582 : W := mkw 0x1fbf5458580aa8a9 0x01fbf5458580aa8a 0xfffffc78780ff8ff 0xffffffc78780ff8f

def z583 : W := mkw 0x2b609f822ed4f74e 0x02b609f822ed4f74 0xffe19f867ffcffcf 0xfffe19f867ffcffc

def z584 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x3021e387c47c3fc9 0x03021e387c47c3fc

def z585 : W := mkw 0x0414000010020000 0x0041400001002000 0x4e18000038030000 0x44e1800003803000

def z586 : W := mkw 0x0002a00ac42c09c0 0x40002a00ac42c09c 0xb007e41fc00c38ce 0xab007e41fc00c38c

def z587 : W := mkw 0x449fe000552f0000 0x0449fe000552f000 0x203fe000447f000b 0xa203fe000447f000

def z588 : W := mkw 0x84dd4a7500000000 0x084dd4a750000000 0x81dffa7f80000007 0x781dffa7f8000000

def z589 : W := mkw 0x49e9ea2627e54554 0x849e9ea2627e5455 0x01e1e20607f00701 0x001e1e20607f0070

def z590 : W := mkw 0x0000a08284341340 0x40000a0828434134 0x8027e79f84700707 0xa8027e79f8470070

def z591 : W := mkw 0x0be99f2605854554 0x80be99f260585455 0xdff99fe6078fc7ff 0xfdff99fe6078fc7f

def z592 : W := mkw 0x2be99f262fc5e55e 0x82be99f262fc5e55 0xdfd99a663f8fc7ff 0x7dfd99a663f8fc7f

def z593 : W := mkw 0x049f8000550f0000 0x0049f8000550f000 0x6fdf80007f8f000b 0xe6fdf80007f8f000

def z594 : W := mkw 0x4d366000726a0000 0x04d366000726a000 0x6e3e6000787f000a 0xe6e3e6000787f000

def z595 : W := mkw 0x06161450500a0000 0x006161450500a000 0xee1e1c78780f000e 0xfee1e1c78780f000

def z596 : W := mkw 0x9ffd5f7d0800a8a9 0x09ffd5f7d0800a8a 0x9fffffff8000f8f7 0xf9fffffff8000f8f

def z597 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8fdff87f80000002 0x58fdff87f8000000

def z598 : W := mkw 0x29600b0022c04406 0x029600b0022c0440 0x01c0000003800000 0x001c000000380000

def z599 : W := mkw 0x4dbf6000726a0000 0x04dbf6000726a000 0x2fffe00078700003 0xe2fffe0007870000

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x0021e38780000001 0x00021e3878000000

def z601 : W := mkw 0x0b20150000000000 0x00b2015000000000 0x0e20058000000000 0x80e2005800000000

def z602 : W := mkw 0x149f807e550f09f1 0x8149f807e550f09f 0x801f807e000f00f2 0x0801f807e000f00f

def z603 : W := mkw 0x04160000500a0000 0x004160000500a000 0xfe1e1860780fc0fe 0xffe1e1860780fc0f

def z604 : W := mkw 0x00cb8a2e458d4dd4 0x800cb8a2e458d4dd 0xf1df9e7e478fffff 0xff1df9e7e478ffff

def z605 : W := mkw 0x449d400011030000 0x0449d40001103000 0x0018000000030000 0x0001800000003000

def z606 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x0ffff86000000003 0xf0ffff8600000000

def z607 : W := mkw 0x0002a00ac42c09c0 0x40002a00ac42c09c 0x8027e79f800c00c7 0xa8027e79f800c00c

def z608 : W := mkw 0x2be91fa42bd1f61e 0x82be91fa42bd1f61 0x7ff81fe07ff3ff3d 0xf7ff81fe07ff3ff3

def z609 : W := mkw 0x0dfdca2605854554 0x80dfdca260585455 0xdffffa66078fc7ff 0xfdffffa66078fc7f

def z610 : W := mkw 0x29600b8022d05606 0x029600b8022d0560 0x31e0078047f03f0d 0xa31e0078047f03f0

def z611 : W := mkw 0x4d36e08af67e1bc0 0x44d36e08af67e1bc 0xbe27e79ffc7c3fcf 0xabe27e79ffc7c3fc

def z612 : W := mkw 0x00c90a2400804404 0x000c90a240080440 0xd1d99a660780c70f 0x7d1d99a660780c70

def z613 : W := mkw 0xa9e94ba522d05606 0x0a9e94ba522d0560 0x01e1e38787f00701 0x001e1e38787f0070

def z614 : W := mkw 0x8f34555100000000 0x08f3455510000000 0x0e00000000000000 0x00e0000000000000

def z615 : W := mkw 0x0b601f8000101200 0x00b601f800010120 0x3fe01f8044703f0d 0xf3fe01f8044703f0

def z616 : W := mkw 0x5ffffe7e7fefedfd 0x85ffffe7e7fefedf 0xfffffe7e7fffffff 0xffffffe7e7ffffff

def z617 : W := mkw 0x4d36e000776f0000 0x04d36e000776f000 0x6e2660007fff0008 0x86e2660007fff000

def z618 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x51c18206078fc7f9 0x051c18206078fc7f

def z619 : W := mkw 0x0002000840080880 0x0000200084008088 0xb027e79fc00c38cf 0xab027e79fc00c38c

def z620 : W := mkw 0x44dfea2655af4554 0x844dfea2655af455 0xd1dffa66078fc7ff 0x7d1dffa66078fc7f

def z621 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0x6e1e1c787803f830 0xd6e1e1c787803f83

def z622 : W := mkw 0x008ba000452d0000 0x0008ba000452d000 0x61ffe00047ff000b 0xe61ffe00047ff000

def z623 : W := mkw 0x4dbfe082f77f1340 0x44dbfe082f77f134 0x6fffe387ffff070b 0xe6fffe387ffff070

def z624 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x30201f804470ff0d 0xb30201f804470ff0

def z625 : W := mkw 0x00c98a0005854404 0x000c98a000585440 0x51d99a00078fc70f 0x751d99a00078fc70

def z626 : W := mkw 0x1616b45adc2ea9e9 0x41616b45adc2ea9e 0xfe1ffc7ff80ff8fe 0xffe1ffc7ff80ff8f

def z627 : W := mkw 0x0d34400000000000 0x00d3440000000000 0x0e26600000000000 0x80e2660000000000

def z628 : W := mkw 0x4089e00005250000 0x04089e0000525000 0x0001e00000000000 0x00001e0000000000

def z629 : W := mkw 0x2b2015802a50b20a 0x02b2015802a50b20 0x6fe005807ff03809 0xe6fe005807ff0380

def z630 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x81d98266078f07f3 0x081d98266078f07f

def z631 : W := mkw 0x22401f802ad0f60e 0x022401f802ad0f60 0x70001f807ff0ff0c 0x170001f807ff0ff0

def z632 : W := mkw 0xdfffff7d7f6fa8a9 0x0dfffff7d7f6fa8a 0xfffffffffffff8ff 0xffffffffffffff8f

def z633 : W := mkw 0x0000008a80101bc0 0x40000008a80101bc 0xb020079fc4703fcd 0xab020079fc4703fc

def z634 : W := mkw 0x82401f7500000000 0x082401f750000000 0x0000186000000000 0x1000018600000000

def z635 : W := mkw 0x1616945a5d8fedfd 0x81616945a5d8fedf 0xfe1e1c787f8ffffe 0xffe1e1c787f8ffff

def z636 : W := mkw 0x00400a0000804404 0x000400a000080440 0x41c018000380c000 0x541c018000380c00

def z637 : W := mkw 0x0000000000000000 0x0000000000000000 0x40180000000f000a 0x640180000000f000

def z638 : W := mkw 0x8fffffffc5bd5fd4 0xc8fffffffc5bd5fd 0xffffffffc7ffffff 0xfffffffffc7fffff

def z639 : W := mkw 0x0000008280101340 0x4000000828010134 0x0000038780000700 0x0000003878000070

def z640 : W := mkw 0x2960ab82a6f45746 0x42960ab82a6f4574 0x01e1e38787f00701 0x001e1e38787f0070

def z641 : W := mkw 0x0000000200000140 0x0000000020000014 0x90000206000007c4 0x090000206000007c

def z642 : W := mkw 0x0002000840080880 0x0000200084008088 0x2006041840003800 0x8200604184000380

def z643 : W := mkw 0x00022088c0381a80 0x400022088c0381a8 0xa027e79fc0703807 0xaa027e79fc070380

def z644 : W := mkw 0xaf3455d12a50b20a 0x0af3455d12a50b20 0x2e266599f8703800 0x82e266599f870380

def z645 : W := mkw 0x16dd9e761d87e57d 0x816dd9e761d87e57 0xdfd99a663f8fc7ff 0x7dfd99a663f8fc7f

def z646 : W := mkw 0xcdffeb25776f0000 0x0cdffeb25776f000 0x6fffe387ffff000b 0xe6fffe387ffff000

def z647 : W := mkw 0x449fe000776f0000 0x0449fe000776f000 0x601fe0007fff000a 0x0601fe0007fff000

def z648 : W := mkw 0x0200140000000000 0x0020014000000000 0x0e001c0000000004 0xf0e001c000000000

def z649 : W := mkw 0x10020008500a08a1 0x010020008500a08a 0x00000000000f00f0 0x000000000000f00f

def z650 : W := mkw 0x2b60bf82aef4f74e 0x42b60bf82aef4f74 0x7fe1ff87fff0ff0d 0xf7fe1ff87fff0ff0

def z651 : W := mkw 0x8ffd5f7700804554 0x88ffd5f770080455 0x9fffffff8000c7f7 0xf9fffffff8000c7f

def z652 : W := mkw 0x4dffea2477ef4414 0x84dffea2477ef441 0x6ffff8607fffc03b 0xf6ffff8607fffc03

def z653 : W := mkw 0x00400a2400000000 0x000400a240000000 0x80001a6600000004 0x180001a660000000

def z654 : W := mkw 0x0000008a80101bc0 0x40000008a80101bc 0x9027e79f80003fc7 0xa9027e79f80003fc

def z655 : W := mkw 0x04160000500a0000 0x004160000500a000 0x2e06000078000000 0x82e0600007800000

def z656 : W := mkw 0x2b601f800890f60e 0x02b601f800890f60 0x1fe01f800000ff05 0xf1fe01f800000ff0

def z657 : W := mkw 0x1416a05ad42e09e1 0x41416a05ad42e09e 0x801fe07f800f00f2 0x0801fe07f800f00f

def z658 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x5fc01f803b80ff04 0x55fc01f803b80ff0

def z659 : W := mkw 0x0002008ac0181bc0 0x40002008ac0181bc 0xb006079fc00c3fce 0xab006079fc00c3fc

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0x500018000000c00c 0x7500018000000c00

def z661 : W := mkw 0x2b2015802ad0f60e 0x02b2015802ad0f60 0x7e2005807ff0ff08 0x87e2005807ff0ff0

def z662 : W := mkw 0x0202b48acc3cbbc8 0x40202b48acc3cbbc 0xfe27ff9ffc7cffcf 0xffe27ff9ffc7cffc

def z663 : W := mkw 0x10000058000008a1 0x010000058000008a 0x80000078000000f0 0x080000078000000f

def z664 : W := mkw 0x361614d87adafeaf 0x0361614d87adafea 0xfe1e1c787ffffffe 0xffe1e1c787ffffff

def z665 : W := mkw 0x00c90a2401814414 0x800c90a240181441 0x01c0000003800000 0x001c000000380000

def z666 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x51c19a060780c70d 0x751c19a060780c70

def z667 : W := mkw 0x10020008580aa8a9 0x010020008580aa8a 0xf0060418780ff8fe 0xaf0060418780ff8f

def z668 : W := mkw 0x44166000502a0000 0x044166000502a000 0x0006600000000000 0x0000660000000000

def z669 : W := mkw 0x0000000000804404 0x0000000000080440 0x500000000780c708 0x0500000000780c70

def z670 : W := mkw 0x0200145000000000 0x0020014500000000 0x80001c7800000004 0x180001c780000000

def z671 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x81d99a6607800707 0x781d99a660780070

def z672 : W := mkw 0x82c99f7705854554 0x882c99f770585455 0xd1d99fff878fc7ff 0x7d1d99fff878fc7f

def z673 : W := mkw 0x161634d8d83abaa9 0x4161634d8d83abaa 0xfe3e7df9f87ff8fe 0xffe3e7df9f87ff8f

def z674 : W := mkw 0x020214084808a888 0x0020214084808a88 0xfe061c18780cf8ce 0xffe061c18780cf8c

def z675 : W := mkw 0x3f761f587acaecaf 0x03f761f587acaeca 0xffde1c787b8ff8fe 0xfffde1c787b8ff8f

def z676 : W := mkw 0x9fff5f7d500a08a1 0x09fff5f7d500a08a 0x8fffffff800f00f7 0xf8fffffff800f00f

def z677 : W := mkw 0x2be99fa62fd5f75e 0x82be99fa62fd5f75 0x7fe19f867ff0ff0d 0xf7fe19f867ff0ff0

def z678 : W := mkw 0x049d400000000000 0x0049d40000000000 0x001fe00000000002 0x0001fe0000000000

def z679 : W := mkw 0x969f547d580aa8a9 0x0969f547d580aa8a 0xfe1ffc7ff80ff8fe 0xffe1ffc7ff80ff8f

def z680 : W := mkw 0x00c98a2405050000 0x000c98a240505000 0xc1d99a66078f000f 0x7c1d99a66078f000

def z681 : W := mkw 0xcfffff7777ef4554 0x8cfffff7777ef455 0xffffffffffffc7ff 0xfffffffffffffc7f

def z682 : W := mkw 0x82401f7700804554 0x882401f770080455 0x90001fff8000c7f4 0x190001fff8000c7f

def z683 : W := mkw 0x0416a08ad43e1bc0 0x40416a08ad43e1bc 0xfe3fe79ffc7f3fcf 0xefe3fe79ffc7f3fc

def z684 : W := mkw 0x00400a2600804554 0x800400a260080455 0xd1c01a660780c7fd 0x7d1c01a660780c7f

def z685 : W := mkw 0x2962ab8ae6fc5fc6 0x42962ab8ae6fc5fc 0xb1e7e79fc7fc3fcf 0xab1e7e79fc7fc3fc

def z686 : W := mkw 0x89e9cb2705854554 0x889e9cb270585455 0xd1f9fbe7878fc7ff 0x7d1f9fbe7878fc7f

def z687 : W := mkw 0x00c98a2605050150 0x800c98a260505015 0x81d99a66000f00f7 0x781d99a66000f00f

def z688 : W := mkw 0x0089002400000000 0x0008900240000000 0x8019806600000002 0x0801980660000000

def z689 : W := mkw 0x4d34400032420000 0x04d3440003242000 0x0e00000038000000 0x00e0000003800000

def z690 : W := mkw 0x49a9e082a7751340 0x449a9e082a775134 0x01e1e38787f00701 0x001e1e38787f0070

def z691 : W := mkw 0x49a9e00027650000 0x049a9e0002765000 0x41f9e00007ff000b 0x641f9e00007ff000

def z692 : W := mkw 0x00408a0205854554 0x800408a020585455 0x51c01a00078fc7fd 0x751c01a00078fc7f

def z693 : W := mkw 0x4dbfe00277ef4554 0x84dbfe00277ef455 0x7fffe0007fffc7fb 0xe7fffe0007fffc7f

def z694 : W := mkw 0x04160000500a0000 0x004160000500a000 0x001e0000000f0002 0x0001e0000000f000

def z695 : W := mkw 0x0089800005050000 0x0008980000505000 0xd1d99860078fc0ff 0x7d1d99860078fc0f

def z696 : W := mkw 0x100000001802a029 0x0100000001802a02 0x400000003803c030 0x0400000003803c03

def z697 : W := mkw 0x2be99f802fd5f60e 0x02be99f802fd5f60 0x7ff99f807fffff0f 0xf7ff99f807fffff0

def z698 : W := mkw 0x0b2014002a40a008 0x00b2014002a40a00 0x7fe01c007ff0f80d 0xf7fe01c007ff0f80

def z699 : W := mkw 0x0416a000542e0000 0x00416a000542e000 0x6e3fe0007c7f000b 0xe6e3fe0007c7f000

def z700 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xa027e59fc07c38c2 0x8a027e59fc07c38c

def z701 : W := mkw 0x0000000200804554 0x8000000020080455 0x100000000000c7f0 0x0100000000000c7f

def z702 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xae1e1c7878003806 0xfae1e1c787800380

def z703 : W := mkw 0x00400a0000000000 0x000400a000000000 0x01c01a0000000005 0x701c01a000000000

def z704 : W := mkw 0x3b601fd82ad0feaf 0x03b601fd82ad0fea 0xffe01ff87ff0fffd 0xfffe01ff87ff0fff

def z705 : W := mkw 0x8f745f7500000000 0x08f745f750000000 0x8e267fff80000004 0x98e267fff8000000

def z706 : W := mkw 0x1616b4dadc3ebbe9 0x41616b4dadc3ebbe 0xbe27e79ffc7c3fcf 0xabe27e79ffc7c3fc

def z707 : W := mkw 0xab601ff52ad0f60e 0x0ab601ff52ad0f60 0xffe7fffffff0ff0f 0xfffe7fffffff0ff0

def z708 : W := mkw 0x0922000062480000 0x0092200006248000 0x6fe600007ffc000b 0xe6fe600007ffc000

def z709 : W := mkw 0x0002a08ad43e1bc0 0x40002a08ad43e1bc 0x700000007c7f3fc8 0x0700000007c7f3fc

def z710 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x51d99a66078fc7f9 0x551d99a66078fc7f

def z711 : W := mkw 0x0000a08284341340 0x40000a0828434134 0xb027e79fc4703f0f 0xab027e79fc4703f0

def z712 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fde00007fff000a 0xe6fde00007fff000

def z713 : W := mkw 0x0000000000000000 0x0000000000000000 0x8007e79f80000006 0x08007e79f8000000

def z714 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0xdfffffff8000c00f 0xfdfffffff8000c00

def z715 : W := mkw 0x8ffd5f750800a008 0x08ffd5f750800a00 0x9fffffff8000f807 0xf9fffffff8000f80

def z716 : W := mkw 0x3d760bd872da5ea7 0x03d760bd872da5ea 0x81fe03f807ff07f3 0x081fe03f807ff07f

def z717 : W := mkw 0x4dbd400033430000 0x04dbd40003343000 0x6fffe0007ff3000b 0xe6fffe0007ff3000

def z718 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6ff800007fff0009 0xe6ff800007fff000

def z719 : W := mkw 0x5ba9f4582f65a8a9 0x05ba9f4582f65a8a 0x91e1fc7807f0f8f5 0x191e1fc7807f0f8f

def z720 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0x7e181c60780ff8fc 0xf7e181c60780ff8f

def z721 : W := mkw 0x4dbfe00af76f09c0 0x44dbfe00af76f09c 0xffffe41fffff38cf 0xeffffe41fffff38c

def z722 : W := mkw 0x4d36e000766e0000 0x04d36e000766e000 0x6fe7e0007ffc000b 0xe6fe7e0007ffc000

def z723 : W := mkw 0x0fbd545000000000 0x00fbd54500000000 0x8fffffff80000007 0xf8fffffff8000000

def z724 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x90001f9f8000ff04 0x190001f9f8000ff0

def z725 : W := mkw 0x8fbd557500000000 0x08fbd55750000000 0x0e27e59f80000000 0x80e27e59f8000000

def z726 : W := mkw 0x449fe02ed52f09d0 0xc449fe02ed52f09d 0x801fe07f800f00f2 0x0801fe07f800f00f

def z727 : W := mkw 0x0089800205050140 0x0008980020505014 0xd1d99a66078fc7ff 0x7d1d99a66078fc7f

def z728 : W := mkw 0xa2401fff8890ffce 0x4a2401fff8890ffc 0x90001fff8000ffc4 0x190001fff8000ffc

def z729 : W := mkw 0x49abe000676d0000 0x049abe000676d000 0x6fe7e0007ffc000b 0xe6fe7e0007ffc000

def z730 : W := mkw 0x16df9e7e5d8fedfd 0x816df9e7e5d8fedf 0x2fc7861e7f803f01 0x82fc7861e7f803f0

def z731 : W := mkw 0x4dbf6000736b0000 0x04dbf6000736b000 0x6fffe0007bf30003 0xe6fffe0007bf3000

def z732 : W := mkw 0xc242bf75776f0000 0x0c242bf75776f000 0xe0001fffffff000c 0x1e0001fffffff000

def z733 : W := mkw 0x4dbfe02ef76f09d0 0xc4dbfe02ef76f09d 0xefffe07fffff00fb 0xeefffe07fffff00f

def z734 : W := mkw 0x8ffd5f7522400000 0x08ffd5f752240000 0x8fffffff87f00007 0xf8fffffff87f0000

def z735 : W := mkw 0x66dfff805dbff60e 0x066dfff805dbff60 0x101fff80000fff06 0x1101fff80000fff0

def z736 : W := mkw 0x36561fd8589afeaf 0x036561fd8589afea 0x901e1ff8000ffff6 0x1901e1ff8000ffff

def z737 : W := mkw 0x1616b4dadc3ebbe9 0x41616b4dadc3ebbe 0x7e1818607c7ffff8 0x57e1818607c7ffff

def z738 : W := mkw 0x0920000022400000 0x0092000002240000 0x6ff800007fff000b 0xe6ff800007fff000

def z739 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xb027ffffc47cffff 0xbb027ffffc47cfff

def z740 : W := mkw 0x4dbfe002776f0140 0x04dbfe002776f014 0x7fffe0007fff07cb 0xe7fffe0007fff07c

def z741 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6ffe60007fff0008 0xc6ffe60007fff000

def z742 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0xcfffffff800f000f 0xfcfffffff800f000

def z743 : W := mkw 0x1002a08adc3ebbe9 0x41002a08adc3ebbe 0x300000007c7c3fc8 0x0300000007c7c3fc

def z744 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe3e1ff8780ff8ff 0xffe3e1ff8780ff8f

def z745 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x9fffffff8000c0f7 0xf9fffffff8000c0f

def z746 : W := mkw 0x99eb4b2d580aa8a9 0x099eb4b2d580aa8a 0x71e1e387f80ff8f9 0x071e1e387f80ff8f

def z747 : W := mkw 0x0000008a80101bc0 0x40000008a80101bc 0xb027e79fc4703fcf 0xab027e79fc4703fc

def z748 : W := mkw 0x2b601f002ac0e40e 0x02b601f002ac0e40 0xcfe7ff9fbb80c007 0xfcfe7ff9fbb80c00

def z749 : W := mkw 0x849d407500000000 0x0849d40750000000 0x803fe5ff80000002 0x8803fe5ff8000000

def z750 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe1ffc7ff80ff8fe 0xffe1ffc7ff80ff8f

def z751 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fe018007ff0ff09 0xf7fe018007ff0ff0

def z752 : W := mkw 0x80c9ca2705854554 0x880c9ca270585455 0xd1d9fa67878fc7ff 0x7d1d9fa67878fc7f

def z753 : W := mkw 0x1002a08addbffffd 0xc1002a08addbffff 0x700000007ffffff8 0x0700000007ffffff

def z754 : W := mkw 0x0920000022400000 0x0092000002240000 0x4fe000003ff00001 0x44fe000003ff0000

def z755 : W := mkw 0xa9e9cba727d55756 0x8a9e9cba727d5575 0x01e1e38787f00701 0x001e1e38787f0070

def z756 : W := mkw 0xc49fe07fd52f09c0 0x4c49fe07fd52f09c 0x801fe07f800f00c2 0x0801fe07f800f00c

def z757 : W := mkw 0x4dbfe002776f0140 0x04dbfe002776f014 0xffffe79fffff07cf 0xeffffe79fffff07c

def z758 : W := mkw 0x0dfd4a2400000000 0x00dfd4a240000000 0x8fffffff80000007 0xf8fffffff8000000

def z759 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0xffe19f867ff0ff0f 0xfffe19f867ff0ff0

def z760 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fe007807ff0ff09 0x87fe007807ff0ff0

def z761 : W := mkw 0xcffd5f7533c34414 0x8cffd5f7533c3441 0xcfffffffbb83c037 0xfcfffffffbb83c03

def z762 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xde1e1c78380ff8f6 0x5de1e1c78380ff8f

def z763 : W := mkw 0x8fffffffc43c1bc0 0x48fffffffc43c1bc 0x3fd81860447c3fc8 0x53fd81860447c3fc

def z764 : W := mkw 0x8dbd417500000000 0x08dbd41750000000 0x803fe1ff80000002 0x0803fe1ff8000000

def z765 : W := mkw 0x4dbd400033430000 0x04dbd40003343000 0x6fd800007ff30008 0x46fd800007ff3000

def z766 : W := mkw 0x0920000022400000 0x0092000002240000 0x6fe007807ff0000d 0xe6fe007807ff0000

def z767 : W := mkw 0x2ba995a62f55b35a 0x82ba995a62f55b35 0xae3985e6787f38f2 0x8ae3985e6787f38f

def z768 : W := mkw 0x0002a08ae67c1bc0 0x40002a08ae67c1bc 0x700000007ffc3fc8 0x0700000007ffc3fc

def z769 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8fffffff800f00f7 0xf8fffffff800f00f

def z770 : W := mkw 0x8b601f7500000000 0x08b601f750000000 0x8fe7ffff80000007 0xf8fe7ffff8000000

def z771 : W := mkw 0x16163458582aa8a9 0x016163458582aa8a 0xfe3e7c78787ff8fe 0xffe3e7c78787ff8f

def z772 : W := mkw 0x1614b4d29c36b369 0x41614b4d29c36b36 0x4e39fbe7bc73c731 0x54e39fbe7bc73c73

def z773 : W := mkw 0x00c9aa2685a54554 0xc00c9aa2685a5455 0xd1d9fa67878fc7ff 0x7d1d9fa67878fc7f

def z774 : W := mkw 0x2b601fa42ad0f60e 0x02b601fa42ad0f60 0xffe01fe67ff0ff0d 0xfffe01fe67ff0ff0

def z775 : W := mkw 0x4dbf6000736b0000 0x04dbf6000736b000 0x6fd800007bf30000 0x46fd800007bf3000

def z776 : W := mkw 0x4dbfe026776f0150 0x84dbfe026776f015 0x6fffe0067fff000b 0xe6fffe0067fff000

def z777 : W := mkw 0x4dbfe002776f0140 0x04dbfe002776f014 0xfffffa667fffc7ff 0xffffffa667fffc7f

def z778 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x91d99a66078fc7f7 0x191d99a66078fc7f

def z779 : W := mkw 0xcffd5f7532420000 0x0cffd5f753242000 0x8fffffffb8000007 0xf8fffffffb800000

def z780 : W := mkw 0x8fbd555100000000 0x08fbd55510000000 0x8fffe79f80000007 0xe8fffe79f8000000

def z781 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x51d81a60078fc7fd 0x751d81a60078fc7f

def z782 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x70000000447ffff8 0x070000000447ffff

def z783 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0xeffffffff800000f 0xfeffffffff800000

def z784 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x6fe01f807ff0ff01 0xd6fe01f807ff0ff0

def z785 : W := mkw 0x0000000000000000 0x0000000000000000 0x9027e79f8400070f 0xa9027e79f8400070

def z786 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7ff81fe07ff3ff3d 0xf7ff81fe07ff3ff3

def z787 : W := mkw 0x0922000862480880 0x0092200086248088 0xffe604187ffc38cf 0xeffe604187ffc38c

def z788 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fe7ff807ff0ff0f 0xf7fe7ff807ff0ff0

def z789 : W := mkw 0x0920000022400000 0x0092000002240000 0x6fe7e0007ff0000b 0xe6fe7e0007ff0000

def z790 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe1e1e787c0fffff 0xffe1e1e787c0ffff

def z791 : W := mkw 0x1002a08acc3cbbe9 0x41002a08acc3cbbe 0x30000000447cfff8 0x030000000447cfff

def z792 : W := mkw 0x869d547500000000 0x0869d54750000000 0x8e3fffff80000007 0xf8e3fffff8000000

def z793 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1d99866078fc7fa 0x5d1d99866078fc7f

def z794 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1df9e7e078fc7ff 0xfd1df9e7e078fc7f

def z795 : W := mkw 0x06dd1e7400000000 0x006dd1e740000000 0x8fffffff80000007 0xf8fffffff8000000

def z796 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x2fe7e0007ffc000b 0xa2fe7e0007ffc000

def z797 : W := mkw 0x22401f880890fe8e 0x022401f880890fe8 0x90001f980000ffc4 0x190001f980000ffc

def z798 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x10000000000c3fc0 0x010000000000c3fc

def z799 : W := mkw 0x49a9e00027650000 0x049a9e0002765000 0x6ff9e0007fff000b 0xe6ff9e0007fff000

def z800 : W := mkw 0x8f34d55305854554 0x88f34d5530585455 0x5e266599878fc7f8 0x85e266599878fc7f

def z801 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1d99a66038fc7f6 0x5d1d99a66038fc7f

def z802 : W := mkw 0x0920000000000000 0x0092000000000000 0x8fe7e79f80000007 0xe8fe7e79f8000000

def z803 : W := mkw 0x0d34000022400000 0x00d3400002240000 0x6ffe00007ff0000b 0xe6ffe00007ff0000

def z804 : W := mkw 0x4dbfe008776f0880 0x04dbfe008776f088 0xffffe79fffff38cf 0xeffffe79fffff38c

def z805 : W := mkw 0xaffd5f7522c04406 0x0affd5f7522c0440 0x8fffffff83800007 0xf8fffffff8380000

def z806 : W := mkw 0x6002a08affffffce 0x46002a08affffffc 0x700000007fffffc8 0x0700000007fffffc

def z807 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0xffe01f9ffff0ff0d 0xfffe01f9ffff0ff0

def z808 : W := mkw 0x0922a08ae67c1bc0 0x40922a08ae67c1bc 0x7fe000007ffc3fc9 0xe7fe000007ffc3fc

def z809 : W := mkw 0x8920410100000000 0x0892041010000000 0x8027e79f80000007 0xa8027e79f8000000

def z810 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8ffffbff80000003 0x58ffffbff8000000

def z811 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xb027e79fc4703fc5 0x8b027e79fc4703fc

def z812 : W := mkw 0xcdbfe101776f0000 0x0cdbfe101776f000 0x6fffe181ffff000b 0xe6fffe181ffff000

def z813 : W := mkw 0x0089000000000000 0x0008900000000000 0x81ffe79f80000007 0xe81ffe79f8000000

def z814 : W := mkw 0x22401fa40890f60e 0x022401fa40890f60 0x90001fe60000ff04 0x190001fe60000ff0

def z815 : W := mkw 0x0920000022400000 0x0092000002240000 0xefe7e79ffff0000f 0xeefe7e79ffff0000

def z816 : W := mkw 0x4dbfe00af76f09c0 0x44dbfe00af76f09c 0xefffe79fffff00cf 0xeefffe79fffff00c

def z817 : W := mkw 0x0922a00ae66c09c0 0x40922a00ae66c09c 0xefe7e01ffffc00cb 0xeefe7e01ffffc00c

def z818 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x3027e79fc4703f0d 0xa3027e79fc4703f0

def z819 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0xd0181fe0000ffffe 0x7d0181fe0000ffff

def z820 : W := mkw 0x0920000022400000 0x0092000002240000 0x2fe000007ff00001 0x82fe000007ff0000

def z821 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x30000200447c3fcd 0x230000200447c3fc

def z822 : W := mkw 0x4dbf6000736b0000 0x04dbf6000736b000 0x6ffe60007ff30009 0xe6ffe60007ff3000

def z823 : W := mkw 0x00cb2aacc1b95e94 0xc00cb2aacc1b95e9 0x61fe7df9c3f3f830 0xd61fe7df9c3f3f83

def z824 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x3fe007807ff03f0d 0xa3fe007807ff03f0

def z825 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x0fe7ff9f80000005 0xf0fe7ff9f8000000

def z826 : W := mkw 0x9ffd5f751802a029 0x09ffd5f751802a02 0x8fffffffb8000007 0xf8fffffffb800000

def z827 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x9027ff9f8000ff07 0xb9027ff9f8000ff0

def z828 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe3e7df9f80ff8fe 0xffe3e7df9f80ff8f

def z829 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe1e1ffff80ff8fe 0xffe1e1ffff80ff8f

def z830 : W := mkw 0x8ffd5f750800a008 0x08ffd5f750800a00 0xfffffffff80ff8ff 0xffffffffff80ff8f

def z831 : W := mkw 0x0002a08ac53d1bd0 0xc0002a08ac53d1bd 0x30000000447f3ff8 0x030000000447f3ff

def z832 : W := mkw 0x96161559580aa8a9 0x096161559580aa8a 0xfe1e1df9f80ff8fe 0xffe1e1df9f80ff8f

def z833 : W := mkw 0x0000000000000000 0x0000000000000000 0x8027e39f80000003 0x08027e39f8000000

def z834 : W := mkw 0x0000000000000000 0x0000000000000000 0xb027e79fc000380f 0xab027e79fc000380

def z835 : W := mkw 0x00c90a2601814554 0x800c90a260181455 0xd1d81a66038fc7fe 0x7d1d81a66038fc7f

def z836 : W := mkw 0x2002a08aee7cbbca 0x42002a08aee7cbbc 0x300000007c7c3fc8 0x0300000007c7c3fc

def z837 : W := mkw 0x22401fae8890ffde 0xc22401fae8890ffd 0x90001fff8000fff4 0x190001fff8000fff

def z838 : W := mkw 0x4d366000726a0000 0x04d366000726a000 0x6fe660007bf00000 0xc6fe660007bf0000

def z839 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8e3fffff80000006 0x98e3fffff8000000

def z840 : W := mkw 0x049fa000552f0000 0x0049fa000552f000 0x6fffe0007fff000b 0xe6fffe0007fff000

def z841 : W := mkw 0x0200140000000000 0x0020014000000000 0x8e27ff9f80000007 0xf8e27ff9f8000000

def z842 : W := mkw 0x29600b8022d05606 0x029600b8022d0560 0x7fe007807ff03f0d 0xe7fe007807ff03f0

def z843 : W := mkw 0x4dbfe00af76f09c0 0x44dbfe00af76f09c 0xffffe21fffff07cf 0xeffffe21fffff07c

def z844 : W := mkw 0x40c9ea2605a54554 0x840c9ea2605a5455 0xd1d9fa66078fc7ff 0x7d1d9fa66078fc7f

def z845 : W := mkw 0x0089800205854554 0x8008980020585455 0xd1d99860078fc7ff 0x7d1d99860078fc7f

def z846 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x2fe01f807ff03f05 0xf2fe01f807ff03f0

def z847 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8fdfffff80000006 0x58fdfffff8000000

def z848 : W := mkw 0x4d34400032420000 0x04d3440003242000 0x6fe000007ff00009 0xe6fe000007ff0000

def z849 : W := mkw 0x32401fd00890f62f 0x032401fd00890f62 0x10001fe00000ff34 0x110001fe00000ff3

def z850 : W := mkw 0x84dd4a7500000000 0x084dd4a750000000 0x81ffffff80000007 0xf81ffffff8000000

def z851 : W := mkw 0x020014000800a008 0x0020014000800a00 0xfe27ff9ff800f80f 0xffe27ff9ff800f80

def z852 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xffde1c787f8ff8ff 0xfffde1c787f8ff8f

def z853 : W := mkw 0x49a9400023410000 0x049a940002341000 0x6fe000007ff00009 0xe6fe000007ff0000

def z854 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1f9fbe7878fc7ff 0x7d1f9fbe7878fc7f

def z855 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xb03fe7ffc47f3fff 0xab03fe7ffc47f3ff

def z856 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fffe0007ff30001 0xc6fffe0007ff3000

def z857 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x00001b800000c700 0x100001b800000c70

def z858 : W := mkw 0x4d36a000776f0000 0x04d36a000776f000 0x6ffe00007fff000b 0xe6ffe00007fff000

def z859 : W := mkw 0x3b601fd02ad0f62f 0x03b601fd02ad0f62 0x7fe01fe07ff0ff3d 0xf7fe01fe07ff0ff3

def z860 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe3e1c787c7ff8ff 0xffe3e1c787c7ff8f

def z861 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x100018000000ff00 0x1100018000000ff0

def z862 : W := mkw 0x8ffd5f7500804404 0x08ffd5f750080440 0xdfffffff878fc7ff 0xfdfffffff878fc7f

def z863 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1d81a66078fc7fc 0x5d1d81a66078fc7f

def z864 : W := mkw 0x4dbfe008776f0880 0x04dbfe008776f088 0x7fffe0007fff38cb 0xe7fffe0007fff38c

def z865 : W := mkw 0x49abe000776f0000 0x049abe000776f000 0x6fe1e0007fff0009 0xe6fe1e0007fff000

def z866 : W := mkw 0x4dbfe002776f0140 0x04dbfe002776f014 0xefffe0067fff00cb 0xeefffe0067fff00c

def z867 : W := mkw 0x0dbf8000774f0000 0x00dbf8000774f000 0x6fff80007fff000b 0xe6fff80007fff000

def z868 : W := mkw 0x0002208ac0381bc0 0x40002208ac0381bc 0xb027e79fc0703fc7 0xab027e79fc0703fc

def z869 : W := mkw 0x4002a08ad53f1bc0 0x44002a08ad53f1bc 0x30000000447f3fc8 0x030000000447f3fc

def z870 : W := mkw 0x8dfd4b7500000000 0x08dfd4b750000000 0x81fffbff80000007 0x781fffbff8000000

def z871 : W := mkw 0x00022088c0381a80 0x400022088c0381a8 0xb027e79fc4703f0f 0xab027e79fc4703f0

def z872 : W := mkw 0x84dd4b7500000000 0x084dd4b750000000 0x801fe3ff80000002 0x0801fe3ff8000000

def z873 : W := mkw 0x5dbfe07e776f09f1 0x85dbfe07e776f09f 0xefffe07e7fff00fb 0xeefffe07e7fff00f

def z874 : W := mkw 0x0d34400000000000 0x00d3440000000000 0x8e27e79f80000007 0xa8e27e79f8000000

def z875 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xfe27e79ffc7c3fcf 0xefe27e79ffc7c3fc

def z876 : W := mkw 0x2b2015802a50b20a 0x02b2015802a50b20 0x7fe007807ff03f0d 0xe7fe007807ff03f0

def z877 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x0000078000003f00 0x00000078000003f0

def z878 : W := mkw 0x0002a08ac53d1bc0 0x40002a08ac53d1bc 0x7000000047ff3fc8 0x07000000047ff3fc

def z879 : W := mkw 0x049d400000000000 0x0049d40000000000 0x803fe79f80000007 0xa803fe79f8000000

def z880 : W := mkw 0x4dbfe00a776f09c0 0x04dbfe00a776f09c 0xffffe61e7fff3fcf 0xeffffe61e7fff3fc

def z881 : W := mkw 0x0d34400022400000 0x00d3440002240000 0x6fe660007ff00009 0xe6fe660007ff0000

def z882 : W := mkw 0xcffd5f7511030000 0x0cffd5f751103000 0x8fffffff80030007 0xf8fffffff8003000

def z883 : W := mkw 0xcdbfe051776f0000 0x0cdbfe051776f000 0x6fffe019ffff000b 0xe6fffe019ffff000

def z884 : W := mkw 0x5dbfe058776f08a1 0x05dbfe058776f08a 0x6fffe0187fff000b 0xe6fffe0187fff000

def z885 : W := mkw 0x4002a08af67e1bc0 0x44002a08af67e1bc 0x300000007c7c3fc8 0x0300000007c7c3fc

def z886 : W := mkw 0xeffd5f753bc3e40e 0x0effd5f753bc3e40 0x4fd818603b83c000 0x54fd818603b83c00

def z887 : W := mkw 0x8f34555100000000 0x08f3455510000000 0x0e27e79f80000001 0x80e27e79f8000000

def z888 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0xefffe2067fff000f 0xeefffe2067fff000

def z889 : W := mkw 0x0000000000000000 0x0000000000000000 0x9027e79f800c00cf 0xa9027e79f800c00c

def z890 : W := mkw 0x161414581802a8a9 0x0161414581802a8a 0xde181c78380ff8fe 0x7de181c78380ff8f

def z891 : W := mkw 0x849d407500000000 0x0849d40750000000 0x801fe7ff80000006 0x0801fe7ff8000000

def z892 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x7fffe0007fffc0fb 0xe7fffe0007fffc0f

def z893 : W := mkw 0x00408a0205854554 0x800408a020585455 0xd1d81a60078fc7ff 0x7d1d81a60078fc7f

def z894 : W := mkw 0x161414501802a029 0x0161414501802a02 0xfe181c60780ff8fe 0xffe181c60780ff8f

def z895 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xf1f99a6647ffc7ff 0xff1f99a6647ffc7f

def z896 : W := mkw 0x4d366000726a0000 0x04d366000726a000 0x2fe660007ff00001 0x82fe660007ff0000

def z897 : W := mkw 0x8ffd5f7500804404 0x08ffd5f750080440 0x9fffffff8000c707 0xf9fffffff8000c70

def z898 : W := mkw 0x0be91f2400000000 0x00be91f240000000 0x8fffffff80000007 0xf8fffffff8000000

def z899 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0xffe61f987ff0ff0f 0xfffe61f987ff0ff0

def z900 : W := mkw 0x4dbd408ab3531bc0 0x44dbd408ab3531bc 0xdfd8079fbb833fc4 0x4dfd8079fbb833fc

def z901 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xf027ff9fc47cffcf 0xff027ff9fc47cffc

def z902 : W := mkw 0x4dbde00037670000 0x04dbde0003767000 0x4ff9e0003fff000b 0x64ff9e0003fff000

def z903 : W := mkw 0xcdbfe075776f0000 0x0cdbfe075776f000 0x6fffe0607fff000b 0xe6fffe0607fff000

def z904 : W := mkw 0x2002a08ae6fc5fc6 0x42002a08ae6fc5fc 0x3000000047fc3fc8 0x03000000047fc3fc

def z905 : W := mkw 0x8dfd4b7500000000 0x08dfd4b750000000 0x01e7e39f80000001 0x001e7e39f8000000

def z906 : W := mkw 0x9ffd5f751983e43d 0x89ffd5f751983e43 0xcfffffffbb83c037 0xfcfffffffbb83c03

def z907 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fe67f99fff0ff0d 0xf7fe67f99fff0ff0

def z908 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x6fe007807ff03f09 0xe6fe007807ff03f0

def z909 : W := mkw 0x0000000000000000 0x0000000000000000 0xa027e79fc470000f 0xaa027e79fc470000

def z910 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x3027e79fc47c3fc9 0x83027e79fc47c3fc

def z911 : W := mkw 0x0614145000000000 0x0061414500000000 0x8e27e79f80000007 0xa8e27e79f8000000

def z912 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8fffe7ff80000003 0x88fffe7ff8000000

def z913 : W := mkw 0x4dbd600033630000 0x04dbd60003363000 0x4ff860003bf30000 0x44ff860003bf3000

def z914 : W := mkw 0x4dbf6000736b0000 0x04dbf6000736b000 0x2fe660007bf00000 0x82fe660007bf0000

def z915 : W := mkw 0xeffd5f753bc3e40e 0x0effd5f753bc3e40 0xcfffffffbb83c007 0xfcfffffffbb83c00

def z916 : W := mkw 0x8fbd557500000000 0x08fbd55750000000 0x8e3fe7ff80000007 0xa8e3fe7ff8000000

def z917 : W := mkw 0x00c98a0005854404 0x000c98a000585440 0xd1d99a60078fc7ff 0x7d1d99a60078fc7f

def z918 : W := mkw 0xcdbfe025776f0000 0x0cdbfe025776f000 0x6fffe007ffff000b 0xe6fffe007ffff000

def z919 : W := mkw 0x22401fa60890f75e 0x822401fa60890f75 0x10001f860000ff04 0x110001f860000ff0

def z920 : W := mkw 0x09600b0000000000 0x009600b000000000 0x81e7e79f80000007 0xa81e7e79f8000000

def z921 : W := mkw 0x8ffd5f750800a008 0x08ffd5f750800a00 0xaffffffff8003807 0xfaffffffff800380

def z922 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0x51d99860078fc7fb 0x751d99860078fc7f

def z923 : W := mkw 0x292000802ad0f60e 0x0292000802ad0f60 0x7fc000007ff0ff08 0x47fc000007ff0ff0

def z924 : W := mkw 0x86541f7500000000 0x086541f750000000 0x8e3fffff80000007 0xf8e3fffff8000000

def z925 : W := mkw 0x8200155100000000 0x0820015510000000 0x8027e79f80000007 0xa8027e79f8000000

def z926 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0xafffffffc470000f 0xfafffffffc470000

def z927 : W := mkw 0x0042aa8ac4bc5fc4 0x40042aa8ac4bc5fc 0x71c01a0047fcffcd 0x771c01a0047fcffc

def z928 : W := mkw 0x0000000000000000 0x0000000000000000 0x803fffff80000007 0xf803fffff8000000

def z929 : W := mkw 0x4dbf6000726a0000 0x04dbf6000726a000 0x6fffe0007ff0000b 0xe6fffe0007ff0000

def z930 : W := mkw 0x0920000022400000 0x0092000002240000 0x6fc000007ff00008 0x46fc000007ff0000

def z931 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0xcfffffff8780000f 0xfcfffffff8780000

def z932 : W := mkw 0x69e9eba627f55756 0x869e9eba627f5575 0x01e1e38607f00701 0x001e1e38607f0070

def z933 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8ffffdff80000002 0xd8ffffdff8000000

def z934 : W := mkw 0x8fbd557500000000 0x08fbd55750000000 0x8fffe5ff80000003 0xe8fffe5ff8000000

def z935 : W := mkw 0x22409f820c94f74e 0x022409f820c94f74 0x90019f86040cffcf 0x390019f86040cffc

def z936 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xbe1e1c78780ff8f6 0x9be1e1c78780ff8f

def z937 : W := mkw 0xa49d40f52ad0f60e 0x0a49d40f52ad0f60 0xf01fe07ffff0ff0a 0x0f01fe07ffff0ff0

def z938 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0xffffe0007fff00cf 0xeffffe0007fff00c

def z939 : W := mkw 0x4dbfe002f76f0140 0x44dbfe002f76f014 0x6fffe007ffff000b 0xe6fffe007ffff000

def z940 : W := mkw 0x8fbd557500000000 0x08fbd55750000000 0x8e3ffdff80000006 0xf8e3ffdff8000000

def z941 : W := mkw 0x4dbfe024776f0000 0x04dbfe024776f000 0xefffe0667fff000b 0xeefffe0667fff000

def z942 : W := mkw 0x0000000000000000 0x0000000000000000 0x0027e79f80000001 0x80027e79f8000000

def z943 : W := mkw 0x8dfd4b7500000000 0x08dfd4b750000000 0x81ffe7ff80000007 0xa81ffe7ff8000000

def z944 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x10001f800400ff0d 0x310001f800400ff0

def z945 : W := mkw 0x09a9000023410000 0x009a900002341000 0x6ff800007ff30009 0xe6ff800007ff3000

def z946 : W := mkw 0xbf3655d97a5abaab 0x0bf3655d97a5abaa 0x2e266599f8703800 0x82e266599f870380

def z947 : W := mkw 0x09aba000676d0000 0x009aba000676d000 0x6fffe0007fff000b 0xe6fffe0007fff000

def z948 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe1e1878780ff8fa 0x5fe1e1878780ff8f

def z949 : W := mkw 0x449fe00ad52f09c0 0x4449fe00ad52f09c 0x001fe000000f00c2 0x0001fe000000f00c

def z950 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xb03fffffc47c3fcf 0xfb03fffffc47c3fc

def z951 : W := mkw 0x8dbd407522400000 0x08dbd40752240000 0xefffe07ffff0000b 0xeefffe07ffff0000

def z952 : W := mkw 0x8ffd5f7501814414 0x88ffd5f750181441 0xdfffffff838fc0ff 0xfdfffffff838fc0f

def z953 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fe7e0007fff0009 0x86fe7e0007fff000

def z954 : W := mkw 0x22c99fa60d95f75e 0x822c99fa60d95f75 0x90199fe6000ffff6 0x190199fe6000ffff

def z955 : W := mkw 0x4d766a2672ea4554 0x84d766a2672ea455 0xbe267a667870c7f4 0x9be267a667870c7f

def z956 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x30001f804000ff0c 0xb30001f804000ff0

def z957 : W := mkw 0x0920a00026640000 0x00920a0002664000 0x6fe1e0007ff00009 0xe6fe1e0007ff0000

def z958 : W := mkw 0x0089002400000000 0x0008900240000000 0x803fe7ff80000007 0xa803fe7ff8000000

def z959 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0x7e1e1c78780ff8f8 0xd7e1e1c78780ff8f

def z960 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x30200000447c3fc9 0xa30200000447c3fc

def z961 : W := mkw 0x4dbfe002776f0150 0x84dbfe002776f015 0x6fffe0007fff00fb 0xe6fffe0007fff00f

def z962 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fe01d807ff0ff08 0xd7fe01d807ff0ff0

def z963 : W := mkw 0x0f741f5000000000 0x00f741f500000000 0x8fffffff80000007 0xf8fffffff8000000

def z964 : W := mkw 0x149fa07ed52f09f1 0xc149fa07ed52f09f 0x801fe07f800f00f2 0x0801fe07f800f00f

def z965 : W := mkw 0x00400a0000000000 0x000400a000000000 0x81e7ff9f80000007 0xf81e7ff9f8000000

def z966 : W := mkw 0xcdbfe077776f0150 0x8cdbfe077776f015 0xefffe07fffff00fb 0xeefffe07fffff00f

def z967 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x9fffffff800c00cf 0xf9fffffff800c00c

def z968 : W := mkw 0x2242bf8accbcffce 0x42242bf8accbcffc 0x9007ff9f800cffc6 0x19007ff9f800cffc

def z969 : W := mkw 0x0b20150000000000 0x00b2015000000000 0x8e27e79f80000007 0xa8e27e79f8000000

def z970 : W := mkw 0x29600a802ad0f60e 0x029600a802ad0f60 0x7fe01a007ff0ff0d 0xf7fe01a007ff0ff0

def z971 : W := mkw 0x8ffd5f750880e40c 0x08ffd5f750880e40 0xffffffffff80ff0f 0xfffffffffff80ff0

def z972 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7ff81f807fffff0f 0xf7ff81f807fffff0

def z973 : W := mkw 0x49aba000776f0000 0x049aba000776f000 0x6ff980007fff000b 0xe6ff980007fff000

def z974 : W := mkw 0x00cbaaaec5bd5fd4 0xc00cbaaaec5bd5fd 0x71d8186047fffff8 0x571d8186047fffff

def z975 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xf03fe79fc47f3fcf 0xef03fe79fc47f3fc

def z976 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fd980007fff000b 0x66fd980007fff000

def z977 : W := mkw 0x9ffd5f7510020021 0x09ffd5f751002002 0x8fffffff80030037 0xf8fffffff8003003

def z978 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xffd99a667f8fc7ff 0xfffd99a667f8fc7f

def z979 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x81ffffff80000007 0x181ffffff8000000

def z980 : W := mkw 0xbffd5f753ac2e42f 0x0bffd5f753ac2e42 0x4fd818603b83c030 0x54fd818603b83c03

def z981 : W := mkw 0x5dbfe008776f08a1 0x05dbfe008776f08a 0x6fffe0007fff00fb 0xe6fffe0007fff00f

def z982 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x90001fe00000fff4 0x190001fe00000fff

def z983 : W := mkw 0x86dd5f7500000000 0x086dd5f750000000 0x8e1fffff80000006 0xf8e1fffff8000000

def z984 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0x7e1e1860780ff8fa 0xf7e1e1860780ff8f

def z985 : W := mkw 0xa6dd5ff50890f60e 0x0a6dd5ff50890f60 0x901fffff8000ff06 0x1901fffff8000ff0

def z986 : W := mkw 0x04160008500a0880 0x004160008500a088 0xfe1e1c78780ff8fe 0xffe1e1c78780ff8f

def z987 : W := mkw 0x4dbfe050776f0000 0x04dbfe050776f000 0xefffe0787fff000b 0xeefffe0787fff000

def z988 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0xefffe4187fff000f 0xeefffe4187fff000

def z989 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fdfe0007fff000a 0x46fdfe0007fff000

def z990 : W := mkw 0x4920a00027650000 0x04920a0002765000 0x6fe000007ff00009 0xe6fe000007ff0000

def z991 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe181c78780ff8fc 0x5fe181c78780ff8f

def z992 : W := mkw 0x2b62bf0aeeecedce 0x42b62bf0aeeecedc 0xcfc7f81fbb8cc0c2 0x5cfc7f81fbb8cc0c

def z993 : W := mkw 0x5dbfe05af76f09e1 0x45dbfe05af76f09e 0xefffe07fffff00fb 0xeefffe07fffff00f

def z994 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0xfff81fe07ff0ff0f 0xffff81fe07ff0ff0

def z995 : W := mkw 0xcffd5f7523410000 0x0cffd5f752341000 0x8fffffff83800007 0xf8fffffff8380000

def z996 : W := mkw 0x00c90a2401814414 0x800c90a240181441 0xd1d81a60078fc7ff 0x7d1d81a60078fc7f

def z997 : W := mkw 0x14160008580aa8a9 0x014160008580aa8a 0xfe1e1860780ff8fe 0xffe1e1860780ff8f

def z998 : W := mkw 0xbffd5f753ac2e42f 0x0bffd5f753ac2e42 0xcfffffffbb83c037 0xfcfffffffbb83c03

def z999 : W := mkw 0x0d360000724a0000 0x00d360000724a000 0x6fe600007ff00009 0xe6fe600007ff0000

def z1000 : W := mkw 0x0002a08ad43e1bc0 0x40002a08ad43e1bc 0xf027e79ffc7f3fcf 0xaf027e79ffc7f3fc

def z1001 : W := mkw 0x061414500800a008 0x0061414500800a00 0xfe1e1c78780ff8fe 0xffe1e1c78780ff8f

def z1002 : W := mkw 0x89e94b2500000000 0x089e94b250000000 0x01e7e79f80000001 0x801e7e79f8000000

def z1003 : W := mkw 0x22421f884898fe8e 0x022421f884898fe8 0xb0061f98400cffce 0xbb0061f98400cffc

def z1004 : W := mkw 0x2b2014802ad0f60e 0x02b2014802ad0f60 0x7fe01c007ff0ff0d 0xf7fe01c007ff0ff0

def z1005 : W := mkw 0x0002a08acc3cbbc8 0x40002a08acc3cbbc 0x700000007c7cffc8 0x0700000007c7cffc

def z1006 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x9027e79f847c3fc7 0x09027e79f847c3fc

def z1007 : W := mkw 0x0922a000666c0000 0x00922a000666c000 0x6fe000007ffc0009 0xe6fe000007ffc000

def z1008 : W := mkw 0x56167458582aa8a9 0x056167458582aa8a 0xfe1e7c78780ff8fe 0xffe1e7c78780ff8f

def z1009 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fc01c007ff0ff0c 0xf7fc01c007ff0ff0

def z1010 : W := mkw 0x1002a08ad43e1be1 0x41002a08ad43e1be 0xb027e79fc47f3fff 0xab027e79fc47f3ff

def z1011 : W := mkw 0x0920000022400000 0x0092000002240000 0x7fe004007ff0380d 0xe7fe004007ff0380

def z1012 : W := mkw 0x0b2014802a50b208 0x00b2014802a50b20 0x7fe01f807ff0ff0d 0xf7fe01f807ff0ff0

def z1013 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xf1d99e66478fffff 0xff1d99e66478ffff

def z1014 : W := mkw 0x161414501802a029 0x0161414501802a02 0xce3fffffb803c037 0xfce3fffffb803c03

def z1015 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x7fffe4007fff380f 0xe7fffe4007fff380

def z1016 : W := mkw 0xcdbfe075776f0000 0x0cdbfe075776f000 0xefffe7ffffff000f 0xeefffe7ffffff000

def z1017 : W := mkw 0x4dbfe024776f0010 0x84dbfe024776f001 0x6fffe0607fff003b 0xe6fffe0607fff003

def z1018 : W := mkw 0x2b2015802ad0f60e 0x02b2015802ad0f60 0x7fe005807ff0ff09 0xe7fe005807ff0ff0

def z1019 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1fffa66078fc7ff 0xfd1fffa66078fc7f

def z1020 : W := mkw 0x09a9000022400000 0x009a900002240000 0x6ff980007ff0000b 0xe6ff980007ff0000

def z1021 : W := mkw 0x09220000724a0000 0x009220000724a000 0x6fe000007fff0009 0xe6fe000007fff000

def z1022 : W := mkw 0x4d366000726a0000 0x04d366000726a000 0x6ffe60007fff000b 0xe6ffe60007fff000

def z1023 : W := mkw 0x4dbfe00af76f09c0 0x44dbfe00af76f09c 0x6fffe0007fff00cb 0xe6fffe0007fff00c

def z1024 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0xefffe01fffff000b 0xeefffe01fffff000

def z1025 : W := mkw 0x22401e802ad0f60e 0x022401e802ad0f60 0x7fc01e007ff0ff0d 0xf7fc01e007ff0ff0

def z1026 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fe01b807ff0ff09 0x57fe01b807ff0ff0

def z1027 : W := mkw 0x9ffd5f750800a029 0x09ffd5f750800a02 0x8fffffff8000c037 0xf8fffffff8000c03

def z1028 : W := mkw 0x4922a000776f0000 0x04922a000776f000 0x6fc000007fff0008 0x46fc000007fff000

def z1029 : W := mkw 0x4dbfe002776f0140 0x04dbfe002776f014 0x6fffe2067fff070b 0xe6fffe2067fff070

def z1030 : W := mkw 0xaffd5f752ac0e40e 0x0affd5f752ac0e40 0xeffffffffff0c00f 0xfeffffffffff0c00

def z1031 : W := mkw 0x549fe07e552f09f1 0x8549fe07e552f09f 0x801fe07e000f00f2 0x0801fe07e000f00f

def z1032 : W := mkw 0xddbfe07d776f08a1 0x0ddbfe07d776f08a 0xefffe07fffff00fb 0xeefffe07fffff00f

def z1033 : W := mkw 0xab601fd12ad0f60e 0x0ab601fd12ad0f60 0x7fe01f99fff0ff0d 0xf7fe01f99fff0ff0

def z1034 : W := mkw 0x0202b48acc3cbbc8 0x40202b48acc3cbbc 0x7e001c007c7cffcc 0xf7e001c007c7cffc

def z1035 : W := mkw 0x8f34555100000000 0x08f3455510000000 0x8e3fffff80000007 0xf8e3fffff8000000

def z1036 : W := mkw 0x32401ffe0890ffff 0x832401ffe0890fff 0x90001ffe0000fff4 0x190001ffe0000fff

def z1037 : W := mkw 0x4dbf6000736b0000 0x04dbf6000736b000 0x6ffe60007bff000a 0xe6ffe60007bff000

def z1038 : W := mkw 0x82401f7500000000 0x082401f750000000 0x8007ffff80000006 0x18007ffff8000000

def z1039 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x00001d800000f800 0x100001d800000f80

def z1040 : W := mkw 0x0920008022501200 0x0092000802250120 0x7fe000007ff03f09 0xe7fe000007ff03f0

def z1041 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xa027e79fc47c3fc3 0x8a027e79fc47c3fc

def z1042 : W := mkw 0x32401fd80890feaf 0x032401fd80890fea 0x10001f980000ff04 0x110001f980000ff0

def z1043 : W := mkw 0xab601ff52ad0f60e 0x0ab601ff52ad0f60 0x7fe01fe07ff0ff0d 0xf7fe01fe07ff0ff0

def z1044 : W := mkw 0xa2401fd10890f60e 0x0a2401fd10890f60 0x10001f998000ff04 0x110001f998000ff0

def z1045 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x4fffe0003fff0003 0x44fffe0003fff000

def z1046 : W := mkw 0x29600b802ad0f60e 0x029600b802ad0f60 0x7fe003807ff0ff09 0xe7fe003807ff0ff0

def z1047 : W := mkw 0x2b62bf8aeefcffce 0x42b62bf8aeefcffc 0x7fc018007ffcffc8 0x57fc018007ffcffc

def z1048 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xa027e79fc4703f07 0xaa027e79fc4703f0

def z1049 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe181860780ff8fe 0x7fe181860780ff8f

def z1050 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fffe387ffff000b 0xe6fffe387ffff000

def z1051 : W := mkw 0x4002a08af7ff5fd4 0xc4002a08af7ff5fd 0x700000007ffffff8 0x0700000007ffffff

def z1052 : W := mkw 0x4dbfe008776f0880 0x04dbfe008776f088 0xfffffc787ffff8ff 0xffffffc787ffff8f

def z1053 : W := mkw 0xab601fa52ad0f60e 0x0ab601fa52ad0f60 0x7fe01f87fff0ff0d 0xf7fe01f87fff0ff0

def z1054 : W := mkw 0x4922a000776f0000 0x04922a000776f000 0x6fe7e0007fff000b 0xe6fe7e0007fff000

def z1055 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1dffa7f878fc7ff 0x7d1dffa7f878fc7f

def z1056 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x2000000044703f00 0x02000000044703f0

def z1057 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xf1e7e79fc7fc3fcf 0xef1e7e79fc7fc3fc

def z1058 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xb027e79fc07c3fc6 0x8b027e79fc07c3fc

def z1059 : W := mkw 0x8dbd407500000000 0x08dbd40750000000 0x8fffe7ff80000007 0xe8fffe7ff8000000

def z1060 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fffe0007bff0002 0xc6fffe0007bff000

def z1061 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8fe7e79f80000007 0xa8fe7e79f8000000

def z1062 : W := mkw 0x8414405100000000 0x0841440510000000 0x8027e79f80000007 0xa8027e79f8000000

def z1063 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fffe7807fff000f 0xe6fffe7807fff000

def z1064 : W := mkw 0x4dbdc00037470000 0x04dbdc0003747000 0x6ff980007fff000b 0xe6ff980007fff000

def z1065 : W := mkw 0x8dfd4b2500000000 0x08dfd4b250000000 0x8fffe79f80000007 0xe8fffe79f8000000

def z1066 : W := mkw 0x5dbfe058776f08a1 0x05dbfe058776f08a 0xffffe4787fff38ff 0xeffffe4787fff38f

def z1067 : W := mkw 0xcdbfe07ff76f09c0 0x4cdbfe07ff76f09c 0xefffe07fffff00cb 0xeefffe07fffff00c

def z1068 : W := mkw 0x0922200062680000 0x0092220006268000 0x6fe660007ff00009 0xe6fe660007ff0000

def z1069 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0xefffe0607fff00fb 0xeefffe0607fff00f

def z1070 : W := mkw 0x09a9400022400000 0x009a940002240000 0x6fe1e0007ff00009 0xe6fe1e0007ff0000

def z1071 : W := mkw 0x549fe05ad52f09e1 0x4549fe05ad52f09e 0x801fe07f800f00f2 0x0801fe07f800f00f

def z1072 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xb0000000447c3fce 0x2b0000000447c3fc

def z1073 : W := mkw 0x12021408580aa8a9 0x012021408580aa8a 0xfe181c60780ff8fe 0xffe181c60780ff8f

def z1074 : W := mkw 0x8be95f7500000000 0x08be95f750000000 0x81e7ffff80000007 0xb81e7ffff8000000

def z1075 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xf0181860447ffffe 0x7f0181860447ffff

def z1076 : W := mkw 0x96165459580aa8a9 0x096165459580aa8a 0xfe1e7c79f80ff8fe 0xffe1e7c79f80ff8f

def z1077 : W := mkw 0x0d34000032420000 0x00d3400003242000 0x6ff800007ff30009 0xe6ff800007ff3000

def z1078 : W := mkw 0x00400a2400000000 0x000400a240000000 0x8027ffff80000007 0xb8027ffff8000000

def z1079 : W := mkw 0x7f3675d87a7abaab 0x07f3675d87a7abaa 0x2e26659878703800 0x82e2665987870380

def z1080 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xc1d99a66078fc7f3 0x5c1d99a66078fc7f

def z1081 : W := mkw 0x89e94b2500000000 0x089e94b250000000 0x81e7e39f80000003 0x081e7e39f8000000

def z1082 : W := mkw 0x0d36a000766e0000 0x00d36a000766e000 0x6fffe0007fff000b 0xe6fffe0007fff000

def z1083 : W := mkw 0x89e94b2500000000 0x089e94b250000000 0x81ffffff80000007 0xf81ffffff8000000

def z1084 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6ff9e0007fff0009 0x46ff9e0007fff000

def z1085 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x10201f800000ff05 0xb10201f800000ff0

def z1086 : W := mkw 0x8ffd5f750800a008 0x08ffd5f750800a00 0xcfffffffb800c007 0xfcfffffffb800c00

def z1087 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x7fffe2007fff070f 0xe7fffe2007fff070

def z1088 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1d99fff878fc7ff 0x7d1d99fff878fc7f

def z1089 : W := mkw 0x86dd5f7500000000 0x086dd5f750000000 0x803fffff80000007 0xb803fffff8000000

def z1090 : W := mkw 0x12401efe8890fffd 0xc12401efe8890fff 0x90001fff8000fff4 0x190001fff8000fff

def z1091 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1d81860078fc7fe 0x7d1d81860078fc7f

def z1092 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x30000400447c3fcc 0xa30000400447c3fc

def z1093 : W := mkw 0x00c98a2605854554 0x800c98a260585455 0xd1f99fe6078fc7ff 0xfd1f99fe6078fc7f

def z1094 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x2fffe0007fff0003 0x82fffe0007fff000

def z1095 : W := mkw 0x1d360058724a08a1 0x01d360058724a08a 0xeffe00787fff00fb 0xeeffe00787fff00f

def z1096 : W := mkw 0x8ffd5f752a40a008 0x08ffd5f752a40a00 0xfffffffffff0f80f 0xffffffffffff0f80

def z1097 : W := mkw 0x0920800027450000 0x0092080002745000 0x6fe000007fff0009 0xe6fe000007fff000

def z1098 : W := mkw 0x8ffd5f7510020000 0x08ffd5f751002000 0xcfffffffb8030007 0xfcfffffffb803000

def z1099 : W := mkw 0x22401f8a8890ffce 0x422401f8a8890ffc 0x10001f800000ffc4 0x110001f800000ffc

def z1100 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x8fe7ffff80000005 0x98fe7ffff8000000

def z1101 : W := mkw 0x0000000000000000 0x0000000000000000 0x8027e59f80000002 0x88027e59f8000000

def z1102 : W := mkw 0x00408a0204844544 0x000408a020484454 0xd1d99a66078fc7ff 0x7d1d99a66078fc7f

def z1103 : W := mkw 0x0002a08ac53d1bc0 0x40002a08ac53d1bc 0xf027e79fc7ff3fcf 0xaf027e79fc7ff3fc

def z1104 : W := mkw 0x2002a08aeffdffde 0xc2002a08aeffdffd 0x700000007ffffff8 0x0700000007ffffff

def z1105 : W := mkw 0x020214084808a888 0x0020214084808a88 0xfe1e1c78780ff8fe 0xffe1e1c78780ff8f

def z1106 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x2027e79fc47c3f0b 0xa2027e79fc47c3f0

def z1107 : W := mkw 0x8ffd5f7522400000 0x08ffd5f752240000 0xaffffffff8700007 0xfaffffffff870000

def z1108 : W := mkw 0x8dfd4b7500000000 0x08dfd4b750000000 0x8fffe3ff80000003 0xe8fffe3ff8000000

def z1109 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0xbfffffffc000380f 0xfbfffffffc000380

def z1110 : W := mkw 0x4dbd400033430000 0x04dbd40003343000 0xcfffe79fbb830007 0xecfffe79fbb83000

def z1111 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fe01f807ffffffd 0xf7fe01f807ffffff

def z1112 : W := mkw 0x00400a0000804404 0x000400a000080440 0xd1e7ff9f8780c70f 0xfd1e7ff9f8780c70

def z1113 : W := mkw 0x0920000022400000 0x0092000002240000 0x6fe000007bf00000 0xc6fe000007bf0000

def z1114 : W := mkw 0x8ffd5f7522400000 0x08ffd5f752240000 0xcfffffffbb800007 0xfcfffffffbb80000

def z1115 : W := mkw 0x49e9eaa6a7f55754 0xc49e9eaa6a7f5575 0x01e1e38787f00701 0x001e1e38787f0070

def z1116 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x20000000407c38c0 0x020000000407c38c

def z1117 : W := mkw 0x2002a08accbcffce 0x42002a08accbcffc 0x30000000447cffc8 0x030000000447cffc

def z1118 : W := mkw 0x9ffd5f751802a029 0x09ffd5f751802a02 0xdfffffffb80fc0ff 0xfdfffffffb80fc0f

def z1119 : W := mkw 0x4dbfe026776f0150 0x84dbfe026776f015 0xfffff8667fffc0ff 0xffffff8667fffc0f

def z1120 : W := mkw 0x80c98b2705854554 0x880c98b270585455 0xd1d99be7878fc7ff 0x7d1d99be7878fc7f

def z1121 : W := mkw 0x8f34555100000000 0x08f3455510000000 0x8e27e59f80000002 0x88e27e59f8000000

def z1122 : W := mkw 0x4dbd400033430000 0x04dbd40003343000 0x4ff800003ff30001 0x44ff800003ff3000

def z1123 : W := mkw 0xa2401ff50890f60e 0x0a2401ff50890f60 0x10001fe00000ff04 0x110001fe00000ff0

def z1124 : W := mkw 0x5f3674d8fa7abaa9 0x45f3674d8fa7abaa 0x2e266599f8703800 0x82e266599f870380

def z1125 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fc01a007ff0ff0d 0x77fc01a007ff0ff0

def z1126 : W := mkw 0x8ffd5f7500804414 0x88ffd5f750080441 0x8fffffff8000c037 0xf8fffffff8000c03

def z1127 : W := mkw 0x4002a08ae77d1bc0 0x44002a08ae77d1bc 0x3000000047fc3fc8 0x03000000047fc3fc

def z1128 : W := mkw 0x32401f880890feaf 0x032401f880890fea 0x10001f800000fff4 0x110001f800000fff

def z1129 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x7ffff8007fffc00f 0xf7ffff8007fffc00

def z1130 : W := mkw 0x4920000033430000 0x0492000003343000 0x6fe000007ff30009 0xe6fe000007ff3000

def z1131 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe3ffc78780ff8ff 0xffe3ffc78780ff8f

def z1132 : W := mkw 0xa2401fa50890f60e 0x0a2401fa50890f60 0x10001f878000ff04 0x110001f878000ff0

def z1133 : W := mkw 0xaffd5f752ac0e40e 0x0affd5f752ac0e40 0xfffffffffb80f80f 0xffffffffffb80f80

def z1134 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0xffe01fe07ff0fffd 0xfffe01fe07ff0fff

def z1135 : W := mkw 0x449fa000776f0000 0x0449fa000776f000 0x6fdf80007fff000b 0xe6fdf80007fff000

def z1136 : W := mkw 0x4dbd400033430000 0x04dbd40003343000 0x6ff800007bf30000 0xc6ff800007bf3000

def z1137 : W := mkw 0x8089402500000000 0x0808940250000000 0x8027e79f80000007 0xa8027e79f8000000

def z1138 : W := mkw 0x4920600022600000 0x0492060002260000 0x6fe060007ff00009 0xe6fe060007ff0000

def z1139 : W := mkw 0x1002a08ad43e1be1 0x41002a08ad43e1be 0x30000000447f3ff8 0x030000000447f3ff

def z1140 : W := mkw 0x0000808204141340 0x0000080820414134 0xb027e79fc47c3fcf 0xab027e79fc47c3fc

def z1141 : W := mkw 0x4dbde00027650000 0x04dbde0002765000 0x6fffe0007ff0000b 0xe6fffe0007ff0000

def z1142 : W := mkw 0x09600a8022d05604 0x009600a8022d0560 0x7fe01f807ff0ff0d 0xf7fe01f807ff0ff0

def z1143 : W := mkw 0x4002a08ad53f1bc0 0x44002a08ad53f1bc 0xb027e79fc47f3fcf 0xab027e79fc47f3fc

def z1144 : W := mkw 0x5002a08aff7fbbe9 0x45002a08aff7fbbe 0x700000007ffffff8 0x0700000007ffffff

def z1145 : W := mkw 0x22401f800890f60e 0x022401f800890f60 0x50001f800000ff0c 0x750001f800000ff0

def z1146 : W := mkw 0x32401fda8890ffef 0x432401fda8890ffe 0x90001fff8000fff4 0x190001fff8000fff

def z1147 : W := mkw 0x4dbfe026776f0150 0x84dbfe026776f015 0xffffe2667fff07ff 0xeffffe2667fff07f

def z1148 : W := mkw 0x0b601e002ac0e40c 0x00b601e002ac0e40 0x7fe01e007ff0ff0d 0xf7fe01e007ff0ff0

def z1149 : W := mkw 0x22401f828890f74e 0x422401f828890f74 0x10001f878000ff04 0x110001f878000ff0

def z1150 : W := mkw 0x0000a08a84341bc0 0x40000a08a84341bc 0x9027e79f84703fc7 0xa9027e79f84703fc

def z1151 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0x00000000047c07c0 0x000000000047c07c

def z1152 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x0fffe79f80000003 0xe0fffe79f8000000

def z1153 : W := mkw 0x80400b2500000000 0x080400b250000000 0x8027e79f80000007 0xa8027e79f8000000

def z1154 : W := mkw 0x22401f820890f75e 0x822401f820890f75 0x10001f800000fff4 0x110001f800000fff

def z1155 : W := mkw 0x49a9e00027650000 0x049a9e0002765000 0x4fe1e0003ff00001 0x44fe1e0003ff0000

def z1156 : W := mkw 0x22401f888890fe8e 0x422401f888890fe8 0x10001f998000ff04 0x110001f998000ff0

def z1157 : W := mkw 0x02401f0000000000 0x002401f000000000 0x8027ff9f80000007 0xb8027ff9f8000000

def z1158 : W := mkw 0x8ffd5f7500804404 0x08ffd5f750080440 0xcfffffff8380c007 0xfcfffffff8380c00

def z1159 : W := mkw 0x0920800026440000 0x0092080002644000 0x6fe180007ffc000b 0xe6fe180007ffc000

def z1160 : W := mkw 0x8ffd5f7500804404 0x08ffd5f750080440 0x8fffffff87800707 0xf8fffffff8780070

def z1161 : W := mkw 0x86dd5f7500000000 0x086dd5f750000000 0x81dfffff80000007 0x781dfffff8000000

def z1162 : W := mkw 0xaffd5f750880e40e 0x0affd5f750880e40 0x8fffffff8000c007 0xf8fffffff8000c00

def z1163 : W := mkw 0x0002a08ac53d1bd0 0xc0002a08ac53d1bd 0xb027e79fc47f3fff 0xab027e79fc47f3ff

def z1164 : W := mkw 0x4dbfe008776f0880 0x04dbfe008776f088 0xefffe0187fff00cb 0xeefffe0187fff00c

def z1165 : W := mkw 0x0002a08ac4bc5fd4 0xc0002a08ac4bc5fd 0x30000000447cfff8 0x030000000447cfff

def z1166 : W := mkw 0x22401fa40890f61e 0x822401fa40890f61 0x10001fe00000ff34 0x110001fe00000ff3

def z1167 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fe7e0007ff00009 0xe6fe7e0007ff0000

def z1168 : W := mkw 0x8ffd5f7501814414 0x88ffd5f750181441 0x8fffffff83800007 0xf8fffffff8380000

def z1169 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6fffe599ffff000b 0xe6fffe599ffff000

def z1170 : W := mkw 0x8f745f5100000000 0x08f745f510000000 0x8fe7ff9f80000007 0xf8fe7ff9f8000000

def z1171 : W := mkw 0x00400a2600804554 0x800400a260080455 0xd1d81a66078fc7ff 0x7d1d81a66078fc7f

def z1172 : W := mkw 0x02401e800890f60c 0x002401e800890f60 0x7fe01f807ff0ff0d 0xf7fe01f807ff0ff0

def z1173 : W := mkw 0x0ffd5f0000000000 0x00ffd5f000000000 0x8fffff9f80000007 0xf8fffff9f8000000

def z1174 : W := mkw 0x5dbfe058776f08a1 0x05dbfe058776f08a 0xfffff8787fffc0ff 0xffffff8787fffc0f

def z1175 : W := mkw 0xa2401ff70890f75e 0x8a2401ff70890f75 0x90001fff8000fff4 0x190001fff8000fff

def z1176 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xfe1f9e7e780ff8ff 0xffe1f9e7e780ff8f

def z1177 : W := mkw 0x4dbde00037670000 0x04dbde0003767000 0x4fffe0003ff30003 0xe4fffe0003ff3000

def z1178 : W := mkw 0xaffd5f752a40a00a 0x0affd5f752a40a00 0x8fffffffb8000007 0xf8fffffffb800000

def z1179 : W := mkw 0x0dbf4000724a0000 0x00dbf4000724a000 0x6fffe0007fff000b 0xe6fffe0007fff000

def z1180 : W := mkw 0x16163458d82aa8a9 0x416163458d82aa8a 0xfe1e7c79f80ff8fe 0xffe1e7c79f80ff8f

def z1181 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x0fffffff80000001 0xd0fffffff8000000

def z1182 : W := mkw 0x3002a08afefeffef 0x43002a08afefeffe 0x700000007ffffff8 0x0700000007ffffff

def z1183 : W := mkw 0x869d557500000000 0x0869d55750000000 0x801fe5ff80000002 0x0801fe5ff8000000

def z1184 : W := mkw 0x00c9aa2605a54554 0x800c9aa2605a5455 0xd1f9fa6607ffc7ff 0x7d1f9fa6607ffc7f

def z1185 : W := mkw 0x09a9802627450150 0x809a980262745015 0xeff980667fff00fb 0xeeff980667fff00f

def z1186 : W := mkw 0x8000007500000000 0x0800000750000000 0x8027e7ff80000007 0xa8027e7ff8000000

def z1187 : W := mkw 0x00c90a2401814414 0x800c90a240181441 0xc1ffffff8383c037 0xfc1ffffff8383c03

def z1188 : W := mkw 0xab605f812ad0f60e 0x0ab605f812ad0f60 0x7fe07f81fff0ff0d 0xf7fe07f81fff0ff0

def z1189 : W := mkw 0x00c90a2400804404 0x000c90a240080440 0xd1d99a66078fc7ff 0x7d1d99a66078fc7f

def z1190 : W := mkw 0x22401fd00890f60e 0x022401fd00890f60 0x90001ff80000ff04 0x190001ff80000ff0

def z1191 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0xcfffffff8003c037 0xfcfffffff8003c03

def z1192 : W := mkw 0x00c90a2400000000 0x000c90a240000000 0x81e7e79f80000007 0xa81e7e79f8000000

def z1193 : W := mkw 0x0920000022400000 0x0092000002240000 0x7fe018007ff0c00d 0xf7fe018007ff0c00

def z1194 : W := mkw 0x49a9e00027650000 0x049a9e0002765000 0x2fe1e0007ff00001 0x82fe1e0007ff0000

def z1195 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x3fe01f807ff0ff05 0x93fe01f807ff0ff0

def z1196 : W := mkw 0x5dbfe050776f0021 0x05dbfe050776f002 0x6fffe0607fff003b 0xe6fffe0607fff003

def z1197 : W := mkw 0xdffd5f753b43a029 0x0dffd5f753b43a02 0xcfffffffbb83c037 0xfcfffffffbb83c03

def z1198 : W := mkw 0x0002a080443c1200 0x00002a080443c120 0xb027e79fc47c3f0f 0xab027e79fc47c3f0

def z1199 : W := mkw 0x849d407500000000 0x0849d40750000000 0x803fe3ff80000003 0x0803fe3ff8000000

def z1200 : W := mkw 0x8ffd5f7501010010 0x88ffd5f750101001 0x8fffffff80030037 0xf8fffffff8003003

def z1201 : W := mkw 0x4dbde00037670000 0x04dbde0003767000 0x4fd800003ff30000 0x44fd800003ff3000

def z1202 : W := mkw 0x8ffd5f7500000000 0x08ffd5f750000000 0x9fffffff8400070f 0xf9fffffff8400070

def z1203 : W := mkw 0x292000802ad0f60e 0x0292000802ad0f60 0x7fe007807ff0ff0d 0xe7fe007807ff0ff0

def z1204 : W := mkw 0x0414005000000000 0x0041400500000000 0x803fe7ff80000007 0xa803fe7ff8000000

def z1205 : W := mkw 0xaffd5f752bc1e41e 0x8affd5f752bc1e41 0x4fd818603b83c030 0x54fd818603b83c03

def z1206 : W := mkw 0x4dbde00037670000 0x04dbde0003767000 0x6ff9e0007ff30009 0xe6ff9e0007ff3000

def z1207 : W := mkw 0x0920000022400000 0x0092000002240000 0xfff818607fffc0ff 0xffff818607fffc0f

def z1208 : W := mkw 0x82c91f7500000000 0x082c91f750000000 0x81ffffff80000007 0xf81ffffff8000000

def z1209 : W := mkw 0x3f3635d8fa7abaab 0x43f3635d8fa7abaa 0x2e266599f8703800 0x82e266599f870380

def z1210 : W := mkw 0x4dbfe08af77f1bc0 0x44dbfe08af77f1bc 0x7fd800007fff3fc8 0x47fd800007fff3fc

def z1211 : W := mkw 0x2b601fa42ad0f61e 0x82b601fa42ad0f61 0x7fe01fe07ff0ff3d 0xf7fe01fe07ff0ff3

def z1212 : W := mkw 0x0002008840181a80 0x00002008840181a8 0xb027e79fc47c3fcf 0xab027e79fc47c3fc

def z1213 : W := mkw 0x4dbfe008f76f0880 0x44dbfe008f76f088 0x6fffe019ffff000b 0xe6fffe019ffff000

def z1214 : W := mkw 0x0b601f8022501200 0x00b601f802250120 0x7fe01f807ff03f0d 0xf7fe01f807ff03f0

def z1215 : W := mkw 0x16161458580aa8a9 0x016161458580aa8a 0xee1e1c78780ff8f2 0xdee1e1c78780ff8f

def z1216 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0xeffff8607fff000f 0xfeffff8607fff000

def z1217 : W := mkw 0xaffd5f752bc1e41e 0x8affd5f752bc1e41 0xcfffffffbb83c037 0xfcfffffffbb83c03

def z1218 : W := mkw 0x09a9400000000000 0x009a940000000000 0x81e7e79f80000007 0xa81e7e79f8000000

def z1219 : W := mkw 0xaffd5f752ac0e40e 0x0affd5f752ac0e40 0xdfffffffbf80c70f 0xfdfffffffbf80c70

def z1220 : W := mkw 0x06161400580aa008 0x006161400580aa00 0xfe1e1c60780ff8fe 0xffe1e1c60780ff8f

def z1221 : W := mkw 0x8ffd5f7522c04404 0x08ffd5f7522c0440 0xfffffffffff0c70f 0xffffffffffff0c70

def z1222 : W := mkw 0x0414000000000000 0x0041400000000000 0x8e3fe79f80000007 0xe8e3fe79f8000000

def z1223 : W := mkw 0x0002a08ac43c1bc0 0x40002a08ac43c1bc 0xf027e79fc47fffff 0xaf027e79fc47ffff

def z1224 : W := mkw 0x09a9800027450000 0x009a980002745000 0x6fe180007ff00009 0xe6fe180007ff0000

def z1225 : W := mkw 0xb2401ffd0890feaf 0x0b2401ffd0890fea 0x90001fff8000fff4 0x190001fff8000fff

def z1226 : W := mkw 0x2b601fd02ad0f60e 0x02b601fd02ad0f60 0xffe01ff87ff0ff0d 0xfffe01ff87ff0ff0

def z1227 : W := mkw 0x4dbf4000734b0000 0x04dbf4000734b000 0x6ffe00007fff000b 0xe6ffe00007fff000

def z1228 : W := mkw 0x22401f820890f74e 0x022401f820890f74 0x90001f860000ffc4 0x190001f860000ffc

def z1229 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x2fffe0007ff00003 0xe2fffe0007ff0000

def z1230 : W := mkw 0x0920800226440140 0x0092080022644014 0xffe182067ffc07cf 0xeffe182067ffc07c

def z1231 : W := mkw 0x4dbfe008776f0880 0x04dbfe008776f088 0x6fffe4187fff380b 0xe6fffe4187fff380

def z1232 : W := mkw 0x0000000000000000 0x0000000000000000 0xd03fffff800fc0ff 0xfd03fffff800fc0f

def z1233 : W := mkw 0x120014580800a8a9 0x0120014580800a8a 0xfe181c78780ff8fe 0xffe181c78780ff8f

def z1234 : W := mkw 0xcffd5f7533430000 0x0cffd5f753343000 0xeffffffffff3000f 0xfeffffffffff3000

def z1235 : W := mkw 0x8ffd5f7501010000 0x08ffd5f750101000 0xcfffffff83830007 0xfcfffffff8383000

def z1236 : W := mkw 0x8be95f2500000000 0x08be95f250000000 0x8fe7ff9f80000007 0xf8fe7ff9f8000000

def z1237 : W := mkw 0x0dbd400022400000 0x00dbd40002240000 0x6ff800007ff00009 0xe6ff800007ff0000

def z1238 : W := mkw 0x4dbfe000776f0000 0x04dbfe000776f000 0x6ffff8607fffc03b 0xf6ffff8607fffc03

def z1239 : W := mkw 0x29e9aba6a7f55756 0xc29e9aba6a7f5575 0x01e1e38787f00701 0x001e1e38787f0070

def z1240 : W := mkw 0x8f745f7500000000 0x08f745f750000000 0x8e27ffff80000007 0xb8e27ffff8000000

def z1241 : W := mkw 0x0dbfe000666c0000 0x00dbfe000666c000 0x6fffe0007ffc000b 0xe6fffe0007ffc000

def z1242 : W := mkw 0x0dbdc00027450000 0x00dbdc0002745000 0x6fffe0007fff000b 0xe6fffe0007fff000

def z1243 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fc01f807ff0ff0c 0x57fc01f807ff0ff0

def z1244 : W := mkw 0x49222000726a0000 0x049222000726a000 0x6fe000007ff00009 0xe6fe000007ff0000

def z1245 : W := mkw 0x0200145000000000 0x0020014500000000 0x8027ffff80000007 0xb8027ffff8000000

def z1246 : W := mkw 0x9ffd5f751802a029 0x09ffd5f751802a02 0xfffffffff803f83f 0xffffffffff803f83

def z1247 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0x7fe1ff87fff0ff0d 0xf7fe1ff87fff0ff0

def z1248 : W := mkw 0x4dbde00037670000 0x04dbde0003767000 0x0fe1e0003ff00001 0x00fe1e0003ff0000

def z1249 : W := mkw 0x8ffd5f7501814414 0x88ffd5f750181441 0xdfffffff8783c73f 0xfdfffffff8783c73

def z1250 : W := mkw 0x2b601f802ad0f60e 0x02b601f802ad0f60 0xffe01f807ffcffcf 0xfffe01f807ffcffc

def z1251 : W := mkw 0x0002a08ac4bc5fc4 0x40002a08ac4bc5fc 0x7000000047fcffc8 0x07000000047fcffc

def z1252 : W := mkw 0x0002a08ac5bd5fd4 0xc0002a08ac5bd5fd 0x3000000047fc3fc8 0x03000000047fc3fc

def z1253 : W := mkw 0x0920000022400000 0x0092000002240000 0x7fe002007ff0070d 0xe7fe002007ff0070

def z1254 : W := mkw 0x4d36e000776f0000 0x04d36e000776f000 0x6fe660007fff0009 0xe6fe660007fff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z8,z4,z5]),(0,[z9,z1,z2,z10,z4,z5,z6]),(0,[z1,z2,z11,z12,z4,z5,z6]),(0,[z1,z2,z3,z4,z13,z5,z6])],[(0,[z1,z2,z3,z4,z5,z14,z6]),(1,[z1,z15,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z17,z5,z6]),(0,[z1,z2,z3,z4,z18,z6,z19])],[(0,[z1,z2,z3,z4,z5,z20,z6]),(0,[z1,z2,z3,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z6]),(0,[z1,z2,z3,z23,z4,z5,z6])],[(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z25,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z26,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z27]),(0,[z28,z1,z2,z3,z29,z4,z5]),(1,[z1,z2,z3,z4,z30,z6]),(0,[z31,z1,z2,z32,z3,z4,z6]),(1,[z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z34,z29,z4,z6])],[(0,[z35,z24,z2,z3,z4,z5,z6]),(0,[z7,z1,z36,z2,z3,z4,z5]),(0,[z1,z2,z3,z37,z38,z5,z6]),(0,[z1,z2,z3,z4,z5,z39,z6])],[(0,[z1,z2,z3,z40,z4,z5,z6]),(0,[z1,z41,z2,z3,z29,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6,z42]),(0,[z43,z1,z2,z3,z4,z5,z6]),(0,[z44,z28,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z45]),(0,[z1,z2,z3,z4,z5,z46,z6]),(0,[z47,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z48,z3,z4,z5]),(1,[z1,z2,z3,z49,z4,z5]),(0,[z1,z2,z3,z4,z5,z50,z6]),(0,[z1,z2,z3,z4,z51,z52,z6]),(0,[z7,z1,z2,z3,z4,z53,z5]),(0,[z9,z1,z3,z54,z4,z5,z6]),(0,[z1,z55,z2,z3,z4,z5,z6]),(1,[z1,z2,z56,z3,z5,z57]),(0,[z1,z2,z3,z58,z4,z5,z6])],[(1,[z1,z59,z2,z3,z4,z5]),(0,[z1,z2,z3,z60,z4,z5,z61]),(0,[z1,z2,z3,z29,z4,z51,z6]),(0,[z1,z2,z3,z4,z5,z62,z6])],[(1,[z1,z2,z3,z4,z63,z6]),(0,[z1,z2,z64,z3,z4,z5,z6]),(0,[z65,z7,z1,z2,z3,z4,z5]),(0,[z66,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z67,z3,z4,z68,z6]),(0,[z1,z2,z3,z69,z4,z5,z6]),(0,[z1,z2,z3,z4,z70,z5,z6]),(0,[z71,z1,z2,z32,z3,z4,z6])],[(0,[z72,z1,z2,z3,z4,z63,z6]),(0,[z1,z2,z3,z73,z4,z5,z6]),(0,[z1,z74,z2,z3,z4,z5,z6]),(0,[z1,z2,z75,z3,z4,z76,z6])],[(0,[z1,z2,z3,z77,z4,z5,z6]),(0,[z1,z2,z3,z4,z78,z51,z6]),(0,[z1,z79,z2,z3,z4,z5,z6]),(0,[z9,z1,z2,z54,z4,z5,z6])],[(0,[z1,z80,z2,z32,z3,z4,z6]),(0,[z28,z35,z1,z2,z3,z4,z5]),(0,[z1,z81,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z82]),(0,[z1,z2,z4,z78,z5,z76,z6]),(0,[z1,z2,z83,z32,z3,z4,z6]),(0,[z1,z2,z84,z3,z4,z5,z6])],[(0,[z7,z1,z80,z2,z3,z4,z5]),(0,[z85,z1,z2,z3,z4,z5,z6]),(0,[z24,z7,z1,z2,z3,z4,z5]),(0,[z1,z86,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z87,z4,z5,z6]),(0,[z1,z2,z3,z4,z88,z5,z6]),(0,[z1,z2,z3,z4,z89,z5,z6])],[(0,[z90,z7,z1,z2,z3,z4,z5]),(0,[z1,z2,z91,z3,z4,z5,z6]),(0,[z1,z2,z3,z92,z4,z5,z6]),(0,[z1,z2,z93,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z94,z5,z95])]],
   [[(0,[z1,z96,z2,z3,z4,z5,z6]),(0,[z1,z2,z12,z97,z4,z5,z6]),(0,[z1,z2,z3,z98,z4,z5,z6]),(1,[z1,z2,z3,z73,z4,z6]),(0,[z99,z1,z2,z3,z4,z5,z6]),(0,[z1,z100,z2,z3,z4,z5,z6]),(0,[z1,z2,z101,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z102]),(1,[z1,z2,z103,z38,z5,z6]),(0,[z104,z1,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z105])],[(0,[z1,z2,z106,z32,z3,z4,z6]),(0,[z1,z2,z3,z4,z107,z5,z6]),(0,[z108,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z109,z38,z5,z6]),(0,[z1,z2,z3,z4,z110,z5,z6])],[(0,[z7,z1,z2,z3,z4,z5,z111]),(0,[z1,z112,z2,z3,z37,z5,z6]),(0,[z1,z2,z3,z113,z4,z5,z6])],[(0,[z1,z2,z3,z4,z114,z5,z6]),(0,[z1,z115,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z116,z3,z4,z5]),(0,[z117,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z118,z5,z6]),(1,[z1,z2,z67,z119,z5,z6]),(0,[z1,z2,z3,z4,z5,z120,z6]),(0,[z1,z2,z3,z29,z4,z62,z6])],[(0,[z1,z2,z3,z4,z5,z121,z6]),(1,[z1,z2,z122,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z4,z6]),(0,[z123,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z124,z3,z4,z5,z6]),(0,[z1,z2,z125,z3,z4,z94,z6])],[(0,[z1,z2,z126,z3,z4,z5,z6]),(0,[z1,z2,z127,z3,z4,z5,z6]),(1,[z1,z128,z3,z37,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z129])],[(0,[z130,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z131,z5,z6]),(0,[z1,z36,z3,z4,z5,z52,z6])]],
   [[(0,[z90,z1,z2,z97,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z132,z6]),(0,[z1,z2,z3,z4,z5,z133,z6]),(0,[z1,z2,z134,z3,z4,z5,z6])],[(0,[z28,z1,z2,z3,z4,z5,z62]),(0,[z1,z2,z3,z37,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z76,z6]),(0,[z1,z2,z3,z4,z5,z57,z135]),(0,[z1,z136,z2,z3,z4,z5,z6])],[(0,[z1,z137,z2,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z109,z6]),(0,[z1,z2,z125,z3,z29,z4,z6])],[(0,[z28,z138,z1,z2,z3,z4,z5]),(0,[z28,z1,z2,z3,z54,z4,z5]),(1,[z1,z2,z32,z3,z6,z57])],[(1,[z139,z80,z3,z4,z5,z6]),(0,[z28,z90,z1,z2,z3,z4,z5]),(0,[z85,z1,z2,z32,z3,z5,z6]),(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z37,z4,z6])],[(0,[z1,z2,z116,z3,z29,z4,z6]),(0,[z141,z1,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z52]),(0,[z1,z2,z3,z4,z30,z5,z6]),(1,[z1,z142,z10,z4,z5,z6]),(0,[z1,z112,z10,z3,z4,z5,z6]),(0,[z1,z143,z2,z3,z4,z5,z6]),(0,[z1,z144,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z120,z6]),(0,[z1,z2,z125,z3,z4,z5,z95])],[(0,[z145,z1,z2,z3,z4,z5,z6]),(1,[z28,z2,z3,z4,z5,z146]),(0,[z9,z1,z2,z103,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z147,z148]),(0,[z1,z2,z84,z3,z29,z4,z6]),(1,[z1,z2,z3,z58,z5,z6])],[(1,[z1,z2,z149,z3,z4,z5]),(0,[z85,z1,z2,z3,z29,z4,z6]),(0,[z150,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z151,z5,z6])]],
   [[(0,[z90,z139,z2,z3,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z51,z6]),(0,[z7,z1,z2,z3,z4,z5,z51]),(0,[z35,z1,z2,z32,z3,z4,z6]),(1,[z1,z2,z3,z152,z4,z6]),(0,[z1,z2,z3,z153,z29,z4,z6])],[(0,[z154,z1,z2,z3,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z155,z6]),(0,[z28,z7,z1,z2,z3,z4,z5]),(1,[z1,z2,z156,z4,z5,z6]),(0,[z1,z2,z157,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z5,z6]),(0,[z159,z1,z2,z3,z4,z5,z6]),(0,[z1,z41,z36,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z160,z5,z6]),(0,[z1,z2,z161,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z95,z6])],[(0,[z1,z2,z3,z4,z162,z5,z6]),(1,[z28,z1,z2,z3,z4,z163]),(0,[z28,z9,z1,z2,z3,z4,z5]),(0,[z1,z2,z164,z3,z4,z5,z6]),(0,[z1,z2,z32,z32,z3,z4,z6])],[(0,[z1,z2,z165,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z148]),(0,[z1,z166,z2,z3,z4,z5,z6])],[(0,[z167,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z168,z4,z5,z6]),(0,[z28,z1,z2,z3,z153,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z169])],[(0,[z139,z1,z80,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z170,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z7,z1,z2,z12,z3,z4,z5]),(0,[z1,z2,z171,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z57]),(0,[z1,z172,z2,z3,z4,z5,z6])],[(0,[z72,z2,z106,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z173,z6]),(0,[z1,z2,z174,z3,z4,z5,z6]),(0,[z1,z2,z3,z107,z5,z51,z6]),(0,[z1,z128,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z175,z6]),(0,[z1,z2,z3,z4,z5,z18,z6]),(0,[z1,z2,z3,z4,z5,z6,z135])],[(0,[z7,z1,z2,z3,z4,z155,z5]),(0,[z1,z2,z32,z3,z119,z4,z6]),(0,[z1,z2,z176,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z10,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z177,z5,z6]),(0,[z1,z2,z178,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z179])],[(0,[z1,z80,z2,z3,z4,z5,z180]),(0,[z1,z2,z181,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z182]),(1,[z1,z2,z183,z4,z76,z6])],[(0,[z1,z2,z3,z184,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z185,z6]),(0,[z1,z2,z3,z4,z53,z5,z6]),(0,[z1,z2,z3,z4,z186,z5,z6])],[(0,[z28,z1,z79,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z187,z6])],[(0,[z1,z2,z3,z4,z5,z188,z6]),(0,[z1,z2,z3,z4,z5,z6,z189]),(0,[z1,z2,z3,z4,z155,z52,z6]),(0,[z7,z1,z190,z2,z3,z4,z5]),(0,[z191,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z192,z4,z6]),(1,[z1,z2,z3,z4,z193,z6])],[(0,[z1,z2,z3,z29,z4,z52,z6]),(0,[z1,z2,z3,z29,z4,z6,z148])],[(0,[z194,z1,z2,z3,z4,z5,z6]),(1,[z9,z1,z54,z4,z5,z6]),(0,[z1,z128,z2,z3,z37,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z195])],[(0,[z1,z2,z3,z196,z4,z5,z6]),(0,[z1,z197,z2,z3,z4,z5,z6]),(0,[z1,z2,z116,z4,z5,z6,z148]),(0,[z7,z1,z2,z3,z4,z118,z5]),(0,[z1,z2,z3,z198,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z29,z60,z4,z6]),(0,[z1,z2,z3,z4,z78,z52,z6]),(0,[z1,z2,z3,z29,z4,z18,z6]),(0,[z1,z2,z3,z29,z4,z6,z135])],[(0,[z1,z2,z3,z4,z199,z5,z6]),(0,[z1,z80,z2,z3,z29,z4,z6]),(0,[z2,z3,z4,z5,z200,z6,z146]),(0,[z7,z1,z2,z67,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z201,z6]),(0,[z1,z2,z103,z67,z4,z5,z6]),(0,[z1,z2,z202,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z95,z6]),(0,[z1,z2,z3,z29,z4,z203,z6])],[(0,[z204,z1,z2,z3,z4,z205,z6]),(0,[z28,z1,z36,z2,z3,z4,z5]),(0,[z206,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z32,z3,z4,z6]),(1,[z1,z2,z3,z153,z5,z18]),(0,[z1,z2,z3,z4,z207,z5,z6])],[(0,[z72,z1,z2,z32,z3,z4,z6]),(1,[z28,z1,z2,z168,z4,z5]),(0,[z7,z1,z2,z3,z4,z5,z147]),(0,[z208,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z11,z3,z4,z5,z120])],[(0,[z1,z2,z209,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z210,z6]),(1,[z24,z2,z3,z4,z51,z6]),(0,[z211,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z212,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z148]),(1,[z1,z2,z32,z3,z29,z6])],[(0,[z99,z28,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z213,z6]),(1,[z1,z2,z214,z4,z5,z6]),(0,[z1,z215,z2,z3,z4,z5,z6])],[(0,[z138,z1,z2,z32,z3,z5,z6]),(1,[z1,z2,z3,z4,z5,z216]),(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z1,z41,z2,z3,z4,z52,z6]),(0,[z1,z2,z3,z4,z5,z95,z18])],[(0,[z28,z1,z2,z3,z60,z4,z5]),(0,[z7,z1,z2,z10,z3,z4,z5]),(0,[z191,z7,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z217,z5,z6]),(0,[z1,z128,z2,z3,z29,z4,z6]),(0,[z1,z2,z218,z3,z4,z5,z6]),(1,[z1,z3,z4,z219,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z135])]],
   [[(0,[z1,z220,z2,z3,z4,z5,z6]),(0,[z24,z2,z3,z4,z5,z51,z6]),(0,[z1,z221,z2,z3,z4,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z222,z6]),(0,[z1,z2,z75,z3,z29,z4,z6]),(0,[z1,z2,z3,z29,z4,z6,z195])],[(0,[z138,z1,z2,z3,z29,z4,z6]),(0,[z1,z36,z2,z3,z4,z52,z6]),(0,[z1,z2,z32,z3,z4,z223,z6]),(0,[z1,z2,z3,z4,z224,z5,z6])],[(0,[z1,z2,z3,z4,z5,z225,z6]),(0,[z1,z2,z3,z4,z5,z226,z6]),(0,[z1,z2,z183,z75,z4,z5,z6]),(0,[z1,z2,z3,z4,z94,z95,z6])],[(1,[z85,z1,z2,z32,z3,z6]),(0,[z7,z1,z2,z3,z4,z5,z57]),(0,[z1,z2,z3,z119,z109,z5,z6]),(0,[z1,z128,z3,z37,z4,z5,z6]),(0,[z1,z2,z3,z227,z4,z5,z6])],[(0,[z1,z2,z228,z3,z4,z5,z6]),(1,[z1,z112,z3,z109,z5,z6]),(0,[z1,z229,z2,z3,z4,z5,z6])],[(0,[z28,z72,z1,z2,z3,z4,z5]),(0,[z28,z1,z2,z15,z3,z4,z5]),(0,[z1,z2,z230,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z231,z6]),(0,[z1,z3,z4,z223,z5,z52,z6]),(0,[z1,z2,z3,z4,z5,z148,z57]),(0,[z1,z2,z232,z3,z4,z5,z6]),(0,[z1,z2,z233,z3,z4,z5,z6]),(0,[z234,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z235,z6]),(0,[z1,z2,z3,z4,z5,z102,z6]),(0,[z1,z2,z11,z32,z3,z4,z6]),(0,[z1,z2,z56,z3,z5,z6,z57]),(0,[z1,z2,z3,z4,z94,z5,z6])],[(0,[z28,z1,z2,z3,z4,z5,z111]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z1,z142,z2,z10,z4,z5,z6]),(0,[z1,z2,z32,z3,z236,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z237])]],
   [[(0,[z1,z2,z32,z3,z4,z6,z146]),(0,[z1,z2,z3,z4,z5,z238,z6]),(0,[z1,z2,z3,z239,z4,z5,z6])],[(0,[z90,z204,z2,z3,z4,z5,z6]),(0,[z1,z240,z2,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z78,z6]),(0,[z1,z2,z32,z3,z4,z94,z6])],[(0,[z241,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z51,z6]),(0,[z1,z2,z3,z4,z242,z5,z6]),(0,[z141,z28,z1,z2,z3,z4,z5]),(0,[z1,z2,z32,z3,z4,z200,z6]),(1,[z240,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z243,z6]),(0,[z1,z2,z32,z244,z3,z4,z6]),(0,[z1,z2,z3,z192,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z116,z3,z4,z5,z188]),(0,[z1,z2,z3,z4,z245,z5,z6]),(1,[z1,z2,z32,z3,z153,z6])],[(0,[z246,z1,z2,z3,z4,z5,z6]),(0,[z35,z1,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z5,z247,z6]),(1,[z248,z2,z3,z4,z5,z6])],[(0,[z249,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z205,z6]),(0,[z204,z2,z3,z97,z4,z5,z6]),(0,[z1,z2,z250,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z120]),(0,[z1,z2,z251,z3,z4,z5,z6])],[(0,[z252,z1,z2,z3,z4,z5,z6]),(0,[z90,z2,z116,z3,z4,z5,z6]),(0,[z1,z2,z3,z253,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z200]),(0,[z9,z1,z2,z119,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z254]),(0,[z1,z2,z32,z3,z29,z4,z6])],[(0,[z1,z2,z3,z4,z155,z5,z20]),(0,[z1,z10,z3,z37,z4,z5,z6]),(0,[z1,z2,z255,z3,z4,z5,z6]),(0,[z1,z256,z2,z3,z4,z5,z6])]],
   [[(0,[z257,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z258,z4,z5,z6]),(0,[z1,z2,z259,z3,z4,z5,z6]),(0,[z1,z260,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z261,z6]),(0,[z1,z2,z3,z4,z262,z5,z6]),(0,[z1,z2,z263,z32,z3,z4,z6])],[(0,[z1,z2,z264,z3,z4,z5,z6]),(0,[z7,z1,z2,z265,z3,z4,z5]),(0,[z1,z2,z3,z4,z52,z76,z6]),(0,[z1,z2,z3,z119,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z266,z6]),(1,[z1,z2,z125,z3,z4,z135])],[(0,[z1,z2,z3,z4,z5,z267,z6]),(0,[z1,z2,z3,z4,z268,z5,z6]),(0,[z1,z269,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z270]),(0,[z1,z142,z2,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z271])],[(0,[z1,z2,z3,z272,z4,z5,z6]),(0,[z28,z1,z15,z3,z4,z5,z6]),(0,[z1,z2,z125,z3,z4,z5,z6]),(0,[z1,z273,z2,z3,z4,z5,z6])],[(0,[z1,z274,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z61]),(0,[z28,z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z29,z4,z155,z6]),(0,[z7,z1,z2,z56,z3,z4,z5]),(0,[z1,z112,z128,z3,z4,z5,z6]),(0,[z1,z2,z125,z3,z4,z6,z135])],[(0,[z1,z2,z275,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z276,z6])],[(0,[z1,z2,z116,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z118,z5,z6]),(0,[z1,z2,z277,z3,z4,z5,z6]),(0,[z1,z2,z3,z278,z4,z5,z6]),(0,[z1,z2,z279,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z94,z5,z135])]],
   [[(0,[z1,z2,z280,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z78,z155,z6]),(0,[z7,z1,z1,z2,z3,z4,z5]),(0,[z7,z1,z2,z32,z3,z4,z6]),(0,[z9,z1,z2,z3,z29,z4,z6]),(0,[z1,z2,z122,z4,z109,z5,z6]),(0,[z1,z281,z2,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z5,z6,z57])],[(0,[z1,z2,z282,z3,z5,z51,z6]),(0,[z1,z2,z3,z4,z5,z6,z283])],[(0,[z1,z2,z3,z4,z5,z6,z284]),(0,[z1,z2,z32,z3,z4,z51,z6]),(0,[z28,z1,z2,z12,z3,z4,z5]),(0,[z9,z1,z2,z3,z285,z5,z6]),(0,[z1,z2,z3,z286,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z287]),(0,[z1,z2,z3,z119,z37,z5,z6]),(0,[z1,z2,z3,z4,z288,z5,z6]),(0,[z1,z55,z2,z3,z4,z5,z147]),(0,[z1,z2,z3,z153,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z289])],[(0,[z139,z1,z106,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z97,z4,z5]),(0,[z7,z1,z2,z75,z3,z4,z5]),(0,[z9,z1,z2,z3,z4,z5,z182]),(0,[z1,z2,z290,z3,z4,z5,z6]),(0,[z1,z2,z3,z291,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z292,z57])],[(0,[z1,z2,z293,z3,z4,z118,z5]),(0,[z28,z1,z2,z3,z4,z155,z5]),(0,[z1,z2,z294,z3,z4,z5,z6]),(0,[z9,z1,z3,z37,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z295]),(1,[z1,z2,z32,z3,z4,z296]),(0,[z1,z2,z3,z203,z5,z62,z6])],[(0,[z1,z80,z2,z3,z4,z5,z42]),(0,[z1,z2,z32,z116,z3,z4,z6]),(0,[z28,z1,z2,z3,z4,z163,z5]),(0,[z7,z1,z2,z103,z3,z4,z5]),(0,[z297,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z298]),(0,[z1,z2,z299,z3,z4,z5,z6])],[(0,[z300,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z142,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z301,z6]),(0,[z1,z302,z3,z4,z38,z5,z6])],[(0,[z72,z1,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z203,z5,z6]),(0,[z1,z2,z32,z3,z4,z5,z296]),(0,[z1,z2,z3,z58,z5,z95,z6])]],
   [[(0,[z303,z1,z2,z3,z4,z5,z6]),(0,[z304,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z305,z6]),(0,[z306,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z307,z4,z5,z6]),(0,[z1,z2,z12,z3,z4,z5,z120]),(0,[z1,z2,z244,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z308,z5,z6]),(1,[z28,z7,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z309,z5,z6]),(0,[z1,z2,z75,z4,z78,z5,z6]),(0,[z310,z1,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z289])],[(0,[z1,z2,z3,z4,z5,z311,z6]),(0,[z1,z2,z10,z3,z4,z5,z6]),(0,[z1,z128,z2,z3,z109,z5,z6])],[(0,[z1,z2,z3,z4,z5,z312,z6]),(0,[z1,z2,z313,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z314,z5,z6]),(0,[z1,z2,z3,z4,z94,z51,z6]),(0,[z1,z190,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z315]),(0,[z9,z1,z2,z3,z316,z5,z6]),(0,[z1,z128,z2,z3,z4,z317,z6]),(0,[z318,z1,z2,z3,z4,z5,z6])],[(1,[z1,z319,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z320,z5,z6]),(0,[z28,z1,z2,z3,z4,z118,z5]),(0,[z85,z7,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z94,z155,z6]),(0,[z1,z2,z321,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z62,z6]),(0,[z1,z2,z3,z4,z5,z6,z19]),(0,[z322,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z97,z4,z5,z6,z148]),(0,[z1,z2,z3,z4,z323,z5,z6]),(0,[z85,z1,z2,z3,z4,z314,z6]),(0,[z1,z2,z32,z3,z54,z4,z6]),(0,[z1,z142,z2,z103,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z120,z147]),(0,[z1,z2,z125,z3,z4,z5,z135])],[(0,[z90,z2,z106,z3,z4,z5,z6]),(0,[z28,z1,z2,z67,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z324,z6]),(0,[z1,z2,z325,z3,z4,z5,z6])],[(1,[z204,z2,z97,z4,z5,z6]),(0,[z1,z2,z3,z60,z5,z6,z57]),(0,[z7,z1,z128,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z326,z6]),(0,[z1,z2,z3,z4,z5,z327,z6])]],
   [[(0,[z1,z2,z328,z3,z4,z5,z6]),(0,[z28,z1,z142,z2,z3,z4,z5]),(0,[z28,z1,z2,z3,z4,z5,z147]),(0,[z71,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z329,z6]),(0,[z1,z2,z330,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z331,z6])],[(0,[z191,z1,z80,z3,z4,z5,z6]),(0,[z1,z2,z149,z3,z97,z4,z5]),(0,[z1,z2,z3,z316,z4,z5,z6]),(0,[z1,z128,z2,z3,z4,z329,z6]),(0,[z1,z2,z3,z4,z223,z76,z6]),(0,[z1,z2,z332,z3,z4,z5,z6])],[(0,[z204,z1,z2,z32,z3,z4,z6]),(1,[z28,z1,z2,z3,z253,z5]),(0,[z1,z2,z3,z4,z5,z147,z57]),(0,[z1,z2,z103,z3,z38,z5,z6]),(0,[z1,z2,z67,z3,z29,z4,z6]),(0,[z1,z2,z11,z3,z29,z4,z6]),(0,[z1,z2,z333,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z334,z57]),(1,[z1,z2,z3,z4,z6,z292])],[(0,[z1,z80,z2,z3,z4,z5,z6]),(0,[z1,z55,z3,z4,z5,z6,z147]),(0,[z1,z2,z103,z32,z3,z4,z6]),(0,[z1,z2,z83,z3,z4,z5,z6])],[(1,[z28,z138,z2,z3,z4,z5]),(0,[z1,z2,z335,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z336,z5,z6])],[(0,[z337,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z338,z3,z4,z5,z6]),(0,[z1,z2,z3,z339,z4,z5,z6]),(1,[z1,z2,z3,z4,z94,z95])],[(0,[z28,z1,z41,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z52,z6]),(0,[z1,z2,z183,z4,z5,z76,z6]),(0,[z1,z2,z32,z3,z4,z120,z6]),(0,[z1,z2,z32,z3,z153,z4,z6]),(0,[z104,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z56,z3,z4,z5,z6])],[(0,[z1,z2,z106,z3,z4,z5,z6]),(1,[z28,z2,z3,z60,z4,z5]),(0,[z1,z2,z340,z3,z4,z109,z6]),(0,[z1,z2,z3,z4,z341,z5,z6]),(0,[z1,z2,z3,z153,z4,z5,z18])]],
   [[(0,[z1,z2,z3,z342,z4,z5,z6]),(0,[z1,z2,z3,z97,z29,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z343]),(0,[z28,z1,z2,z3,z4,z5,z57]),(0,[z7,z1,z2,z3,z4,z109,z5]),(0,[z7,z1,z2,z3,z4,z38,z5])],[(0,[z1,z2,z3,z29,z4,z6,z147]),(0,[z344,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z345,z6]),(0,[z28,z1,z2,z3,z4,z346,z5]),(0,[z1,z2,z3,z4,z5,z132,z6]),(0,[z1,z2,z75,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z347,z6]),(0,[z1,z2,z3,z4,z5,z348,z6])],[(0,[z90,z1,z2,z32,z3,z4,z6]),(1,[z1,z2,z3,z4,z5,z349]),(0,[z138,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z55,z2,z3,z4,z5]),(0,[z1,z142,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z350,z6]),(0,[z1,z2,z351,z3,z4,z5,z6])],[(0,[z1,z59,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z156,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z352]),(0,[z1,z2,z353,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z354]),(0,[z1,z2,z355,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z356,z6])],[(1,[z85,z2,z3,z60,z5,z6]),(0,[z1,z2,z3,z4,z357,z5,z6]),(0,[z1,z2,z32,z358,z3,z4,z6])],[(0,[z1,z359,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z360]),(0,[z28,z1,z2,z168,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z361])]],
   [[(0,[z1,z2,z3,z362,z4,z5,z6]),(0,[z7,z1,z2,z32,z3,z4,z5]),(0,[z9,z1,z2,z3,z4,z301,z6]),(0,[z1,z2,z363,z3,z4,z5,z6])],[(0,[z1,z2,z3,z364,z4,z5,z6]),(0,[z138,z2,z3,z4,z118,z5,z6]),(0,[z1,z2,z3,z4,z5,z61,z6]),(0,[z1,z112,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z4,z326,z5,z6])],[(0,[z365,z1,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z120]),(0,[z1,z366,z2,z3,z4,z5,z6]),(0,[z367,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z368,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z60,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z200]),(0,[z9,z369,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z370,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z95,z57]),(0,[z1,z2,z3,z4,z5,z6,z371])],[(0,[z1,z2,z3,z73,z4,z118,z6]),(0,[z7,z1,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z5,z372,z6]),(0,[z1,z2,z3,z4,z5,z6,z373]),(0,[z1,z55,z2,z3,z4,z5,z111])],[(0,[z7,z1,z2,z3,z119,z4,z5]),(0,[z1,z2,z3,z4,z5,z374,z6])],[(0,[z138,z7,z1,z2,z3,z4,z5]),(0,[z35,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z375,z3,z4,z5,z51]),(0,[z7,z1,z2,z183,z3,z4,z5]),(0,[z1,z2,z32,z3,z4,z52,z6]),(0,[z191,z1,z2,z3,z4,z5,z147]),(0,[z1,z2,z75,z3,z4,z78,z6]),(0,[z1,z2,z32,z3,z4,z6,z148]),(0,[z1,z2,z3,z339,z29,z4,z6]),(0,[z1,z2,z3,z4,z5,z376,z6])],[(0,[z28,z7,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z125,z3,z4,z5]),(0,[z7,z1,z2,z3,z4,z5,z95]),(0,[z1,z2,z3,z4,z5,z377,z6]),(0,[z1,z2,z56,z3,z29,z4,z6])]],
   [[(0,[z1,z2,z106,z3,z29,z4,z6]),(0,[z1,z2,z378,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z379,z6]),(1,[z1,z2,z368,z3,z4,z6]),(0,[z1,z2,z32,z3,z4,z5,z6])],[(0,[z1,z2,z3,z380,z4,z5,z6]),(0,[z1,z2,z32,z3,z60,z4,z6]),(1,[z35,z2,z3,z4,z155,z6]),(0,[z1,z3,z37,z4,z109,z5,z6]),(0,[z381,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z382]),(0,[z1,z2,z383,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z384,z6]),(0,[z1,z2,z32,z3,z4,z18,z6]),(0,[z1,z2,z32,z3,z4,z6,z135])],[(0,[z28,z1,z2,z56,z3,z4,z5]),(0,[z1,z2,z3,z385,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z386,z6]),(0,[z1,z2,z32,z3,z4,z203,z6]),(1,[z1,z2,z32,z3,z62,z6])],[(0,[z191,z1,z55,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z38,z5,z6]),(0,[z1,z2,z56,z3,z4,z5,z18]),(0,[z1,z2,z387,z3,z4,z5,z6])],[(0,[z1,z2,z3,z388,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z389,z6])],[(0,[z1,z59,z2,z106,z3,z4,z5]),(0,[z139,z2,z3,z97,z4,z5,z6]),(0,[z1,z2,z3,z4,z205,z5,z6]),(0,[z28,z1,z1,z2,z3,z4,z5]),(0,[z1,z2,z15,z3,z4,z5,z6]),(0,[z28,z1,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z4,z390,z5,z6]),(0,[z1,z2,z3,z4,z5,z296,z6]),(0,[z310,z1,z2,z3,z29,z4,z6])],[(0,[z28,z1,z80,z2,z3,z4,z5]),(1,[z28,z1,z2,z156,z4,z5]),(0,[z7,z1,z2,z3,z4,z5,z146]),(0,[z1,z391,z2,z3,z4,z5,z6])],[(0,[z392,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z393]),(0,[z1,z2,z214,z4,z109,z5,z6]),(0,[z1,z2,z3,z4,z5,z120,z111]),(0,[z1,z2,z3,z4,z5,z394,z6]),(0,[z1,z2,z395,z3,z4,z5,z6])]],
   [[(0,[z28,z1,z2,z3,z97,z4,z5]),(0,[z1,z2,z48,z3,z97,z4,z5]),(0,[z28,z1,z2,z75,z3,z4,z5]),(0,[z7,z1,z2,z396,z3,z4,z5]),(0,[z1,z2,z67,z3,z38,z5,z6])],[(1,[z1,z2,z11,z4,z5,z148])],[(0,[z28,z1,z2,z168,z3,z4,z5]),(1,[z28,z1,z2,z3,z4,z132]),(0,[z1,z2,z3,z397,z4,z5,z6]),(0,[z1,z2,z165,z3,z4,z38,z6]),(0,[z1,z2,z3,z4,z193,z5,z6])],[(0,[z1,z2,z398,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z399]),(0,[z1,z2,z265,z3,z4,z5,z6]),(0,[z1,z400,z2,z3,z4,z5,z6]),(0,[z367,z1,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z193,z18,z6])],[(0,[z401,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z183,z3,z4,z76,z6])],[(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z403,z6]),(0,[z1,z2,z3,z404,z4,z5,z6]),(0,[z1,z2,z405,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z406,z6])],[(0,[z204,z1,z2,z3,z29,z4,z6]),(0,[z1,z407,z2,z3,z4,z5,z6]),(0,[z1,z112,z3,z4,z109,z5,z6]),(0,[z408,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z60,z4,z5,z6]),(0,[z1,z2,z409,z3,z4,z5,z6]),(0,[z1,z2,z103,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z410]),(0,[z1,z2,z12,z3,z29,z4,z6]),(0,[z411,z1,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z412,z6])]],
   [[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z293,z3,z4,z5,z6]),(1,[z28,z1,z2,z3,z346,z5]),(0,[z1,z2,z3,z4,z413,z5,z6]),(0,[z1,z3,z4,z219,z38,z5,z6])],[(0,[z72,z1,z2,z3,z4,z5,z6]),(0,[z139,z80,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z118,z5,z6,z57]),(1,[z1,z2,z3,z4,z5,z414]),(0,[z1,z2,z103,z3,z119,z5,z6]),(0,[z1,z2,z415,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z416]),(0,[z1,z2,z12,z4,z5,z120,z6])],[(0,[z337,z28,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z417,z4,z5,z6]),(0,[z1,z3,z4,z5,z111,z6,z147]),(0,[z1,z2,z3,z418,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z334])],[(0,[z1,z419,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z420,z6]),(0,[z1,z2,z421,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z422,z5,z6]),(0,[z1,z2,z3,z49,z4,z118,z5]),(1,[z1,z2,z3,z4,z131,z5]),(0,[z28,z1,z128,z2,z3,z4,z5]),(0,[z1,z2,z3,z122,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z423,z6])],[(0,[z1,z2,z3,z4,z5,z6,z424]),(0,[z1,z425,z2,z3,z4,z5,z6]),(0,[z138,z1,z2,z3,z60,z5,z6]),(0,[z9,z7,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z201]),(0,[z1,z2,z3,z4,z426,z5,z6]),(0,[z1,z2,z3,z4,z5,z427,z6]),(0,[z1,z2,z428,z3,z4,z5,z6]),(0,[z1,z2,z183,z32,z3,z4,z6])],[(0,[z1,z429,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z430,z6]),(0,[z1,z2,z3,z4,z5,z6,z431]),(0,[z1,z2,z3,z29,z4,z38,z6]),(0,[z1,z2,z432,z3,z4,z5,z6]),(0,[z1,z2,z433,z3,z4,z5,z6]),(0,[z1,z2,z3,z434,z4,z5,z6])],[(0,[z191,z1,z106,z3,z4,z5,z6]),(0,[z1,z2,z435,z3,z4,z5,z6]),(0,[z90,z1,z2,z3,z29,z4,z6]),(0,[z1,z142,z2,z3,z29,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z436,z6]),(0,[z138,z2,z3,z4,z5,z200,z6]),(0,[z28,z2,z3,z60,z4,z5,z6]),(0,[z2,z3,z4,z155,z5,z51,z6]),(0,[z1,z2,z437,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z6]),(0,[z1,z2,z395,z3,z29,z4,z6])],[(1,[z1,z2,z3,z4,z5,z180]),(0,[z438,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z131,z5,z51]),(0,[z1,z2,z3,z439,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z440]),(1,[z1,z302,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z33]),(0,[z1,z2,z441,z3,z4,z5,z6])],[(1,[z1,z2,z3,z253,z5,z6]),(0,[z1,z2,z3,z4,z442,z5,z6]),(0,[z1,z2,z3,z4,z5,z443,z6]),(0,[z1,z2,z3,z4,z5,z18,z111]),(0,[z1,z2,z3,z444,z4,z5,z6]),(0,[z1,z2,z3,z4,z95,z6,z135])],[(0,[z1,z2,z3,z4,z445,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z446]),(0,[z1,z2,z3,z153,z118,z5,z6]),(0,[z1,z2,z3,z447,z4,z5,z6]),(0,[z35,z1,z2,z3,z4,z51,z6]),(0,[z1,z2,z3,z4,z5,z448,z6]),(1,[z1,z2,z12,z4,z5,z120]),(0,[z1,z2,z449,z3,z4,z5,z6])],[(0,[z35,z1,z2,z3,z4,z155,z6]),(0,[z1,z2,z67,z3,z4,z5,z6]),(0,[z1,z450,z2,z3,z4,z5,z6]),(0,[z1,z2,z11,z3,z4,z5,z6]),(0,[z1,z2,z32,z12,z3,z4,z6])],[(0,[z451,z1,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z109,z5]),(0,[z28,z1,z2,z3,z4,z38,z5]),(0,[z1,z2,z3,z4,z5,z452,z6])],[(0,[z1,z2,z32,z3,z4,z155,z6]),(0,[z453,z1,z2,z3,z4,z5,z6])],[(1,[z90,z2,z116,z4,z5,z6]),(0,[z1,z2,z3,z4,z454,z5,z6]),(0,[z35,z2,z3,z4,z155,z5,z6]),(0,[z365,z28,z1,z2,z3,z4,z5]),(0,[z7,z1,z2,z3,z4,z17,z5]),(0,[z1,z455,z2,z3,z4,z5,z6]),(0,[z456,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z29,z4,z118,z6]),(0,[z28,z1,z55,z2,z3,z4,z5]),(0,[z191,z1,z2,z3,z4,z5,z111]),(0,[z1,z2,z3,z4,z5,z457,z6])],[(0,[z28,z139,z1,z2,z3,z4,z5]),(0,[z28,z1,z2,z3,z253,z4,z5]),(0,[z1,z2,z3,z156,z4,z5,z6]),(0,[z1,z2,z458,z3,z4,z5,z6]),(0,[z459,z1,z2,z3,z4,z5,z6]),(0,[z460,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z461,z6]),(1,[z1,z2,z3,z29,z4,z6])],[(0,[z139,z1,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z97,z4,z5,z6]),(0,[z1,z2,z3,z4,z223,z51,z6]),(0,[z1,z2,z3,z4,z5,z6,z462]),(1,[z1,z2,z3,z346,z5,z6]),(0,[z28,z1,z2,z3,z253,z5,z6]),(0,[z1,z2,z463,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z111,z6]),(0,[z464,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z465])],[(1,[z138,z1,z2,z32,z3,z6]),(0,[z2,z3,z60,z4,z5,z200,z6]),(0,[z1,z2,z3,z466,z4,z5,z6]),(1,[z1,z2,z3,z285,z5,z6]),(0,[z1,z2,z3,z54,z29,z4,z6]),(0,[z1,z2,z3,z467,z4,z5,z6]),(0,[z1,z2,z67,z119,z4,z5,z6]),(0,[z1,z2,z3,z4,z468,z5,z6])],[(0,[z1,z2,z469,z3,z4,z5,z6]),(0,[z7,z1,z112,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z470]),(1,[z1,z2,z3,z4,z5,z182]),(0,[z1,z2,z3,z4,z471,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z472]),(0,[z1,z473,z2,z3,z4,z5,z6]),(0,[z1,z2,z474,z3,z4,z5,z6]),(0,[z1,z2,z421,z3,z29,z4,z6])],[(0,[z28,z1,z2,z32,z3,z4,z5]),(0,[z1,z2,z3,z152,z4,z109,z6]),(0,[z31,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z475,z29,z4,z6])],[(0,[z1,z2,z3,z4,z5,z476,z6]),(0,[z1,z2,z3,z60,z4,z5,z189]),(0,[z477,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z148]),(0,[z1,z2,z3,z478,z29,z4,z6]),(0,[z1,z2,z479,z3,z4,z5,z6])],[(0,[z44,z1,z2,z3,z4,z5,z6]),(0,[z1,z106,z3,z4,z5,z6,z147]),(0,[z1,z480,z2,z3,z4,z5,z6]),(0,[z1,z2,z481,z3,z4,z5,z6]),(0,[z482,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z189]),(0,[z1,z2,z263,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z483,z5,z6])]],
   [[(0,[z484,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z485,z3,z4,z5,z6]),(0,[z1,z2,z486,z3,z4,z5,z6])],[(0,[z28,z1,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z5,z487,z6]),(0,[z1,z2,z32,z3,z4,z6,z33])],[(0,[z1,z488,z2,z3,z4,z5,z6]),(0,[z204,z1,z2,z116,z4,z5,z6]),(0,[z28,z1,z2,z3,z119,z4,z5]),(0,[z1,z2,z3,z4,z285,z5,z6]),(0,[z1,z36,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z147]),(0,[z1,z2,z11,z3,z4,z5,z148])],[(0,[z489,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z12,z116,z4,z5,z6]),(0,[z28,z1,z2,z183,z3,z4,z5]),(0,[z1,z2,z332,z3,z4,z6,z57])],[(1,[z1,z2,z3,z4,z185,z6]),(0,[z28,z1,z2,z125,z3,z4,z5]),(0,[z28,z1,z2,z3,z4,z5,z95]),(0,[z300,z7,z1,z2,z3,z4,z5]),(0,[z7,z1,z2,z11,z3,z4,z5]),(1,[z1,z2,z3,z316,z5,z6]),(0,[z1,z2,z32,z355,z3,z4,z6])],[],[(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z490,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z491,z5,z6]),(0,[z1,z2,z3,z4,z68,z5,z6]),(0,[z1,z2,z492,z32,z3,z4,z6]),(0,[z1,z2,z3,z153,z5,z18,z6])],[(0,[z1,z2,z3,z4,z5,z63,z6]),(0,[z28,z1,z2,z10,z3,z4,z5]),(1,[z1,z2,z3,z4,z163,z6]),(0,[z1,z2,z493,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z494,z6]),(1,[z1,z55,z3,z4,z5,z147]),(0,[z1,z2,z3,z4,z5,z6,z495]),(0,[z1,z2,z3,z4,z5,z496,z6]),(0,[z1,z2,z67,z3,z119,z5,z6]),(0,[z1,z2,z497,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z498,z4,z5,z6]),(0,[z499,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z500,z5,z6]),(0,[z1,z2,z3,z4,z5,z120,z57])],[(0,[z1,z2,z3,z4,z5,z501,z6]),(0,[z138,z85,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z155,z5,z414]),(1,[z1,z41,z3,z4,z223,z6]),(0,[z1,z2,z3,z502,z4,z5,z6])],[(0,[z503,z1,z2,z3,z4,z5,z6]),(0,[z1,z504,z2,z3,z4,z5,z6]),(1,[z138,z2,z3,z118,z5,z6]),(0,[z505,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z506]),(0,[z1,z2,z32,z3,z29,z5,z6]),(1,[z1,z2,z3,z4,z5,z296]),(0,[z1,z2,z3,z4,z5,z6,z507]),(0,[z1,z2,z3,z4,z5,z6,z57])],[(0,[z80,z2,z106,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z51,z76,z6]),(0,[z1,z2,z3,z4,z5,z6,z508]),(0,[z28,z1,z2,z3,z4,z5,z146]),(0,[z1,z2,z3,z4,z509,z5,z6]),(0,[z1,z2,z510,z3,z4,z5,z6])],[(0,[z138,z1,z2,z3,z118,z5,z6]),(0,[z1,z2,z3,z511,z4,z5,z6]),(0,[z1,z2,z3,z4,z512,z5,z6]),(0,[z1,z2,z183,z3,z4,z78,z6]),(0,[z513,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z514,z5,z6]),(0,[z248,z2,z3,z4,z5,z6,z57])],[(0,[z515,z1,z2,z3,z4,z5,z6]),(0,[z24,z1,z2,z32,z3,z4,z6]),(1,[z28,z1,z2,z3,z4,z5]),(1,[z1,z79,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z37,z4,z5]),(0,[z516,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z517,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z518,z6]),(1,[z1,z2,z32,z3,z4,z33]),(0,[z1,z2,z3,z29,z519,z4,z6])],[(0,[z310,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z520,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z521,z5,z6]),(0,[z1,z2,z32,z3,z5,z62,z6])]],
   [[(0,[z1,z2,z3,z4,z522,z5,z6])],[(0,[z523,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z524,z3,z4,z5,z6]),(0,[z1,z525,z2,z3,z4,z5,z6]),(0,[z1,z526,z2,z3,z4,z5,z6]),(0,[z7,z7,z1,z2,z3,z4,z5]),(0,[z1,z2,z527,z3,z4,z5,z6]),(0,[z1,z41,z3,z4,z223,z5,z6]),(0,[z1,z2,z183,z3,z29,z4,z6]),(0,[z1,z2,z32,z3,z4,z5,z33])],[(0,[z528,z1,z2,z3,z4,z5,z6]),(1,[z1,z36,z3,z4,z52,z6]),(0,[z1,z55,z2,z32,z3,z4,z6]),(0,[z1,z2,z32,z3,z4,z6,z147]),(1,[z1,z2,z165,z3,z4,z6]),(0,[z1,z2,z3,z203,z5,z6,z57]),(0,[z1,z2,z3,z4,z5,z529,z6])],[(0,[z530,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z531,z3,z4,z5,z6]),(0,[z532,z1,z2,z3,z4,z5,z6]),(0,[z499,z7,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z533,z6]),(0,[z1,z2,z3,z4,z5,z18,z147]),(0,[z1,z2,z3,z4,z219,z5,z6]),(0,[z1,z2,z3,z5,z95,z6,z289])],[(0,[z1,z2,z3,z4,z534,z5,z6]),(0,[z1,z2,z149,z3,z4,z5,z6]),(0,[z28,z138,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z148]),(0,[z1,z2,z3,z4,z535,z5,z6]),(0,[z1,z2,z3,z29,z4,z6,z57]),(0,[z1,z2,z3,z29,z203,z5,z6]),(0,[z1,z2,z3,z4,z536,z5,z6])],[(0,[z2,z106,z3,z97,z4,z5,z6]),(0,[z537,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z349]),(0,[z1,z2,z3,z4,z538,z5,z6]),(0,[z28,z1,z79,z3,z4,z5,z6])],[(0,[z1,z539,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z540,z6])],[(0,[z7,z1,z2,z106,z3,z4,z5]),(0,[z1,z2,z3,z153,z60,z5,z6]),(0,[z28,z1,z2,z3,z156,z4,z5]),(0,[z7,z1,z2,z3,z4,z5,z135]),(0,[z1,z2,z3,z4,z5,z6,z541]),(0,[z1,z2,z11,z4,z5,z6,z148])]],
   [[(0,[z204,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z542,z6]),(0,[z191,z1,z3,z4,z5,z111,z6]),(0,[z1,z2,z3,z4,z5,z543,z6])],[(0,[z544,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z545,z6]),(1,[z1,z2,z3,z4,z301,z6]),(1,[z1,z2,z340,z3,z4,z6]),(0,[z1,z2,z103,z3,z4,z5,z6]),(0,[z1,z2,z12,z3,z4,z5,z6]),(0,[z546,z1,z2,z3,z4,z5,z6])],[(0,[z28,z204,z1,z2,z3,z4,z5]),(0,[z1,z2,z547,z3,z4,z5,z6]),(0,[z1,z2,z548,z3,z4,z5,z6]),(0,[z310,z7,z1,z2,z3,z4,z5]),(0,[z549,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z550,z6]),(0,[z1,z2,z551,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z552,z6]),(0,[z1,z2,z32,z3,z4,z6,z57])],[(0,[z1,z2,z553,z3,z4,z5,z6]),(0,[z28,z85,z1,z2,z3,z4,z5]),(0,[z7,z1,z2,z3,z4,z5,z18]),(0,[z9,z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z554,z4,z5,z6]),(0,[z1,z2,z3,z4,z317,z5,z6]),(0,[z1,z2,z555,z3,z4,z5,z6])],[(0,[z65,z1,z2,z3,z4,z5,z6]),(1,[z369,z2,z3,z4,z5,z6]),(0,[z556,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z557,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z558,z6]),(0,[z1,z2,z32,z56,z3,z4,z6]),(1,[z1,z2,z3,z29,z203,z6])],[(1,[z1,z2,z3,z4,z5,z42]),(0,[z559,z1,z2,z3,z4,z5,z6]),(0,[z528,z7,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z317,z6]),(0,[z560,z1,z2,z3,z4,z5,z6]),(0,[z117,z1,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z236,z4,z5,z6]),(0,[z1,z2,z3,z561,z4,z5,z6])],[(0,[z72,z1,z80,z3,z4,z5,z6]),(0,[z139,z1,z2,z3,z29,z4,z6]),(0,[z1,z80,z3,z4,z5,z6,z147]),(1,[z7,z1,z2,z32,z3,z4]),(0,[z1,z562,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z271]),(0,[z1,z2,z3,z4,z5,z6,z563]),(0,[z1,z2,z3,z4,z564,z5,z6]),(0,[z1,z565,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z566]),(0,[z1,z2,z3,z4,z5,z567,z6]),(0,[z1,z2,z3,z4,z5,z406,z6])],[(0,[z568,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z569,z5,z6]),(1,[z1,z2,z3,z4,z5,z188]),(0,[z2,z3,z60,z4,z118,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z76]),(0,[z9,z1,z112,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z6,z19]),(0,[z1,z2,z3,z4,z5,z6,z570])]],
   [[(0,[z1,z2,z3,z4,z5,z571,z6]),(0,[z1,z2,z3,z49,z4,z5,z6]),(0,[z572,z1,z2,z3,z4,z5,z6]),(0,[z573,z1,z2,z3,z4,z5,z6]),(0,[z574,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z223,z5,z6])],[(0,[z1,z319,z2,z3,z4,z5,z6]),(0,[z90,z1,z2,z3,z4,z5,z6]),(0,[z1,z575,z2,z3,z4,z5,z6]),(1,[z1,z2,z375,z3,z4,z5]),(0,[z1,z142,z2,z3,z4,z5,z6]),(0,[z576,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z324,z6]),(0,[z1,z2,z577,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z578,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z579])],[(0,[z1,z2,z32,z3,z97,z4,z6]),(0,[z1,z2,z3,z580,z4,z5,z6]),(0,[z1,z2,z32,z75,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z581,z6]),(0,[z1,z2,z3,z582,z4,z5,z6])],[(0,[z1,z2,z3,z4,z583,z5,z6]),(0,[z204,z7,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z109,z5,z6]),(1,[z1,z2,z3,z4,z329,z6])],[(0,[z35,z7,z1,z2,z3,z4,z5]),(0,[z584,z1,z2,z3,z4,z5,z6])],[(0,[z484,z28,z1,z2,z3,z4,z5]),(0,[z28,z1,z2,z103,z3,z4,z5]),(0,[z7,z1,z2,z3,z16,z4,z5]),(0,[z1,z2,z340,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z120])],[(0,[z1,z2,z585,z3,z4,z5,z6]),(0,[z1,z36,z2,z3,z29,z4,z6]),(0,[z586,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z76,z6])],[(0,[z7,z1,z2,z3,z60,z4,z5]),(0,[z1,z2,z3,z4,z587,z5,z6]),(1,[z1,z2,z3,z107,z5,z6]),(0,[z1,z112,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z588,z6]),(0,[z1,z2,z3,z4,z589,z5,z6]),(0,[z1,z2,z12,z3,z4,z5,z148]),(0,[z590,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z591,z3,z4,z5,z6])]],
   [[(0,[z2,z116,z3,z97,z4,z5,z6]),(0,[z1,z2,z3,z4,z592,z5,z6]),(0,[z1,z2,z3,z4,z51,z6,z135]),(0,[z28,z1,z2,z3,z4,z5,z132]),(0,[z7,z1,z2,z3,z4,z203,z5]),(0,[z1,z2,z593,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z594,z5,z6]),(0,[z1,z142,z2,z119,z4,z5,z6]),(0,[z1,z2,z595,z3,z4,z5,z6])],[(0,[z28,z24,z1,z2,z3,z4,z5]),(0,[z28,z1,z112,z2,z3,z4,z5]),(1,[z191,z1,z3,z4,z5,z111]),(0,[z1,z2,z3,z4,z5,z6,z596])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z597,z6]),(0,[z7,z1,z2,z3,z4,z223,z5]),(0,[z1,z2,z32,z3,z153,z5,z6])],[(0,[z1,z2,z3,z598,z4,z5,z6]),(0,[z85,z2,z3,z60,z4,z5,z6]),(0,[z572,z7,z1,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z5,z200,z6]),(0,[z1,z2,z3,z29,z4,z4,z6])],[(0,[z204,z1,z2,z97,z4,z5,z6]),(0,[z1,z2,z168,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z200]),(0,[z1,z112,z2,z3,z4,z5,z201]),(0,[z1,z2,z3,z4,z599,z5,z6]),(0,[z248,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z334])],[(0,[z600,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z132,z6]),(0,[z1,z2,z3,z54,z4,z5,z6]),(0,[z1,z2,z601,z3,z4,z5,z6]),(0,[z1,z2,z67,z3,z4,z324,z6])],[(0,[z1,z2,z602,z3,z4,z5,z6]),(0,[z1,z2,z603,z3,z4,z5,z6]),(0,[z1,z2,z119,z4,z38,z5,z6])],[(0,[z1,z2,z604,z3,z4,z5,z6]),(0,[z1,z2,z3,z475,z4,z5,z6]),(0,[z1,z2,z3,z4,z155,z76,z6])]],
   [[(0,[z1,z2,z3,z4,z605,z5,z6]),(0,[z1,z2,z3,z4,z5,z606,z6]),(0,[z1,z2,z3,z8,z4,z5,z6]),(0,[z1,z128,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z4,z326,z38,z6]),(0,[z1,z2,z3,z478,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z76,z6]),(0,[z1,z2,z32,z3,z4,z296,z6])],[(0,[z24,z1,z2,z3,z29,z4,z6]),(0,[z28,z1,z2,z11,z3,z4,z5]),(0,[z1,z2,z3,z29,z4,z109,z6]),(0,[z607,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z534,z6]),(0,[z1,z319,z2,z106,z3,z4,z5]),(0,[z1,z2,z3,z4,z608,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z138,z1,z2,z32,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z78,z5]),(0,[z7,z1,z2,z3,z4,z94,z5]),(0,[z1,z2,z609,z3,z4,z5,z6])],[(0,[z72,z1,z2,z3,z4,z534,z6]),(0,[z1,z2,z48,z3,z4,z5,z6]),(0,[z1,z2,z3,z610,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z414]),(0,[z28,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z37,z4,z6]),(0,[z1,z2,z3,z4,z611,z5,z6])],[(0,[z310,z28,z1,z2,z3,z4,z5]),(0,[z1,z142,z10,z3,z4,z5,z6]),(0,[z1,z612,z2,z3,z4,z5,z6])],[(1,[z7,z1,z2,z3,z29,z4]),(0,[z43,z1,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z613])],[(0,[z1,z2,z3,z4,z5,z614,z6]),(0,[z85,z1,z2,z3,z203,z5,z6]),(1,[z7,z1,z2,z3,z4,z5]),(0,[z1,z2,z615,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z616,z6]),(0,[z1,z2,z3,z4,z617,z5,z6]),(0,[z1,z55,z2,z3,z29,z4,z6]),(0,[z191,z1,z2,z32,z3,z4,z6]),(0,[z1,z618,z2,z3,z4,z5,z6]),(0,[z619,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z620,z5,z6])],[(0,[z1,z2,z621,z3,z4,z5,z6]),(0,[z72,z7,z1,z2,z3,z4,z5]),(0,[z1,z622,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z623,z6]),(1,[z1,z2,z3,z4,z314,z6]),(0,[z1,z2,z3,z624,z4,z5,z6]),(0,[z7,z1,z2,z3,z29,z4,z5]),(0,[z1,z2,z32,z3,z4,z38,z6]),(0,[z1,z625,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z153,z203,z5,z6])]],
   [[(0,[z1,z2,z3,z626,z4,z5,z6]),(1,[z28,z1,z2,z32,z3,z4]),(0,[z1,z112,z2,z3,z29,z4,z6]),(0,[z1,z2,z627,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z628,z5,z6])],[(0,[z1,z2,z3,z629,z4,z5,z6]),(0,[z1,z630,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z120,z6,z148]),(0,[z1,z74,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z631,z4,z5,z6])],[(0,[z537,z28,z1,z2,z3,z4,z5]),(0,[z28,z1,z2,z3,z37,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z632]),(0,[z633,z1,z2,z3,z4,z5,z6])],[(0,[z28,z191,z1,z2,z3,z4,z5])],[(0,[z1,z2,z368,z3,z4,z118,z6]),(0,[z1,z2,z3,z4,z5,z634,z6]),(0,[z1,z2,z3,z635,z4,z5,z6]),(0,[z1,z2,z358,z3,z4,z5,z6])],[(0,[z1,z636,z2,z3,z4,z5,z6]),(0,[z637,z1,z2,z3,z4,z5,z6]),(0,[z411,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z223,z155,z6]),(0,[z1,z2,z3,z29,z119,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6,z638]),(0,[z639,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z640,z4,z5,z6]),(0,[z1,z302,z2,z3,z4,z5,z6])]],
   [[(0,[z641,z1,z2,z3,z4,z5,z6]),(0,[z642,z1,z2,z3,z4,z5,z6]),(0,[z204,z1,z2,z3,z4,z436,z6]),(0,[z643,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z644])],[(0,[z1,z2,z3,z645,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z118,z6]),(0,[z1,z2,z282,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z148]),(0,[z1,z2,z3,z4,z5,z6,z646]),(0,[z1,z2,z3,z4,z647,z5,z6])],[(0,[z1,z41,z2,z32,z3,z4,z6]),(0,[z1,z2,z648,z3,z4,z5,z6]),(0,[z1,z2,z649,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z650,z5,z6]),(1,[z1,z2,z293,z3,z4,z5]),(0,[z451,z7,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z651]),(0,[z1,z2,z32,z3,z4,z111,z6]),(0,[z1,z2,z32,z67,z3,z4,z6]),(0,[z1,z2,z183,z3,z4,z5,z6]),(1,[z1,z2,z332,z3,z4,z6])],[(0,[z28,z1,z2,z106,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z652,z6]),(1,[z1,z2,z3,z4,z5,z20]),(1,[z28,z1,z15,z3,z4,z5]),(0,[z1,z2,z3,z4,z346,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z135]),(0,[z1,z653,z2,z3,z4,z5,z6]),(0,[z654,z1,z2,z3,z4,z5,z6])],[(0,[z28,z1,z2,z3,z346,z5,z6]),(0,[z1,z2,z655,z3,z4,z5,z6]),(0,[z1,z2,z3,z656,z4,z5,z6])],[(0,[z7,z1,z2,z116,z3,z4,z5]),(0,[z1,z2,z3,z4,z163,z5,z6]),(0,[z1,z2,z32,z125,z3,z4,z6])],[(0,[z1,z2,z657,z3,z4,z5,z6]),(0,[z1,z2,z3,z658,z4,z5,z6]),(1,[z28,z1,z79,z3,z4,z5]),(0,[z1,z2,z3,z153,z4,z5,z57])]],
   [[(0,[z72,z139,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z18]),(0,[z659,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z95,z6])],[(0,[z660,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z2,z32,z3,z4,z6]),(0,[z1,z2,z32,z10,z3,z4,z6]),(0,[z1,z2,z3,z661,z4,z5,z6]),(0,[z1,z2,z662,z3,z4,z5,z6]),(0,[z1,z2,z663,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z664,z5,z6])],[(0,[z1,z2,z103,z3,z4,z5,z254])],[(0,[z1,z2,z3,z4,z155,z5,z6]),(0,[z1,z2,z3,z4,z5,z216,z6]),(1,[z1,z2,z75,z4,z78,z6])],[(0,[z72,z1,z106,z3,z4,z5,z6]),(0,[z1,z665,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z155,z6,z135]),(0,[z28,z1,z2,z3,z4,z5,z76]),(0,[z7,z1,z2,z3,z4,z5,z62]),(0,[z1,z666,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z146]),(0,[z1,z2,z667,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z4,z5,z216]),(0,[z1,z2,z3,z4,z668,z5,z6])],[(1,[z72,z106,z3,z4,z5,z6]),(0,[z90,z1,z2,z116,z4,z5,z6]),(0,[z7,z1,z2,z3,z54,z4,z5]),(0,[z1,z2,z396,z3,z4,z5,z6]),(0,[z669,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z116,z3,z4,z5,z349]),(1,[z28,z1,z2,z3,z29,z4]),(0,[z1,z2,z3,z4,z5,z200,z6]),(0,[z1,z2,z3,z4,z78,z5,z6]),(0,[z1,z2,z670,z3,z4,z5,z6]),(0,[z1,z671,z2,z3,z4,z5,z6])]],
   [[(0,[z139,z1,z2,z3,z4,z5,z6]),(0,[z138,z1,z2,z3,z203,z5,z6]),(0,[z7,z1,z142,z2,z3,z4,z5]),(0,[z7,z1,z2,z3,z4,z5,z52]),(0,[z1,z2,z3,z29,z4,z223,z6]),(0,[z1,z2,z3,z4,z5,z672,z6])],[(0,[z489,z7,z1,z2,z3,z4,z5]),(0,[z1,z2,z103,z4,z38,z5,z6])],[(0,[z1,z2,z3,z673,z4,z5,z6]),(0,[z1,z2,z674,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z675,z5,z6]),(0,[z600,z28,z1,z2,z3,z4,z5]),(0,[z28,z1,z2,z3,z4,z163,z6]),(0,[z369,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z676]),(0,[z1,z260,z2,z32,z3,z4,z6])],[(1,[z1,z2,z3,z4,z436,z6]),(0,[z1,z2,z3,z4,z677,z5,z6]),(0,[z1,z2,z3,z4,z78,z223,z6]),(0,[z1,z172,z2,z3,z29,z4,z6]),(0,[z1,z2,z678,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z679]),(0,[z1,z680,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z681]),(0,[z1,z2,z3,z4,z5,z682,z6]),(0,[z1,z2,z683,z3,z4,z5,z6]),(0,[z1,z2,z428,z32,z3,z4,z6]),(0,[z1,z684,z2,z3,z4,z5,z6])],[(0,[z28,z1,z2,z3,z4,z203,z5]),(0,[z1,z2,z3,z685,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z686,z6]),(0,[z1,z687,z2,z3,z4,z5,z6])],[(1,[z1,z2,z282,z3,z5,z6]),(0,[z28,z2,z3,z4,z5,z6,z146]),(0,[z7,z1,z41,z2,z3,z4,z5]),(0,[z1,z688,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z689,z5,z6]),(0,[z1,z2,z3,z4,z690,z5,z6]),(0,[z28,z1,z2,z3,z4,z223,z5]),(0,[z1,z2,z3,z29,z4,z6,z146]),(0,[z7,z1,z2,z3,z153,z4,z5]),(0,[z1,z2,z3,z4,z691,z5,z6]),(0,[z1,z692,z2,z3,z4,z5,z6])]],
   [[(0,[z28,z28,z1,z2,z3,z4,z5]),(0,[z1,z36,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z693,z6]),(0,[z1,z2,z694,z3,z4,z5,z6]),(0,[z1,z695,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z78,z6]),(0,[z1,z2,z3,z29,z4,z94,z6])],[(0,[z1,z2,z696,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z200,z6]),(0,[z9,z240,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z697,z5,z6]),(0,[z1,z41,z2,z3,z4,z223,z6]),(0,[z1,z2,z698,z3,z4,z5,z6]),(0,[z1,z2,z3,z519,z4,z5,z6])],[(0,[z1,z2,z699,z3,z4,z5,z6]),(0,[z700,z1,z2,z3,z4,z5,z6]),(0,[z701,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z702,z3,z4,z5,z6]),(0,[z191,z1,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z29,z4,z336,z6]),(0,[z1,z2,z3,z5,z18,z6,z57])],[(0,[z139,z7,z1,z2,z3,z4,z5]),(0,[z515,z7,z1,z2,z3,z4,z5]),(0,[z1,z10,z3,z54,z4,z5,z6]),(0,[z1,z703,z2,z3,z4,z5,z6]),(0,[z1,z112,z2,z3,z109,z5,z6]),(0,[z1,z2,z3,z152,z4,z5,z6]),(0,[z1,z2,z56,z3,z153,z5,z6]),(0,[z1,z2,z56,z3,z4,z5,z57])],[(0,[z1,z2,z3,z4,z5,z180,z6]),(0,[z1,z2,z492,z3,z4,z5,z6]),(0,[z1,z2,z375,z3,z4,z5,z6]),(0,[z1,z36,z2,z3,z4,z223,z6]),(1,[z1,z2,z3,z4,z5,z254]),(0,[z1,z2,z3,z4,z704,z5,z6])],[(0,[z1,z2,z3,z4,z5,z270,z6]),(0,[z1,z112,z2,z3,z4,z5,z271]),(0,[z1,z2,z3,z29,z29,z4,z6])],[(0,[z1,z2,z3,z4,z5,z185,z6]),(0,[z1,z2,z3,z4,z5,z705,z6]),(0,[z1,z2,z103,z3,z4,z5,z102]),(1,[z1,z2,z3,z4,z68,z6])],[(0,[z28,z1,z2,z3,z4,z78,z5]),(0,[z28,z1,z2,z3,z4,z94,z5]),(0,[z1,z2,z3,z706,z4,z5,z6]),(0,[z1,z2,z214,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z292])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z204,z2,z97,z4,z205,z6])],[],[(0,[z1,z2,z368,z3,z49,z4]),(0,[z1,z2,z3,z5,z6,z707]),(0,[z28,z2,z3,z4,z5,z146]),(0,[z7,z1,z41,z3,z4,z223]),(0,[z1,z2,z32,z3,z348,z6])],[(0,[z1,z2,z708,z3,z4,z6]),(0,[z1,z2,z149,z3,z4,z5]),(0,[z28,z2,z3,z60,z4,z163]),(0,[z1,z112,z3,z29,z109,z6]),(0,[z1,z709,z2,z3,z4,z5])],[(0,[z1,z710,z3,z4,z5,z6]),(0,[z1,z2,z3,z316,z30,z6]),(0,[z711,z2,z3,z4,z5,z6])],[(0,[z1,z2,z156,z4,z5,z6]),(0,[z1,z2,z3,z4,z51,z33]),(0,[z1,z2,z214,z38,z5,z6]),(0,[z1,z2,z474,z4,z5,z120])],[(0,[z204,z2,z48,z97,z4,z5]),(0,[z1,z2,z3,z4,z712,z6]),(0,[z43,z1,z2,z32,z3,z6]),(0,[z713,z1,z2,z32,z3,z4]),(0,[z1,z2,z3,z346,z132,z6]),(0,[z1,z2,z3,z4,z5,z714])],[(0,[z191,z1,z3,z4,z5,z180]),(0,[z28,z15,z3,z60,z4,z5]),(0,[z1,z2,z3,z4,z5,z715]),(0,[z1,z2,z103,z716,z5,z6])],[(0,[z1,z2,z3,z4,z717,z6]),(0,[z28,z1,z2,z3,z4,z718]),(0,[z1,z2,z4,z78,z719,z6])],[(0,[z139,z80,z3,z4,z5,z180]),(0,[z1,z2,z720,z4,z5,z6]),(0,[z1,z2,z3,z4,z132,z18]),(0,[z1,z2,z3,z4,z721,z6])],[(0,[z1,z2,z3,z4,z722,z6]),(0,[z1,z2,z723,z3,z4,z5]),(0,[z138,z2,z368,z3,z118,z6]),(0,[z1,z2,z3,z724,z4,z6]),(0,[z1,z2,z3,z4,z5,z725]),(0,[z1,z2,z332,z3,z4,z6])],[(0,[z1,z2,z3,z726,z5,z6]),(0,[z1,z727,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z32,z3,z227,z6]),(0,[z1,z2,z32,z3,z95,z57])],[(0,[z1,z2,z3,z4,z6,z728]),(0,[z1,z15,z3,z156,z4,z5]),(0,[z1,z172,z3,z4,z52,z6]),(0,[z499,z248,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z729,z6]),(0,[z28,z1,z79,z3,z29,z4]),(0,[z1,z2,z3,z253,z346,z5]),(0,[z7,z1,z128,z3,z37,z5]),(0,[z1,z10,z730,z4,z5,z6]),(0,[z1,z2,z183,z4,z76,z6])],[(0,[z1,z2,z3,z4,z731,z6]),(0,[z28,z1,z79,z3,z4,z5]),(0,[z28,z1,z2,z3,z152,z4]),(0,[z1,z2,z3,z203,z6,z292]),(0,[z1,z2,z3,z4,z732,z135])],[(0,[z1,z2,z3,z4,z733,z6]),(0,[z1,z2,z12,z4,z5,z188]),(0,[z1,z2,z3,z4,z5,z734]),(0,[z1,z2,z3,z735,z62,z6])]],
   [[(0,[z1,z2,z3,z4,z736,z6])],[(0,[z1,z2,z3,z737,z4,z5])],[(0,[z1,z2,z168,z253,z5,z6]),(0,[z451,z1,z2,z3,z4,z270]),(0,[z1,z2,z738,z3,z4,z6]),(0,[z739,z2,z3,z4,z5,z6]),(0,[z1,z2,z75,z4,z78,z6])],[(0,[z28,z1,z2,z3,z107,z5]),(0,[z1,z2,z32,z3,z567,z6])],[(0,[z1,z2,z355,z3,z4,z33])],[(0,[z72,z106,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z740]),(0,[z1,z2,z3,z29,z370,z6])],[(0,[z28,z499,z2,z3,z4,z5]),(0,[z607,z2,z3,z60,z5,z6]),(0,[z28,z1,z2,z3,z4,z741]),(0,[z484,z1,z79,z3,z4,z5]),(0,[z1,z2,z156,z29,z4,z6]),(0,[z1,z2,z3,z4,z5,z742]),(0,[z1,z2,z56,z332,z3,z57])],[(0,[z1,z2,z32,z3,z4,z414]),(0,[z1,z2,z3,z4,z94,z20]),(0,[z1,z2,z743,z3,z4,z5])],[(0,[z24,z2,z3,z4,z51,z6]),(0,[z28,z7,z2,z3,z346,z5]),(0,[z28,z1,z3,z4,z219,z5]),(0,[z1,z2,z3,z4,z296,z135])],[(0,[z28,z2,z3,z447,z4,z5]),(0,[z28,z1,z2,z744,z4,z5]),(0,[z1,z2,z3,z4,z5,z745]),(0,[z1,z2,z183,z4,z719,z6])],[(1,[z1,z2,z4,z5,z746]),(0,[z747,z2,z3,z4,z5,z6])],[(0,[z90,z2,z116,z4,z5,z349]),(0,[z1,z2,z3,z748,z4,z5]),(0,[z1,z2,z3,z4,z346,z132]),(0,[z191,z1,z396,z3,z4,z5]),(0,[z1,z3,z4,z219,z5,z6]),(0,[z1,z2,z332,z3,z4,z135])],[(0,[z72,z106,z3,z4,z534,z6]),(0,[z1,z2,z3,z4,z5,z749]),(0,[z138,z7,z1,z2,z32,z3])],[(0,[z204,z2,z149,z97,z4,z5]),(0,[z1,z2,z3,z29,z4,z349]),(0,[z1,z2,z282,z3,z5,z6]),(0,[z28,z1,z2,z750,z4,z5]),(0,[z28,z1,z2,z3,z751,z5]),(0,[z1,z3,z4,z5,z752,z6]),(0,[z1,z2,z32,z3,z62,z33])],[(0,[z1,z2,z753,z3,z4,z5]),(0,[z1,z2,z754,z3,z4,z6]),(0,[z1,z2,z282,z3,z6,z135]),(0,[z1,z2,z4,z5,z6,z755]),(0,[z234,z1,z3,z4,z5,z111])],[(0,[z1,z2,z32,z3,z4,z180]),(0,[z85,z1,z2,z32,z3,z6]),(0,[z1,z2,z3,z5,z6,z756]),(0,[z1,z2,z3,z4,z757,z6]),(0,[z1,z302,z32,z3,z4,z6])]],
   [[(0,[z1,z2,z758,z3,z4,z5]),(0,[z1,z112,z3,z109,z5,z6])],[(0,[z72,z319,z106,z3,z4,z5]),(0,[z1,z2,z282,z3,z131,z5]),(0,[z600,z1,z2,z168,z4,z5]),(0,[z28,z2,z3,z4,z163,z146])],[(0,[z28,z1,z2,z3,z4,z329]),(0,[z1,z2,z3,z58,z94,z95])],[(0,[z28,z138,z2,z3,z346,z5]),(0,[z28,z1,z2,z3,z759,z5]),(0,[z1,z2,z3,z760,z5,z6]),(0,[z1,z2,z3,z4,z5,z761]),(0,[z1,z2,z67,z29,z119,z6])],[(0,[z1,z59,z15,z3,z4,z5]),(0,[z1,z2,z156,z4,z163,z6]),(0,[z1,z2,z32,z3,z697,z6]),(0,[z1,z2,z32,z762,z4,z6])],[(0,[z1,z2,z293,z3,z73,z4]),(0,[z1,z112,z3,z109,z5,z201]),(0,[z1,z2,z3,z4,z68,z6])],[(0,[z28,z2,z3,z60,z346,z5]),(0,[z1,z269,z3,z4,z52,z6]),(0,[z9,z1,z54,z4,z5,z182])],[(0,[z24,z2,z355,z3,z4,z6]),(0,[z1,z2,z375,z3,z107,z5]),(0,[z28,z79,z3,z4,z5,z146]),(0,[z1,z2,z3,z4,z5,z763]),(0,[z1,z2,z3,z4,z5,z764]),(0,[z1,z2,z3,z4,z765,z6])],[(0,[z248,z2,z3,z4,z5,z6]),(0,[z1,z2,z766,z3,z4,z6]),(0,[z1,z112,z3,z767,z5,z6]),(0,[z1,z2,z32,z3,z113,z6]),(0,[z1,z768,z2,z32,z3,z4])],[(0,[z1,z2,z282,z3,z94,z6]),(0,[z560,z7,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z769])],[(0,[z1,z2,z3,z4,z5,z770]),(0,[z28,z2,z168,z60,z4,z5]),(0,[z1,z2,z3,z4,z163,z20]),(0,[z1,z79,z156,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z182]),(0,[z1,z2,z214,z29,z4,z6])],[(0,[z1,z2,z771,z4,z5,z6]),(0,[z2,z772,z3,z4,z5,z6]),(0,[z138,z2,z3,z29,z118,z6]),(0,[z1,z2,z3,z156,z346,z5])],[(0,[z1,z773,z3,z4,z5,z6]),(0,[z1,z2,z32,z282,z3,z6])],[(0,[z138,z7,z2,z3,z118,z5]),(0,[z1,z2,z3,z285,z5,z216]),(0,[z1,z2,z3,z774,z5,z6]),(0,[z1,z2,z3,z4,z775,z6])],[(0,[z1,z2,z48,z3,z29,z4]),(0,[z1,z2,z3,z49,z29,z4]),(0,[z9,z1,z54,z316,z5,z6]),(0,[z1,z2,z437,z32,z3,z6]),(0,[z1,z2,z3,z4,z776,z6])],[(0,[z1,z2,z3,z49,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z777,z6]),(0,[z1,z2,z32,z657,z3,z6]),(0,[z1,z2,z3,z751,z5,z6]),(1,[z1,z2,z3,z346,z132]),(0,[z1,z778,z3,z4,z5,z6]),(0,[z1,z2,z421,z4,z336,z6])],[(0,[z1,z2,z3,z4,z63,z6]),(0,[z1,z2,z3,z4,z5,z779]),(0,[z28,z1,z2,z3,z4,z314]),(0,[z337,z1,z2,z3,z4,z163]),(0,[z1,z3,z29,z4,z219,z6])],[(0,[z1,z2,z3,z4,z5,z780]),(0,[z1,z781,z3,z4,z5,z6]),(0,[z1,z2,z3,z131,z107,z5]),(0,[z1,z2,z3,z29,z253,z6]),(0,[z782,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z444,z5,z18]),(0,[z1,z2,z32,z3,z4,z783]),(0,[z1,z2,z3,z4,z193,z296])],[(0,[z1,z2,z3,z784,z5,z6]),(0,[z28,z138,z2,z32,z3,z5]),(0,[z785,z1,z2,z3,z4,z5]),(0,[z1,z2,z183,z236,z4,z6])],[(0,[z1,z2,z3,z786,z5,z6]),(0,[z28,z204,z2,z97,z4,z5]),(0,[z1,z2,z787,z3,z4,z6]),(0,[z1,z2,z3,z788,z5,z6]),(0,[z28,z24,z2,z3,z4,z51]),(0,[z28,z1,z2,z789,z3,z346]),(0,[z1,z2,z232,z3,z5,z57])],[(0,[z1,z128,z3,z37,z329,z6])],[(0,[z1,z2,z790,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z131]),(0,[z1,z15,z3,z4,z5,z148]),(0,[z1,z2,z3,z316,z5,z216]),(0,[z1,z2,z791,z3,z4,z5]),(0,[z248,z2,z32,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z289])],[(0,[z1,z2,z3,z4,z5,z792]),(0,[z1,z2,z3,z73,z4,z6]),(0,[z28,z1,z793,z3,z4,z5]),(0,[z7,z1,z2,z3,z152,z4]),(0,[z1,z2,z103,z38,z5,z6])],[(0,[z1,z794,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z296])],[(0,[z1,z2,z795,z3,z4,z5]),(0,[z28,z419,z2,z3,z4,z5]),(0,[z28,z1,z2,z3,z29,z203]),(0,[z248,z2,z3,z4,z5,z135])],[(0,[z1,z2,z3,z4,z796,z6]),(0,[z1,z2,z3,z797,z4,z6]),(0,[z1,z15,z3,z346,z5,z6]),(0,[z798,z1,z2,z3,z4,z5]),(0,[z240,z2,z3,z4,z5,z182]),(0,[z1,z2,z3,z4,z799,z6]),(0,[z1,z55,z3,z4,z5,z800]),(0,[z1,z2,z67,z119,z5,z6]),(0,[z1,z801,z32,z3,z4,z6]),(0,[z1,z2,z802,z32,z3,z4])],[(0,[z1,z2,z3,z29,z4,z414]),(0,[z28,z1,z2,z766,z3,z4]),(0,[z1,z2,z11,z156,z4,z5]),(0,[z248,z7,z2,z3,z4,z5]),(0,[z1,z2,z803,z3,z4,z6]),(0,[z1,z2,z3,z4,z804,z6])],[(0,[z1,z2,z3,z4,z5,z805]),(0,[z1,z2,z3,z4,z5,z806]),(0,[z7,z1,z2,z3,z107,z5]),(0,[z1,z2,z3,z807,z5,z6]),(0,[z1,z2,z32,z808,z3,z4]),(0,[z1,z2,z3,z4,z5,z809])],[(0,[z1,z2,z3,z4,z5,z810]),(0,[z28,z7,z2,z3,z4,z5]),(0,[z28,z1,z15,z3,z4,z163]),(0,[z28,z1,z2,z156,z346,z5]),(0,[z1,z15,z3,z4,z5,z18]),(0,[z811,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z812]),(0,[z1,z128,z3,z37,z5,z6]),(0,[z1,z813,z2,z3,z4,z5])],[(0,[z1,z2,z548,z4,z76,z6]),(0,[z1,z79,z15,z3,z4,z5]),(0,[z1,z2,z3,z814,z4,z6]),(0,[z1,z2,z4,z5,z719,z6])],[(0,[z1,z2,z168,z4,z5,z188]),(0,[z1,z2,z815,z3,z4,z5]),(0,[z1,z2,z3,z4,z816,z6])]],
   [[(0,[z7,z1,z2,z168,z4,z5]),(0,[z1,z79,z3,z4,z5,z111])],[(0,[z28,z2,z3,z4,z5,z189]),(0,[z28,z1,z2,z3,z346,z132]),(0,[z7,z1,z3,z4,z219,z5])],[(0,[z1,z2,z32,z3,z608,z6]),(0,[z1,z2,z32,z817,z3,z6]),(0,[z240,z2,z3,z316,z5,z6]),(0,[z1,z2,z32,z3,z6,z57])],[(0,[z204,z2,z97,z4,z5,z6]),(0,[z9,z1,z54,z4,z301,z6]),(0,[z1,z302,z3,z29,z4,z6])],[(0,[z28,z1,z112,z3,z109,z5]),(0,[z818,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z819,z4,z6]),(0,[z1,z2,z214,z32,z4,z6])],[(0,[z1,z2,z149,z3,z29,z4]),(0,[z1,z2,z368,z3,z6,z57]),(0,[z1,z2,z820,z3,z4,z6]),(0,[z821,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z58,z5,z6])],[(0,[z1,z2,z3,z4,z822,z6]),(0,[z138,z104,z2,z32,z3,z6]),(1,[z1,z3,z4,z5,z800]),(0,[z1,z2,z3,z58,z6,z135])],[(0,[z1,z823,z3,z4,z5,z6]),(0,[z1,z2,z3,z824,z5,z6]),(0,[z99,z1,z15,z3,z4,z5]),(0,[z9,z1,z21,z4,z5,z6]),(0,[z1,z2,z3,z152,z4,z6]),(0,[z1,z2,z11,z4,z5,z746])],[(0,[z28,z138,z2,z3,z4,z5]),(0,[z7,z1,z2,z32,z3,z29]),(0,[z1,z2,z3,z4,z5,z825])],[(0,[z1,z2,z3,z4,z5,z826]),(0,[z1,z2,z32,z3,z624,z6]),(0,[z1,z2,z3,z827,z4,z6]),(0,[z1,z2,z32,z3,z153,z296]),(0,[z1,z2,z3,z339,z4,z406]),(0,[z1,z2,z3,z153,z18,z19])],[(0,[z1,z2,z828,z4,z5,z6]),(0,[z1,z2,z829,z4,z5,z6]),(0,[z1,z2,z214,z4,z5,z830]),(0,[z1,z2,z32,z3,z529,z6])],[(0,[z7,z1,z2,z3,z4,z329]),(0,[z1,z2,z3,z4,z301,z216]),(0,[z1,z831,z2,z3,z4,z5])],[(0,[z1,z190,z3,z4,z5,z147]),(0,[z2,z3,z4,z5,z200,z763]),(0,[z367,z2,z3,z475,z4,z6])],[(0,[z28,z1,z2,z3,z4,z324]),(0,[z1,z2,z168,z4,z132,z6])],[(0,[z1,z2,z3,z346,z5,z147]),(1,[z2,z3,z4,z5,z763]),(0,[z1,z2,z4,z5,z6,z832])],[(0,[z1,z2,z3,z4,z5,z349]),(1,[z1,z15,z3,z346,z5]),(0,[z28,z1,z2,z32,z3,z253])]],
   [[(0,[z1,z2,z3,z203,z185,z6])],[(0,[z2,z3,z60,z5,z6,z541]),(0,[z28,z1,z79,z168,z4,z5]),(0,[z833,z1,z2,z3,z4,z5]),(0,[z834,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z58,z94,z6])],[(0,[z1,z835,z3,z4,z5,z6]),(0,[z1,z2,z3,z836,z4,z5])],[(0,[z28,z574,z2,z3,z4,z5])],[(0,[z72,z106,z3,z4,z63,z6]),(0,[z1,z2,z3,z837,z4,z6]),(0,[z204,z2,z97,z29,z4,z6]),(0,[z1,z2,z3,z4,z838,z6]),(0,[z337,z1,z2,z3,z346,z5]),(0,[z28,z1,z2,z3,z724,z346]),(0,[z1,z2,z3,z4,z5,z839]),(0,[z1,z2,z321,z3,z29,z6])],[(0,[z1,z2,z840,z3,z4,z6]),(0,[z1,z2,z125,z3,z4,z132]),(0,[z1,z2,z841,z3,z4,z5])],[(0,[z1,z2,z3,z842,z5,z6]),(0,[z1,z112,z3,z109,z5,z271]),(0,[z1,z2,z3,z4,z843,z6]),(0,[z1,z3,z4,z844,z5,z6]),(0,[z1,z845,z3,z4,z5,z6])],[(0,[z24,z2,z3,z107,z51,z6]),(0,[z240,z2,z3,z4,z301,z6]),(0,[z1,z2,z3,z846,z5,z6]),(0,[z1,z2,z32,z3,z4,z847])],[],[(0,[z1,z2,z3,z4,z848,z6]),(0,[z1,z2,z3,z4,z849,z6]),(0,[z28,z138,z2,z3,z60,z5]),(0,[z28,z1,z2,z168,z29,z4]),(0,[z1,z2,z168,z4,z5,z148]),(0,[z1,z2,z32,z3,z6,z579])],[(0,[z1,z2,z3,z4,z5,z850]),(0,[z7,z1,z2,z3,z4,z314]),(0,[z28,z1,z2,z168,z4,z5]),(0,[z1,z2,z851,z3,z4,z5]),(0,[z2,z3,z4,z6,z292,z334])],[(0,[z28,z453,z2,z3,z4,z5]),(0,[z28,z1,z2,z3,z4,z292]),(0,[z1,z2,z852,z4,z5,z6]),(0,[z1,z2,z32,z3,z29,z6])],[(0,[z1,z2,z3,z4,z853,z6]),(0,[z1,z854,z3,z4,z5,z6]),(0,[z546,z2,z3,z4,z51,z6]),(0,[z1,z2,z214,z4,z5,z6]),(0,[z855,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z746])],[(0,[z1,z2,z3,z4,z856,z6]),(0,[z1,z2,z3,z857,z4,z6]),(0,[z1,z2,z168,z346,z5,z6]),(0,[z1,z2,z3,z4,z858,z6])],[(0,[z35,z2,z3,z4,z155,z414]),(0,[z28,z2,z3,z4,z5,z457])],[(0,[z1,z2,z3,z859,z5,z6]),(0,[z1,z2,z860,z4,z5,z6]),(0,[z28,z1,z2,z3,z861,z4]),(0,[z1,z2,z3,z4,z5,z862])]],
   [[(0,[z1,z2,z3,z346,z5,z120]),(0,[z1,z2,z3,z4,z94,z270])],[(0,[z1,z2,z820,z3,z316,z6])],[(0,[z28,z1,z2,z156,z4,z5]),(0,[z28,z1,z863,z3,z4,z5]),(0,[z28,z1,z2,z32,z3,z29]),(0,[z7,z1,z2,z3,z4,z864]),(0,[z7,z1,z2,z3,z29,z203]),(0,[z1,z2,z3,z4,z865,z6])],[(0,[z1,z2,z3,z4,z866,z6]),(0,[z139,z823,z3,z4,z5,z6])],[(0,[z1,z2,z867,z3,z4,z6]),(0,[z868,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z869,z5])],[(0,[z141,z1,z2,z3,z4,z132]),(0,[z619,z7,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z870]),(0,[z871,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z872])],[(0,[z1,z2,z3,z4,z873,z6]),(0,[z1,z2,z874,z3,z4,z5]),(0,[z875,z2,z32,z3,z4,z6])],[(0,[z1,z2,z3,z876,z5,z6]),(0,[z138,z2,z32,z3,z200,z6])],[(0,[z528,z1,z2,z16,z4,z5]),(0,[z1,z2,z3,z877,z316,z6]),(0,[z1,z878,z2,z3,z4,z5]),(0,[z1,z2,z879,z3,z4,z5])],[(0,[z1,z2,z3,z4,z880,z6])],[(0,[z145,z1,z2,z32,z3,z6]),(0,[z1,z2,z29,z122,z4,z6]),(0,[z1,z692,z3,z4,z5,z111])],[(0,[z139,z197,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z301]),(0,[z1,z612,z3,z4,z5,z147]),(0,[z1,z2,z881,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z882]),(0,[z1,z2,z3,z4,z5,z414]),(0,[z1,z15,z3,z4,z132,z6]),(0,[z7,z1,z112,z3,z109,z5]),(0,[z1,z2,z3,z4,z6,z883])],[(1,[z823,z3,z4,z5,z6]),(0,[z85,z2,z3,z60,z185,z6])],[(0,[z7,z1,z2,z3,z253,z5]),(0,[z28,z1,z854,z3,z4,z5]),(0,[z1,z2,z3,z4,z884,z6]),(0,[z1,z2,z214,z119,z5,z6]),(0,[z1,z2,z3,z4,z885,z5]),(0,[z2,z3,z4,z5,z6,z886])]],
   [[(0,[z204,z2,z772,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z887]),(0,[z28,z79,z3,z60,z4,z5]),(0,[z28,z1,z2,z3,z4,z888]),(0,[z28,z1,z794,z3,z4,z5])],[(0,[z889,z1,z2,z3,z4,z5])],[(0,[z1,z2,z890,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z891]),(0,[z1,z2,z3,z4,z892,z6]),(0,[z1,z893,z3,z4,z5,z6])],[(0,[z1,z2,z894,z4,z5,z6]),(0,[z1,z3,z4,z326,z219,z6]),(0,[z1,z2,z67,z119,z324,z6]),(0,[z1,z895,z32,z3,z4,z6]),(0,[z117,z2,z355,z3,z4,z6])],[(0,[z1,z2,z762,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z180]),(0,[z1,z302,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z661,z6]),(0,[z1,z2,z103,z165,z38,z6]),(0,[z1,z2,z3,z4,z896,z6]),(0,[z1,z2,z56,z3,z292,z57])],[(0,[z1,z2,z3,z253,z5,z6]),(0,[z7,z1,z2,z3,z4,z324]),(0,[z1,z3,z4,z767,z5,z6]),(0,[z1,z2,z11,z29,z4,z148]),(0,[z318,z1,z2,z32,z3,z6]),(0,[z1,z2,z3,z29,z4,z897])],[(0,[z1,z2,z898,z3,z4,z5]),(0,[z28,z7,z79,z3,z4,z5]),(0,[z28,z2,z490,z3,z4,z5]),(0,[z1,z2,z3,z29,z629,z6]),(0,[z1,z2,z12,z4,z5,z120]),(0,[z1,z2,z3,z153,z193,z18])],[(0,[z1,z2,z3,z899,z5,z6]),(0,[z1,z2,z808,z3,z4,z5])],[(0,[z24,z2,z3,z4,z900,z6]),(0,[z901,z2,z3,z4,z5,z6]),(0,[z1,z142,z32,z10,z4,z6]),(0,[z1,z2,z428,z244,z4,z6]),(0,[z248,z2,z3,z153,z4,z5])],[(0,[z28,z139,z80,z3,z4,z5]),(0,[z7,z1,z2,z3,z4,z731])],[(0,[z1,z2,z3,z4,z902,z6]),(0,[z1,z2,z817,z3,z4,z6]),(0,[z7,z143,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z6,z903]),(0,[z1,z302,z119,z4,z5,z6]),(0,[z1,z2,z3,z904,z4,z5])],[(0,[z9,z1,z54,z4,z5,z216]),(0,[z1,z2,z214,z4,z5,z905]),(0,[z1,z302,z3,z37,z5,z6])],[(0,[z28,z1,z2,z3,z4,z185]),(0,[z2,z3,z60,z346,z5,z6]),(0,[z1,z2,z3,z4,z5,z906])],[(0,[z1,z2,z3,z907,z5,z6]),(0,[z138,z1,z2,z32,z3,z6]),(0,[z28,z7,z2,z3,z29,z4]),(0,[z1,z2,z3,z285,z5,z6]),(0,[z1,z2,z3,z908,z5,z6]),(0,[z909,z1,z2,z32,z3,z4]),(0,[z1,z2,z32,z3,z153,z18])]],
   [[(0,[z28,z1,z79,z3,z253,z5]),(0,[z1,z2,z3,z4,z5,z182]),(0,[z910,z2,z3,z4,z5,z6]),(0,[z1,z2,z911,z3,z4,z5]),(0,[z1,z3,z4,z5,z800,z147])],[(0,[z2,z823,z3,z4,z5,z6]),(0,[z28,z556,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z912])],[(0,[z1,z319,z2,z3,z29,z4]),(0,[z28,z138,z79,z3,z4,z5]),(0,[z28,z2,z683,z3,z4,z5]),(0,[z1,z2,z3,z4,z913,z6]),(0,[z1,z2,z3,z227,z5,z18])],[(0,[z1,z319,z2,z3,z4,z5]),(1,[z28,z138,z2,z32,z3]),(0,[z367,z2,z3,z4,z51,z6]),(0,[z28,z1,z2,z3,z4,z193]),(0,[z248,z2,z332,z3,z4,z6])],[(0,[z1,z2,z3,z4,z914,z6]),(0,[z7,z1,z142,z10,z4,z5]),(0,[z7,z1,z2,z3,z4,z292]),(0,[z1,z2,z3,z4,z5,z915])],[],[(0,[z1,z2,z3,z4,z5,z916]),(0,[z1,z2,z3,z29,z4,z180]),(0,[z24,z2,z282,z3,z51,z6]),(0,[z1,z2,z119,z285,z5,z6]),(0,[z1,z2,z3,z4,z326,z6]),(0,[z1,z917,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z918])],[(0,[z28,z1,z2,z3,z4,z68])],[(0,[z28,z1,z2,z3,z4,z63]),(0,[z1,z2,z3,z4,z185,z6]),(0,[z28,z499,z2,z3,z253,z5]),(0,[z7,z1,z2,z32,z3,z62]),(0,[z1,z2,z3,z919,z4,z6]),(0,[z1,z2,z3,z4,z5,z783]),(0,[z1,z2,z920,z3,z4,z5]),(0,[z1,z2,z12,z29,z4,z120])],[(0,[z28,z1,z2,z3,z253,z5]),(0,[z1,z2,z3,z4,z5,z921]),(0,[z1,z2,z3,z4,z6,z292])],[(0,[z28,z138,z2,z3,z29,z4]),(0,[z1,z922,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z254]),(0,[z1,z2,z56,z3,z29,z57])],[(0,[z72,z59,z106,z3,z4,z5]),(0,[z1,z2,z3,z923,z5,z6]),(0,[z7,z1,z2,z156,z4,z5]),(0,[z1,z565,z3,z4,z223,z6])],[(0,[z28,z2,z3,z153,z60,z5])],[(0,[z1,z2,z3,z4,z5,z924]),(0,[z248,z2,z3,z60,z5,z6]),(0,[z9,z1,z258,z4,z5,z6]),(0,[z1,z41,z3,z4,z223,z6])],[(0,[z28,z2,z3,z60,z4,z5]),(0,[z24,z2,z375,z3,z4,z51]),(0,[z9,z1,z54,z4,z30,z6]),(0,[z1,z36,z358,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z925]),(0,[z1,z2,z3,z4,z5,z296])],[(0,[z2,z3,z4,z900,z51,z6]),(0,[z7,z1,z2,z3,z4,z132]),(0,[z2,z56,z3,z5,z334,z57])]],
   [[(0,[z1,z2,z32,z3,z4,z188]),(0,[z1,z801,z3,z4,z5,z6]),(0,[z1,z2,z3,z877,z4,z6]),(0,[z1,z2,z11,z32,z4,z148])],[(0,[z240,z2,z3,z4,z5,z216]),(0,[z1,z2,z3,z29,z4,z182]),(0,[z1,z142,z87,z4,z5,z6])],[(0,[z1,z2,z3,z346,z5,z95]),(0,[z1,z2,z244,z4,z78,z6]),(0,[z1,z2,z32,z3,z4,z926])],[(0,[z28,z1,z2,z828,z4,z5]),(0,[z1,z927,z2,z3,z4,z5]),(0,[z928,z240,z2,z3,z4,z5])],[(0,[z1,z3,z37,z285,z5,z6]),(0,[z1,z2,z3,z4,z929,z6])],[(0,[z28,z1,z2,z930,z3,z253]),(0,[z1,z2,z3,z253,z163,z6]),(0,[z7,z1,z2,z3,z4,z301])],[(0,[z1,z2,z32,z3,z185,z6]),(0,[z1,z2,z3,z4,z30,z216]),(0,[z1,z2,z32,z3,z4,z931]),(0,[z43,z2,z3,z519,z4,z6])],[(0,[z9,z1,z119,z37,z5,z6]),(0,[z1,z2,z32,z3,z6,z292])],[(0,[z1,z2,z4,z5,z932,z6]),(0,[z367,z1,z2,z32,z3,z6])],[(0,[z1,z2,z3,z29,z262,z6]),(0,[z1,z2,z125,z3,z4,z33]),(0,[z1,z2,z84,z3,z4,z195])],[(0,[z1,z2,z3,z4,z5,z933]),(0,[z1,z79,z3,z4,z5,z180]),(0,[z138,z2,z3,z49,z118,z5]),(0,[z28,z2,z3,z4,z514,z5]),(0,[z1,z2,z156,z4,z5,z57]),(0,[z1,z2,z3,z4,z94,z296]),(0,[z1,z2,z3,z29,z4,z934])],[(0,[z1,z2,z3,z935,z4,z6]),(0,[z1,z79,z3,z253,z5,z6]),(0,[z28,z2,z156,z4,z5,z146]),(0,[z1,z2,z936,z4,z5,z6])],[(0,[z24,z2,z3,z4,z131,z51]),(0,[z28,z1,z79,z156,z4,z5]),(0,[z1,z2,z463,z4,z5,z148]),(0,[z1,z2,z3,z5,z6,z937])],[(0,[z7,z2,z32,z3,z4,z200]),(0,[z1,z3,z37,z509,z5,z6])],[(0,[z1,z2,z3,z4,z938,z6]),(0,[z1,z2,z3,z4,z939,z6]),(0,[z28,z1,z142,z10,z4,z5]),(1,[z248,z2,z32,z3,z6])],[(0,[z1,z2,z3,z4,z5,z940]),(0,[z1,z302,z165,z3,z4,z6]),(0,[z1,z2,z3,z29,z4,z296])]],
   [[(0,[z464,z2,z3,z4,z51,z6]),(0,[z28,z1,z79,z3,z4,z132]),(0,[z1,z730,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z941,z6])],[(0,[z1,z2,z32,z3,z62,z6])],[(0,[z138,z2,z3,z73,z118,z6]),(0,[z138,z2,z3,z346,z5,z6]),(0,[z1,z2,z293,z3,z346,z5]),(0,[z28,z1,z2,z32,z3,z62]),(0,[z28,z2,z3,z4,z5,z763]),(0,[z240,z2,z3,z4,z30,z6])],[(0,[z28,z1,z15,z3,z346,z5]),(0,[z28,z1,z2,z32,z168,z4]),(0,[z1,z79,z3,z346,z5,z6])],[(0,[z28,z1,z2,z156,z29,z4])],[(0,[z942,z1,z2,z3,z4,z5])],[],[(0,[z7,z1,z2,z3,z4,z185]),(0,[z28,z1,z2,z282,z3,z5]),(0,[z1,z2,z15,z156,z4,z5])],[(0,[z823,z106,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z5,z446]),(0,[z138,z2,z293,z3,z4,z5]),(0,[z85,z2,z32,z3,z60,z6]),(0,[z1,z2,z3,z4,z5,z897]),(0,[z1,z2,z3,z767,z5,z6]),(0,[z1,z2,z11,z4,z5,z148]),(0,[z248,z2,z56,z3,z5,z57])],[(0,[z1,z2,z3,z4,z5,z943]),(0,[z28,z1,z2,z3,z4,z132])],[(0,[z1,z2,z3,z944,z4,z6]),(0,[z139,z80,z32,z3,z4,z6]),(0,[z1,z2,z32,z3,z296,z57])],[(0,[z1,z2,z945,z3,z4,z6]),(0,[z24,z7,z2,z3,z4,z51]),(0,[z28,z369,z2,z3,z4,z5]),(0,[z1,z55,z15,z3,z4,z5]),(0,[z1,z3,z4,z5,z6,z946])],[(0,[z7,z1,z2,z3,z4,z193]),(0,[z1,z112,z122,z109,z5,z6]),(0,[z1,z2,z32,z3,z502,z6])],[(0,[z1,z2,z3,z4,z5,z847]),(0,[z484,z1,z2,z156,z4,z5]),(0,[z654,z7,z2,z3,z4,z5]),(0,[z1,z2,z178,z4,z5,z148]),(0,[z1,z2,z3,z5,z18,z937])],[(0,[z1,z2,z947,z3,z4,z6]),(0,[z1,z2,z948,z4,z5,z6]),(0,[z7,z1,z2,z3,z949,z5]),(0,[z950,z2,z3,z4,z5,z6]),(0,[z1,z2,z214,z340,z4,z6]),(0,[z1,z2,z3,z29,z4,z254]),(0,[z1,z2,z3,z4,z951,z6])],[(0,[z1,z2,z3,z4,z5,z952])]],
   [[(0,[z1,z2,z3,z4,z94,z132]),(0,[z1,z2,z32,z3,z133,z6]),(0,[z7,z1,z2,z3,z4,z68]),(0,[z1,z2,z3,z4,z953,z6]),(0,[z1,z2,z67,z119,z68,z6])],[(0,[z7,z1,z2,z3,z4,z63]),(0,[z1,z2,z3,z954,z4,z6]),(0,[z1,z2,z3,z4,z955,z6]),(0,[z2,z32,z3,z6,z334,z57])],[(0,[z1,z2,z3,z956,z4,z6]),(0,[z1,z2,z957,z3,z4,z6]),(0,[z90,z2,z116,z4,z5,z188]),(0,[z28,z344,z2,z3,z4,z5]),(0,[z1,z958,z2,z3,z4,z5])],[(0,[z28,z1,z2,z959,z4,z5]),(0,[z1,z2,z3,z861,z253,z6]),(0,[z369,z2,z3,z285,z5,z6]),(0,[z960,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z29,z4,z188]),(0,[z28,z513,z2,z3,z4,z5]),(0,[z1,z2,z156,z4,z5,z111]),(0,[z369,z2,z3,z4,z5,z182])],[(0,[z1,z2,z32,z3,z466,z6])],[(0,[z90,z2,z32,z116,z4,z6]),(0,[z1,z863,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z961,z6])],[(0,[z28,z1,z2,z3,z962,z5]),(0,[z1,z2,z730,z4,z5,z6])],[(0,[z1,z2,z963,z3,z4,z5]),(0,[z654,z2,z3,z4,z155,z6])],[(0,[z1,z2,z149,z12,z4,z5])],[(0,[z1,z2,z964,z3,z5,z6]),(0,[z9,z7,z1,z54,z4,z5]),(0,[z1,z965,z2,z3,z4,z5]),(0,[z1,z2,z698,z3,z29,z6])],[(0,[z1,z2,z282,z3,z29,z6]),(0,[z1,z2,z3,z4,z6,z966]),(0,[z248,z2,z32,z3,z6,z57])],[(0,[z28,z1,z2,z32,z3,z4]),(0,[z369,z2,z3,z316,z5,z6])],[(0,[z1,z2,z3,z4,z5,z967]),(0,[z1,z2,z375,z3,z4,z132]),(0,[z35,z2,z3,z4,z900,z6]),(0,[z1,z2,z340,z122,z4,z6]),(0,[z1,z3,z37,z767,z5,z6]),(0,[z1,z2,z32,z3,z111,z57]),(0,[z875,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z962,z5,z6]),(0,[z1,z2,z3,z968,z4,z6]),(0,[z1,z2,z969,z3,z4,z5]),(0,[z1,z2,z3,z970,z5,z6])],[(0,[z1,z15,z3,z4,z346,z5]),(0,[z1,z2,z3,z4,z5,z971]),(0,[z1,z2,z32,z3,z58,z6])]],
   [[(0,[z1,z2,z3,z972,z5,z6]),(0,[z1,z2,z3,z4,z973,z6])],[(0,[z1,z2,z3,z346,z5,z6]),(0,[z7,z2,z3,z29,z4,z200])],[(0,[z28,z35,z2,z3,z4,z155])],[(0,[z1,z2,z3,z4,z888,z6]),(0,[z1,z2,z974,z3,z4,z5]),(0,[z28,z7,z2,z168,z4,z5]),(0,[z1,z2,z3,z4,z163,z132]),(0,[z975,z2,z3,z4,z5,z6]),(0,[z1,z2,z716,z38,z5,z6])],[(0,[z28,z1,z2,z3,z4,z976]),(0,[z1,z15,z168,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z216]),(0,[z1,z695,z3,z4,z52,z6]),(0,[z1,z2,z3,z4,z95,z195])],[(0,[z1,z2,z3,z4,z5,z977]),(0,[z1,z2,z32,z3,z307,z6]),(0,[z1,z978,z32,z3,z4,z6])],[(0,[z28,z1,z2,z3,z29,z346]),(0,[z1,z2,z32,z3,z4,z979]),(0,[z1,z2,z32,z3,z6,z195])],[(0,[z1,z2,z3,z107,z185,z6]),(0,[z1,z15,z3,z4,z5,z120]),(0,[z2,z3,z4,z5,z6,z980]),(0,[z1,z2,z3,z4,z981,z6])],[(0,[z28,z1,z15,z3,z4,z5])],[(0,[z1,z895,z3,z4,z5,z6]),(0,[z28,z2,z3,z253,z5,z146])],[(0,[z1,z2,z3,z982,z285,z6])],[(0,[z7,z2,z3,z4,z5,z763]),(0,[z1,z2,z3,z316,z5,z6]),(0,[z1,z2,z32,z3,z4,z983])],[(0,[z85,z2,z3,z29,z60,z6]),(0,[z28,z1,z2,z168,z253,z5]),(0,[z28,z1,z2,z984,z4,z5]),(0,[z1,z2,z3,z4,z5,z934])],[(0,[z1,z112,z214,z109,z5,z6]),(0,[z1,z112,z3,z152,z109,z6])],[(0,[z28,z138,z2,z168,z4,z5])],[(0,[z1,z2,z3,z6,z985,z57])]],
   [[(0,[z1,z2,z986,z4,z5,z6]),(0,[z7,z1,z2,z282,z3,z5]),(0,[z240,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z4,z987,z6])],[(0,[z138,z2,z3,z118,z5,z6]),(0,[z369,z2,z3,z4,z301,z6])],[(0,[z90,z2,z772,z4,z5,z6]),(0,[z600,z1,z15,z3,z4,z5]),(0,[z28,z1,z2,z3,z4,z988]),(0,[z28,z1,z2,z3,z4,z989]),(0,[z1,z15,z32,z3,z4,z6]),(0,[z1,z2,z3,z346,z5,z135]),(0,[z9,z240,z54,z4,z5,z6])],[(0,[z28,z281,z2,z3,z4,z5]),(0,[z28,z2,z615,z3,z4,z5]),(0,[z28,z2,z449,z3,z4,z5]),(0,[z1,z2,z3,z4,z990,z6])],[(0,[z1,z2,z149,z156,z4,z5]),(0,[z365,z1,z2,z3,z346,z5])],[(0,[z1,z2,z991,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z33])],[(0,[z28,z1,z2,z3,z4,z534]),(0,[z85,z2,z3,z992,z5,z6]),(0,[z1,z79,z3,z4,z132,z6])],[(0,[z1,z2,z3,z4,z993,z6]),(0,[z1,z2,z3,z994,z5,z6]),(0,[z248,z2,z3,z4,z5,z111]),(0,[z1,z2,z32,z860,z4,z6]),(0,[z1,z2,z32,z3,z6,z237])],[(0,[z28,z1,z2,z829,z4,z5]),(0,[z28,z2,z415,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z995]),(0,[z1,z996,z3,z4,z5,z6]),(0,[z28,z2,z3,z748,z4,z5]),(0,[z28,z633,z2,z3,z4,z5]),(0,[z1,z2,z387,z3,z5,z57])],[(0,[z1,z2,z3,z4,z740,z6]),(0,[z1,z2,z997,z4,z5,z6]),(0,[z1,z260,z3,z4,z223,z6]),(0,[z1,z2,z3,z58,z5,z57])],[(0,[z1,z2,z32,z3,z4,z61]),(0,[z7,z2,z3,z561,z4,z5])],[(0,[z1,z2,z3,z4,z5,z998])],[(0,[z138,z2,z355,z3,z5,z6]),(0,[z1,z2,z999,z3,z4,z6]),(0,[z1000,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z930,z3,z4,z6]),(0,[z1,z2,z1001,z4,z5,z6]),(0,[z1,z172,z3,z34,z4,z6])]],
   [[(0,[z80,z823,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z217,z5]),(0,[z1,z2,z3,z346,z163,z6]),(0,[z1,z2,z3,z4,z301,z6]),(0,[z9,z1,z54,z29,z4,z6]),(0,[z1,z2,z340,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z254]),(0,[z1,z2,z3,z153,z5,z296])],[(0,[z1,z2,z3,z4,z5,z1002]),(0,[z28,z1,z2,z3,z346,z163]),(0,[z28,z2,z3,z4,z5,z334]),(0,[z7,z1,z2,z214,z4,z5]),(0,[z1,z2,z32,z3,z4,z102]),(0,[z1,z2,z3,z4,z193,z95])],[(0,[z1,z2,z3,z1003,z4,z6]),(0,[z28,z9,z1,z54,z4,z5]),(0,[z28,z2,z3,z4,z5,z175]),(0,[z1,z2,z387,z3,z29,z6])],[(0,[z1,z2,z3,z5,z61,z57]),(0,[z1,z2,z32,z3,z89,z6]),(0,[z1,z2,z3,z1004,z5,z6]),(0,[z607,z1,z2,z32,z3,z6]),(0,[z1,z2,z3,z29,z203,z6])],[(0,[z28,z2,z156,z60,z4,z5]),(0,[z1,z2,z3,z4,z317,z6]),(0,[z1,z2,z3,z4,z95,z33]),(0,[z1,z2,z3,z193,z6,z57])],[(0,[z7,z1,z2,z32,z3,z4]),(0,[z7,z2,z3,z4,z5,z495]),(0,[z1,z1005,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z188]),(0,[z1006,z2,z32,z3,z4,z6]),(0,[z1,z2,z32,z3,z153,z33])],[(0,[z1,z2,z3,z923,z5,z20]),(0,[z7,z1,z2,z1007,z3,z4]),(0,[z1,z2,z32,z3,z285,z6])],[(0,[z1,z2,z3,z4,z5,z926]),(0,[z1,z2,z3,z29,z4,z216]),(0,[z1,z2,z4,z5,z1008,z6]),(0,[z1,z2,z3,z5,z735,z6]),(0,[z1,z2,z395,z478,z4,z6]),(0,[z1,z2,z3,z5,z376,z57])],[(0,[z85,z1,z2,z368,z3,z6]),(0,[z1,z2,z282,z375,z3,z5]),(0,[z28,z1,z2,z3,z1009,z5]),(0,[z2,z1010,z3,z4,z5,z6])],[(0,[z1,z2,z1011,z3,z4,z6]),(0,[z1,z2,z3,z4,z900,z6]),(0,[z1,z2,z168,z4,z5,z120]),(0,[z1,z2,z492,z3,z4,z33])],[(0,[z1,z2,z1012,z3,z5,z6]),(0,[z1,z2,z32,z48,z3,z4])],[(0,[z1,z1013,z3,z4,z5,z6]),(0,[z1,z2,z1014,z3,z4,z5]),(0,[z28,z1,z2,z168,z4,z132]),(0,[z7,z1,z2,z3,z4,z30]),(0,[z1,z2,z3,z4,z5,z931]),(0,[z1,z2,z32,z3,z6,z295])],[(0,[z1,z59,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1015,z6]),(0,[z28,z322,z2,z3,z4,z5])],[(0,[z28,z2,z433,z3,z4,z5])],[(0,[z28,z1,z2,z3,z73,z4]),(0,[z1,z3,z4,z955,z5,z6])]],
   [[(0,[z1,z2,z772,z4,z5,z6]),(0,[z1,z2,z3,z4,z61,z1016]),(0,[z1,z2,z32,z3,z305,z6]),(0,[z28,z1,z2,z3,z4,z326])],[(0,[z7,z1,z15,z3,z4,z5]),(0,[z1,z2,z32,z3,z346,z6]),(0,[z1,z2,z395,z4,z76,z6]),(0,[z1,z2,z32,z3,z6,z289])],[(0,[z28,z7,z2,z3,z253,z5]),(0,[z1,z2,z32,z815,z3,z4]),(0,[z1,z2,z3,z153,z17,z5])],[(0,[z1,z2,z3,z4,z1017,z6]),(0,[z138,z2,z3,z992,z5,z6]),(0,[z7,z2,z3,z4,z5,z200]),(0,[z1,z2,z3,z1018,z5,z6]),(0,[z1,z3,z4,z5,z800,z6])],[(0,[z1,z2,z3,z4,z132,z6]),(0,[z240,z2,z3,z29,z4,z6]),(0,[z1,z2,z214,z152,z4,z6])],[(0,[z104,z2,z492,z3,z4,z6])],[(0,[z1,z2,z3,z4,z864,z6]),(0,[z28,z1,z79,z32,z3,z4]),(0,[z28,z1,z36,z3,z4,z52]),(0,[z1,z15,z3,z29,z4,z6]),(0,[z1,z3,z730,z4,z5,z6])],[(0,[z28,z1,z1019,z3,z4,z5]),(0,[z1,z2,z12,z16,z4,z5]),(0,[z1,z2,z1020,z3,z4,z6]),(0,[z1,z2,z1021,z3,z4,z6]),(0,[z71,z1,z358,z3,z4,z6])],[(0,[z643,z80,z3,z4,z5,z6])],[(1,[z1,z2,z815,z3,z4]),(0,[z1,z2,z3,z4,z1022,z6]),(0,[z1,z2,z3,z29,z4,z33])],[(0,[z1,z2,z3,z4,z1023,z6]),(0,[z1,z2,z4,z716,z5,z6])],[(0,[z1,z429,z2,z32,z3,z6]),(0,[z28,z1,z2,z3,z4,z1024]),(0,[z28,z1,z2,z214,z4,z5])],[],[(0,[z28,z138,z2,z3,z253,z5]),(0,[z1,z2,z3,z1025,z5,z6]),(0,[z1,z302,z103,z38,z5,z6])],[(0,[z1,z2,z3,z1026,z5,z6]),(0,[z1,z2,z149,z4,z5,z148]),(0,[z1,z2,z3,z4,z5,z1027]),(0,[z1,z2,z3,z4,z1028,z61]),(0,[z1,z2,z32,z3,z444,z6])],[(0,[z1,z2,z3,z4,z1029,z6]),(0,[z7,z1,z2,z3,z4,z534]),(0,[z1,z2,z3,z29,z4,z61]),(0,[z1,z2,z3,z4,z5,z1030]),(0,[z1,z2,z3,z5,z1031,z6]),(0,[z1,z2,z3,z4,z6,z1032]),(0,[z1,z2,z125,z3,z4,z732])]],
   [[(0,[z139,z80,z3,z4,z5,z6]),(0,[z28,z85,z2,z3,z60,z5]),(0,[z28,z2,z3,z60,z253,z5]),(0,[z1,z2,z3,z5,z6,z1033])],[(0,[z35,z2,z3,z519,z4,z6]),(0,[z1,z2,z56,z3,z5,z937])],[(0,[z28,z1,z2,z930,z3,z4]),(0,[z248,z2,z3,z4,z6,z292])],[(0,[z1,z2,z1034,z3,z4,z5]),(0,[z1,z260,z263,z3,z4,z6])],[(0,[z1,z59,z3,z4,z5,z147]),(0,[z28,z138,z1,z2,z32,z3]),(0,[z2,z32,z3,z4,z6,z334])],[(0,[z1,z2,z3,z4,z5,z1035]),(0,[z1,z2,z3,z4,z1036,z6]),(0,[z1,z2,z3,z29,z4,z102])],[(0,[z28,z1,z2,z3,z4,z30])],[(0,[z72,z823,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z268,z6]),(0,[z1,z2,z32,z3,z6,z360])],[(0,[z1,z2,z3,z4,z1037,z6])],[(0,[z1,z2,z293,z3,z29,z4]),(0,[z1,z2,z3,z4,z5,z1038])],[(0,[z1,z2,z3,z1039,z4,z6]),(0,[z1,z2,z293,z3,z4,z5]),(0,[z85,z2,z3,z514,z5,z6]),(0,[z1,z2,z32,z3,z308,z6]),(0,[z28,z1,z15,z3,z29,z4]),(0,[z7,z2,z3,z4,z5,z334])],[(0,[z2,z3,z4,z155,z900,z6]),(0,[z1,z407,z3,z4,z223,z6]),(0,[z28,z1,z2,z720,z4,z5]),(0,[z1,z2,z3,z253,z5,z57]),(0,[z28,z2,z3,z4,z5,z443]),(0,[z1,z2,z1040,z3,z5,z6]),(0,[z1041,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z285,z6])],[(0,[z28,z72,z106,z3,z4,z5]),(0,[z1,z2,z789,z3,z346,z6])],[(0,[z489,z1,z2,z265,z4,z5]),(0,[z1,z2,z3,z4,z1042,z6])],[(0,[z1,z793,z3,z4,z5,z6]),(0,[z28,z7,z2,z156,z4,z5]),(0,[z7,z1,z2,z75,z4,z78])],[(0,[z1,z2,z3,z5,z6,z1043]),(0,[z1,z2,z156,z253,z5,z6])]],
   [[(0,[z7,z1,z2,z183,z4,z76]),(0,[z1,z2,z3,z4,z6,z1044]),(0,[z1,z2,z3,z4,z193,z6])],[(0,[z139,z80,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z1045,z6]),(0,[z85,z7,z2,z3,z60,z5]),(0,[z1,z302,z103,z4,z5,z6]),(0,[z1,z2,z3,z1046,z5,z6])],[(0,[z1,z2,z3,z4,z1047,z5]),(0,[z2,z3,z60,z992,z5,z6]),(0,[z28,z7,z2,z3,z4,z132]),(0,[z9,z1,z54,z4,z5,z6]),(0,[z1048,z2,z3,z4,z5,z6]),(0,[z1,z142,z10,z29,z4,z6])],[(0,[z1,z2,z1049,z4,z5,z6]),(0,[z1,z2,z3,z4,z1050,z6]),(0,[z1,z302,z3,z4,z5,z725])],[(0,[z28,z2,z3,z346,z5,z146]),(0,[z1,z2,z75,z4,z336,z6])],[(0,[z28,z138,z2,z3,z118,z5]),(0,[z1,z2,z3,z29,z6,z289])],[(0,[z928,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z153,z5,z18])],[(0,[z7,z1,z2,z3,z4,z205]),(0,[z85,z2,z3,z60,z5,z61]),(0,[z28,z1,z2,z156,z253,z5]),(0,[z1,z2,z156,z346,z5,z6]),(0,[z1,z2,z32,z3,z394,z6])],[(0,[z1,z2,z3,z4,z1051,z5]),(0,[z7,z1,z2,z3,z73,z4])],[(0,[z1,z2,z3,z4,z1052,z6]),(0,[z28,z138,z2,z156,z4,z5]),(0,[z1,z2,z168,z29,z4,z6]),(0,[z7,z1,z2,z3,z4,z326]),(0,[z1,z2,z3,z5,z6,z1053])],[(0,[z1,z2,z3,z4,z436,z6]),(0,[z2,z3,z4,z992,z5,z6]),(0,[z1,z2,z3,z4,z1054,z6]),(0,[z1,z2,z156,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z216]),(1,[z1,z2,z4,z719,z6]),(0,[z1,z2,z3,z203,z735,z6])],[(0,[z1,z2,z293,z3,z153,z5]),(0,[z28,z1,z2,z3,z253,z132]),(0,[z1,z2,z103,z285,z5,z6]),(0,[z1,z2,z32,z3,z4,z201]),(0,[z1,z978,z3,z4,z5,z6])],[(0,[z28,z1,z1055,z3,z4,z5]),(0,[z369,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z29,z331,z6])],[(0,[z7,z1,z2,z3,z4,z436]),(0,[z28,z138,z2,z3,z4,z132]),(0,[z1056,z1,z2,z3,z4,z5]),(0,[z1057,z2,z32,z3,z4,z6])],[(0,[z191,z1,z59,z3,z4,z5]),(0,[z713,z1,z2,z3,z4,z5]),(0,[z1,z79,z3,z4,z5,z147]),(0,[z1,z2,z3,z29,z160,z6]),(0,[z1058,z2,z32,z3,z4,z6]),(0,[z1,z2,z3,z29,z4,z1059])],[(0,[z1,z2,z3,z4,z1060,z6]),(0,[z1,z2,z3,z4,z5,z1061]),(0,[z7,z1,z36,z3,z4,z52])]],
   [[(0,[z1,z2,z32,z3,z610,z6]),(0,[z1,z2,z3,z4,z5,z1062])],[(0,[z7,z1,z2,z165,z3,z4]),(0,[z1,z2,z3,z4,z5,z983]),(0,[z1,z2,z3,z4,z193,z135])],[(0,[z798,z1,z2,z32,z3,z4]),(0,[z1,z2,z3,z6,z292,z289])],[(0,[z1,z2,z3,z4,z1063,z6]),(0,[z28,z1,z2,z948,z4,z5])],[(0,[z1,z2,z3,z4,z1064,z6]),(0,[z28,z2,z3,z60,z5,z57]),(0,[z28,z123,z2,z3,z4,z5]),(0,[z515,z7,z1,z2,z32,z3]),(0,[z9,z1,z32,z54,z4,z6]),(0,[z1,z2,z3,z58,z5,z296])],[(0,[z1,z2,z3,z4,z5,z1065])],[(0,[z240,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1066,z6]),(0,[z28,z1,z2,z340,z3,z4]),(0,[z1,z2,z3,z4,z6,z1067]),(0,[z1,z2,z3,z29,z58,z6])],[(0,[z1,z2,z1068,z3,z4,z6]),(0,[z1,z2,z3,z1009,z5,z6])],[(0,[z1,z15,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z658,z6]),(0,[z28,z1,z2,z75,z4,z78]),(0,[z1,z2,z3,z4,z1069,z6]),(0,[z1,z2,z1070,z3,z4,z6])],[(0,[z1,z2,z3,z4,z205,z6]),(0,[z1,z10,z4,z341,z5,z6]),(1,[z1,z2,z716,z5,z6])],[(0,[z28,z1,z2,z183,z4,z76])],[(0,[z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z5,z33]),(1,[z1,z2,z3,z5,z937])],[(0,[z1,z2,z3,z5,z1071,z6]),(0,[z1,z2,z214,z285,z5,z6]),(0,[z1072,z1,z2,z3,z4,z5]),(0,[z1,z2,z1073,z4,z5,z6]),(0,[z1,z2,z4,z5,z120,z746])],[(0,[z1,z2,z3,z4,z5,z1074]),(0,[z1,z79,z168,z4,z5,z6]),(0,[z1,z2,z3,z346,z5,z111]),(0,[z1,z1075,z2,z3,z4,z5]),(0,[z1,z2,z4,z5,z6,z1076])],[(0,[z1,z2,z149,z32,z3,z4]),(0,[z1,z128,z3,z767,z5,z6]),(0,[z1,z2,z4,z5,z6,z746]),(0,[z1,z2,z125,z3,z4,z135])],[(0,[z1,z59,z2,z3,z29,z4]),(0,[z1,z2,z1077,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z163]),(0,[z1,z1078,z2,z3,z4,z5]),(0,[z1,z3,z4,z5,z1079,z6])]],
   [[(0,[z204,z2,z32,z97,z4,z6]),(0,[z28,z138,z2,z32,z3,z4])],[(0,[z1,z1080,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z205]),(0,[z1,z2,z3,z4,z5,z61]),(0,[z1,z2,z3,z4,z5,z1081]),(0,[z43,z1,z2,z282,z3,z6]),(0,[z28,z1,z2,z3,z1026,z5]),(0,[z1,z2,z56,z3,z346,z5])],[(0,[z1,z2,z1082,z3,z4,z6]),(0,[z1,z2,z32,z3,z316,z6])],[(0,[z1,z2,z3,z4,z5,z1083])],[(0,[z1,z2,z3,z4,z1084,z6]),(0,[z1,z3,z4,z5,z111,z800])],[(0,[z139,z80,z3,z4,z5,z42]),(0,[z1,z55,z32,z3,z4,z147])],[(0,[z1,z2,z32,z122,z4,z6]),(0,[z1,z103,z219,z38,z5,z6])],[(0,[z28,z1,z2,z3,z4,z436]),(0,[z28,z1,z2,z156,z4,z132]),(0,[z1,z2,z3,z1085,z4,z6]),(0,[z1,z2,z152,z122,z4,z6]),(0,[z1,z2,z3,z4,z5,z102])],[],[(0,[z1,z2,z3,z4,z5,z1086]),(0,[z1,z2,z3,z4,z1028,z6]),(0,[z28,z2,z3,z4,z5,z39])],[(0,[z1,z2,z3,z4,z1087,z6]),(0,[z2,z3,z4,z5,z334,z189]),(0,[z1,z1088,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z1084]),(0,[z248,z2,z3,z346,z5,z6]),(0,[z191,z1,z3,z4,z5,z800]),(0,[z1,z2,z32,z3,z4,z1089]),(0,[z1,z2,z32,z3,z29,z296])],[(0,[z28,z1,z2,z165,z3,z4]),(0,[z1,z79,z32,z3,z4,z6])],[(0,[z1,z2,z1090,z3,z4,z6]),(0,[z1,z1091,z3,z4,z5,z6]),(0,[z1,z2,z3,z982,z4,z6]),(0,[z1006,z2,z3,z4,z5,z6])],[(0,[z1,z2,z32,z3,z380,z6]),(0,[z1,z2,z3,z4,z1024,z6]),(0,[z28,z1,z922,z3,z4,z5]),(0,[z7,z1,z2,z3,z4,z1023]),(0,[z1092,z1,z2,z3,z4,z5]),(0,[z1,z2,z32,z3,z339,z33])],[],[(0,[z537,z1,z2,z156,z4,z5]),(0,[z1,z2,z3,z29,z4,z201])]],
   [[(0,[z1,z1093,z3,z4,z5,z6]),(0,[z28,z1,z79,z3,z4,z163]),(0,[z1,z2,z3,z4,z1094,z6]),(0,[z1,z2,z32,z602,z3,z6]),(0,[z1,z2,z3,z1095,z4,z6]),(0,[z1,z2,z3,z4,z5,z1096]),(0,[z1,z768,z2,z3,z4,z5])],[(0,[z85,z1,z2,z32,z3,z296]),(0,[z28,z1,z2,z789,z3,z4]),(0,[z1,z2,z1007,z3,z4,z6])],[(0,[z2,z3,z4,z5,z763,z146]),(0,[z7,z1,z2,z3,z5,z289]),(0,[z1,z2,z1097,z3,z4,z6]),(1,[z1,z2,z3,z4,z732])],[(0,[z1,z2,z3,z4,z5,z1098]),(0,[z28,z318,z2,z3,z4,z5]),(0,[z1,z2,z332,z3,z4,z33])],[(0,[z1,z142,z10,z4,z5,z6])],[(0,[z28,z2,z32,z3,z60,z4]),(1,[z1,z15,z156,z4,z5]),(0,[z28,z248,z2,z3,z346,z5])],[(0,[z1,z2,z3,z4,z132,z57]),(1,[z1,z3,z767,z5,z6])],[(0,[z1,z15,z3,z4,z163,z6]),(0,[z28,z2,z3,z4,z132,z146]),(0,[z7,z1,z2,z3,z1099,z4])],[(0,[z65,z1,z190,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1100])],[(0,[z90,z2,z116,z29,z4,z6]),(0,[z138,z1,z2,z368,z3,z6]),(0,[z1,z2,z3,z4,z155,z33]),(0,[z28,z1,z2,z3,z4,z163]),(0,[z1101,z1,z2,z3,z4,z5]),(0,[z1,z2,z103,z326,z38,z6])],[(0,[z1,z2,z3,z49,z73,z4]),(0,[z1,z2,z156,z4,z132,z6]),(0,[z369,z2,z32,z3,z4,z6])],[(0,[z1,z2,z32,z3,z4,z42]),(0,[z1,z2,z168,z4,z5,z6]),(0,[z1,z1102,z3,z4,z5,z6]),(0,[z1,z3,z767,z109,z5,z6])],[(0,[z1,z302,z3,z4,z326,z6])],[(0,[z28,z1,z2,z815,z3,z4])],[(0,[z138,z2,z32,z355,z3,z6]),(0,[z28,z1,z15,z168,z4,z5]),(0,[z1,z2,z265,z4,z5,z148]),(0,[z369,z2,z3,z4,z5,z216])],[(0,[z28,z1,z302,z3,z4,z5]),(0,[z7,z1,z2,z340,z3,z4]),(0,[z1,z2,z32,z3,z6,z541]),(0,[z1103,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z955,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1059])],[(0,[z1,z2,z3,z4,z6,z1016]),(0,[z7,z1,z2,z1040,z3,z5])],[(0,[z572,z1,z2,z3,z4,z53]),(0,[z1,z2,z802,z3,z4,z5])],[],[(0,[z1,z2,z3,z1104,z4,z5]),(0,[z1,z1055,z3,z4,z5,z6]),(1,[z2,z3,z4,z900,z6]),(0,[z104,z2,z3,z4,z155,z6])],[(0,[z1,z2,z1105,z4,z5,z6]),(0,[z1,z2,z3,z992,z5,z6]),(0,[z1106,z2,z3,z4,z5,z6]),(1,[z1,z730,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z1107]),(0,[z1,z2,z3,z29,z4,z1108])],[(0,[z1,z2,z3,z4,z5,z1109]),(0,[z1,z2,z3,z4,z1110,z5]),(0,[z28,z159,z2,z3,z4,z5]),(0,[z1,z2,z3,z29,z316,z6])],[(0,[z1,z2,z3,z4,z741,z6]),(0,[z1,z2,z3,z1111,z5,z6]),(0,[z191,z1,z32,z3,z4,z111]),(0,[z1,z2,z32,z67,z119,z6])],[(0,[z1,z2,z3,z4,z314,z1038]),(0,[z24,z1,z2,z282,z3,z6]),(0,[z1,z1112,z2,z3,z4,z5]),(0,[z1,z2,z3,z29,z346,z6])],[(0,[z1,z2,z32,z3,z4,z6]),(0,[z1,z2,z1113,z3,z4,z6]),(0,[z1,z55,z3,z29,z4,z147]),(0,[z1,z2,z32,z3,z4,z1114]),(0,[z1,z2,z3,z4,z406,z135]),(0,[z1,z2,z3,z4,z5,z937])],[(1,[z2,z772,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z830]),(0,[z248,z1,z2,z32,z3,z6]),(0,[z1,z2,z3,z58,z5,z18])],[(0,[z1,z2,z4,z1115,z5,z6]),(0,[z28,z90,z2,z116,z4,z5]),(0,[z515,z1,z2,z3,z8,z5]),(0,[z1116,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z1117,z4,z5]),(0,[z1,z2,z3,z94,z95,z289])],[(0,[z1,z2,z368,z3,z4,z6]),(0,[z28,z1,z2,z3,z5,z289]),(0,[z1,z2,z3,z4,z719,z6])],[(0,[z1,z2,z3,z4,z5,z1118]),(0,[z28,z584,z2,z3,z4,z5]),(0,[z1,z2,z32,z852,z4,z6])],[(0,[z1,z2,z282,z3,z52,z6])],[(0,[z28,z47,z2,z3,z4,z5]),(0,[z28,z1,z2,z332,z3,z4]),(0,[z1,z2,z3,z4,z5,z979]),(0,[z1,z2,z3,z4,z1119,z6]),(0,[z1,z3,z4,z5,z1120,z6])]],
   [[(0,[z72,z7,z106,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1121]),(0,[z85,z1,z2,z817,z3,z6]),(0,[z28,z1,z2,z3,z907,z5]),(0,[z1,z2,z3,z4,z1122,z6])],[(0,[z1,z2,z3,z949,z5,z6])],[(0,[z28,z1,z2,z991,z4,z5]),(0,[z28,z1,z2,z3,z807,z5]),(0,[z28,z1,z2,z3,z285,z5]),(0,[z1,z2,z3,z4,z6,z1123]),(0,[z1,z2,z32,z936,z4,z6]),(0,[z1,z2,z3,z153,z193,z6])],[(0,[z1,z3,z4,z5,z1124,z6]),(0,[z28,z2,z3,z60,z4,z132]),(0,[z28,z1,z2,z3,z1125,z5]),(0,[z7,z1,z2,z3,z58,z5]),(0,[z1,z2,z4,z5,z746,z148])],[(0,[z44,z1,z15,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1126]),(0,[z1,z128,z32,z3,z37,z6]),(0,[z1,z2,z3,z4,z1127,z5]),(0,[z1,z2,z3,z4,z1128,z6])],[(0,[z28,z1,z2,z3,z29,z253]),(0,[z1,z112,z340,z3,z109,z6])],[(0,[z1,z2,z3,z1125,z5,z6]),(0,[z1,z2,z3,z4,z1129,z6])],[(0,[z28,z7,z2,z32,z3,z4]),(0,[z499,z1,z2,z3,z17,z5]),(0,[z1,z2,z103,z38,z5,z254]),(0,[z1,z302,z3,z4,z5,z862]),(0,[z1,z165,z3,z4,z219,z6])],[(0,[z248,z2,z3,z118,z5,z6]),(0,[z28,z2,z3,z29,z60,z4]),(0,[z1,z2,z3,z4,z1130,z6])],[(0,[z28,z248,z2,z3,z4,z5]),(0,[z1,z2,z1131,z4,z5,z6]),(0,[z1,z2,z168,z4,z163,z6]),(0,[z1,z2,z32,z3,z153,z6])],[(0,[z1,z319,z2,z32,z3,z4]),(0,[z1,z2,z3,z716,z5,z6]),(0,[z1,z2,z32,z12,z4,z120])],[(0,[z7,z1,z2,z368,z3,z4]),(0,[z28,z1,z2,z3,z346,z5]),(0,[z9,z1,z437,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z1132])],[(0,[z1,z2,z3,z4,z5,z1133]),(0,[z1,z2,z368,z3,z153,z6]),(0,[z1,z3,z4,z223,z955,z6])],[(0,[z1,z2,z3,z1134,z5,z6]),(0,[z1,z2,z3,z4,z1135,z6]),(0,[z1,z2,z3,z4,z1136,z6]),(0,[z1,z2,z3,z4,z5,z1137])],[(0,[z1,z2,z3,z29,z4,z42]),(0,[z1,z2,z3,z4,z1138,z6]),(0,[z1,z2,z1139,z3,z4,z5])]],
   [[(0,[z1,z2,z32,z3,z4,z189])],[(0,[z1,z2,z3,z4,z5,z201])],[(0,[z2,z3,z4,z900,z5,z6]),(0,[z2,z3,z4,z5,z6,z763]),(0,[z1140,z2,z3,z4,z5,z6]),(0,[z1,z128,z3,z37,z317,z6]),(0,[z1,z2,z3,z4,z1141,z6]),(0,[z1,z2,z119,z716,z5,z6])],[(0,[z1,z2,z1142,z3,z5,z6]),(0,[z1057,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z1143,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1144]),(0,[z28,z7,z15,z3,z4,z5]),(0,[z1,z2,z789,z3,z4,z6]),(0,[z1,z2,z3,z1145,z4,z6]),(0,[z1058,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1146,z6]),(0,[z2,z116,z772,z4,z5,z6]),(0,[z138,z2,z293,z3,z118,z5]),(0,[z1,z2,z3,z4,z1147,z6]),(0,[z28,z1,z2,z3,z4,z317]),(0,[z1,z2,z1148,z3,z5,z6])],[(0,[z600,z1,z2,z3,z346,z5]),(0,[z1,z2,z32,z56,z3,z57])],[],[(0,[z7,z1,z302,z3,z4,z5])],[(0,[z560,z106,z3,z4,z5,z6]),(0,[z659,z2,z3,z4,z155,z6]),(0,[z248,z2,z3,z4,z5,z148])],[(0,[z1,z2,z3,z1149,z4,z6]),(0,[z7,z240,z2,z3,z4,z5]),(0,[z1,z32,z3,z4,z219,z6])],[(0,[z90,z2,z116,z4,z5,z6]),(0,[z28,z1,z2,z1049,z4,z5]),(0,[z28,z15,z3,z4,z5,z146]),(0,[z191,z1,z3,z29,z4,z111]),(0,[z1,z2,z3,z29,z6,z570])],[(0,[z72,z106,z32,z3,z4,z6]),(0,[z1,z2,z3,z29,z198,z6]),(0,[z942,z369,z2,z3,z4,z5]),(0,[z1,z2,z103,z38,z5,z102])],[(0,[z1,z2,z3,z29,z4,z6]),(0,[z28,z1,z15,z3,z253,z5]),(0,[z28,z1,z2,z3,z58,z5]),(0,[z7,z2,z3,z4,z151,z5])],[(0,[z1,z15,z156,z4,z5,z6]),(0,[z1150,z2,z3,z4,z5,z6])],[(0,[z28,z138,z15,z3,z4,z5])]],
   [[(0,[z28,z1,z1093,z3,z4,z5]),(0,[z1151,z1,z2,z3,z4,z5]),(0,[z1,z214,z37,z4,z5,z6]),(0,[z1,z2,z32,z3,z62,z296])],[(0,[z1,z2,z3,z4,z5,z1152]),(0,[z1,z2,z3,z4,z5,z1153]),(0,[z1,z2,z3,z4,z6,z732])],[(0,[z2,z772,z97,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z1063]),(0,[z1,z2,z32,z3,z278,z6])],[(0,[z1,z2,z3,z153,z5,z61]),(0,[z1,z2,z3,z4,z296,z33])],[(0,[z28,z2,z3,z8,z4,z5]),(0,[z28,z2,z3,z4,z5,z266]),(0,[z1,z2,z32,z3,z13,z6])],[(0,[z1,z480,z2,z32,z3,z6]),(0,[z28,z1,z2,z3,z827,z4])],[(0,[z28,z1,z2,z368,z3,z4]),(0,[z1,z2,z32,z375,z3,z4]),(0,[z28,z1,z2,z32,z156,z4]),(0,[z1,z2,z32,z615,z3,z6]),(0,[z1,z2,z3,z1154,z4,z6])],[(0,[z515,z1,z2,z32,z3,z6]),(0,[z1,z2,z3,z4,z1155,z6]),(0,[z1,z2,z3,z4,z5,z1108])],[(0,[z7,z1,z2,z332,z3,z4]),(0,[z1,z302,z3,z285,z5,z6])],[],[(0,[z1,z2,z3,z1156,z4,z6])],[(0,[z1,z2,z3,z253,z5,z18]),(0,[z7,z1,z2,z3,z285,z5]),(0,[z1,z55,z3,z4,z5,z147]),(0,[z1,z2,z1157,z3,z4,z5]),(0,[z1,z2,z3,z5,z937,z57])],[(0,[z401,z106,z3,z4,z5,z6]),(0,[z28,z1,z2,z168,z4,z163]),(0,[z1,z2,z32,z3,z511,z6]),(0,[z1,z2,z3,z4,z94,z95])],[(0,[z1,z2,z3,z4,z5,z1158]),(0,[z28,z1,z2,z3,z899,z5]),(0,[z7,z2,z176,z3,z4,z5]),(0,[z1,z2,z3,z4,z95,z732])],[(0,[z1,z2,z1159,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1160])],[(0,[z1,z2,z32,z3,z4,z271])]],
   [[(0,[z1,z2,z3,z4,z988,z6]),(0,[z1,z2,z3,z4,z5,z1089]),(0,[z9,z1,z730,z4,z5,z6])],[(0,[z1,z79,z3,z4,z5,z6]),(0,[z1,z144,z3,z4,z5,z147]),(0,[z1,z2,z3,z4,z5,z732])],[(0,[z139,z7,z80,z3,z4,z5]),(0,[z1,z2,z156,z4,z5,z147])],[(0,[z7,z2,z3,z4,z5,z298]),(0,[z1,z2,z3,z285,z5,z182]),(0,[z1,z2,z32,z3,z4,z1161])],[(0,[z1,z2,z3,z29,z4,z189]),(0,[z28,z240,z2,z3,z4,z5]),(0,[z1,z2,z930,z3,z253,z6]),(0,[z1,z2,z32,z3,z29,z33]),(0,[z1,z2,z3,z29,z4,z1162])],[(0,[z85,z2,z3,z60,z5,z6]),(0,[z7,z1,z2,z3,z346,z5]),(0,[z546,z7,z2,z3,z4,z5]),(0,[z1163,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z735,z6])],[(0,[z1,z2,z32,z293,z3,z4]),(0,[z1,z2,z375,z3,z4,z135]),(0,[z1,z74,z3,z192,z4,z6])],[(0,[z1,z2,z3,z4,z6,z985]),(0,[z909,z1,z2,z3,z4,z5])],[(0,[z1,z2,z32,z3,z107,z6]),(0,[z1,z2,z3,z153,z346,z5])],[(0,[z1,z2,z3,z4,z1164,z6]),(0,[z1,z2,z368,z293,z3,z4]),(0,[z28,z1,z15,z156,z4,z5]),(0,[z1,z1165,z2,z3,z4,z5])],[(0,[z1,z2,z3,z1166,z4,z6]),(0,[z590,z7,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1167,z6]),(0,[z1,z36,z3,z4,z955,z6])],[(0,[z1,z2,z3,z4,z5,z1168]),(0,[z85,z1,z2,z32,z3,z33]),(0,[z28,z381,z2,z3,z4,z5]),(0,[z499,z7,z1,z2,z32,z3]),(0,[z960,z1,z2,z32,z3,z4])],[(0,[z35,z1,z2,z282,z3,z6]),(0,[z1,z2,z156,z4,z346,z5]),(0,[z1,z2,z32,z168,z4,z6]),(0,[z1,z2,z3,z316,z5,z182]),(0,[z1,z2,z171,z4,z78,z6])],[(0,[z1,z2,z3,z4,z1169,z6]),(0,[z1,z1019,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z135]),(0,[z28,z1,z15,z3,z4,z132]),(0,[z1,z2,z3,z1117,z29,z4]),(0,[z1,z2,z3,z4,z94,z732])],[(0,[z1,z2,z3,z4,z5,z1170]),(0,[z28,z2,z168,z4,z5,z146]),(0,[z7,z1,z2,z3,z4,z317]),(0,[z1,z1171,z3,z4,z5,z6])],[(0,[z1,z2,z1172,z3,z5,z6]),(0,[z1,z2,z3,z4,z163,z95]),(0,[z1,z2,z3,z8,z5,z57])]],
   [[(0,[z369,z2,z3,z4,z5,z6]),(0,[z1,z2,z293,z3,z5,z57]),(0,[z1,z2,z1173,z3,z4,z5]),(0,[z35,z2,z3,z4,z155,z6]),(0,[z1,z2,z738,z3,z285,z6]),(0,[z1,z2,z3,z4,z1174,z6])],[(0,[z1,z2,z3,z4,z5,z42]),(0,[z138,z1,z2,z32,z3,z296]),(0,[z85,z2,z3,z60,z314,z6]),(0,[z28,z1,z2,z1131,z4,z5]),(0,[z1,z2,z3,z4,z6,z1175])],[(0,[z1,z79,z3,z29,z4,z6])],[(0,[z28,z1,z2,z1176,z4,z5]),(0,[z1,z2,z32,z3,z735,z6])],[(0,[z1,z2,z959,z4,z5,z6]),(0,[z1,z2,z3,z4,z1177,z6]),(0,[z28,z1,z2,z3,z724,z4])],[(0,[z1,z2,z3,z4,z5,z1178]),(0,[z90,z2,z378,z4,z5,z6]),(0,[z1,z2,z3,z4,z718,z6]),(0,[z1,z2,z32,z3,z6,z985])],[(0,[z28,z1,z79,z3,z346,z5])],[],[(0,[z1,z2,z485,z32,z3,z6]),(0,[z1,z2,z3,z4,z5,z800]),(0,[z1,z2,z1179,z3,z4,z6]),(0,[z1,z2,z32,z3,z33,z57])],[(0,[z1,z2,z1180,z4,z5,z6]),(0,[z619,z2,z97,z4,z5,z6]),(0,[z1,z302,z3,z109,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1181]),(0,[z1,z2,z3,z4,z1182,z5]),(0,[z28,z1,z2,z3,z1085,z4]),(0,[z1,z2,z3,z1099,z4,z6]),(1,[z1,z2,z3,z735,z6]),(0,[z2,z332,z3,z4,z6,z334])],[(0,[z28,z85,z1,z2,z32,z3]),(0,[z28,z1,z2,z3,z4,z1050]),(0,[z28,z1,z781,z3,z4,z5]),(0,[z191,z1,z15,z3,z4,z5]),(0,[z1,z2,z218,z119,z5,z6]),(0,[z1,z2,z3,z4,z5,z1107]),(0,[z1,z2,z3,z4,z5,z1183]),(0,[z1,z2,z3,z153,z5,z937])],[(0,[z1,z1184,z3,z4,z5,z6]),(0,[z85,z2,z3,z60,z5,z189]),(0,[z28,z2,z32,z3,z4,z146]),(0,[z1,z2,z1185,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1186])],[(0,[z1,z2,z1176,z4,z5,z6]),(0,[z28,z1,z2,z3,z316,z5]),(0,[z191,z1,z3,z4,z5,z111]),(0,[z31,z1,z2,z236,z4,z6])],[(0,[z1,z1187,z2,z3,z4,z5]),(0,[z204,z2,z97,z4,z436,z6]),(0,[z28,z138,z2,z3,z203,z5]),(0,[z211,z2,z3,z4,z51,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1114]),(0,[z28,z1,z2,z32,z3,z346]),(0,[z1,z2,z3,z5,z6,z1188])]],
   [[(0,[z1,z79,z3,z4,z163,z6]),(0,[z1,z2,z3,z285,z301,z6]),(0,[z1,z2,z32,z3,z656,z6])],[(0,[z2,z3,z4,z5,z6,z334]),(0,[z28,z1,z2,z122,z4,z5]),(0,[z7,z2,z3,z4,z5,z371]),(0,[z369,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z301,z182]),(0,[z1,z2,z32,z3,z57,z135])],[(0,[z28,z7,z2,z3,z4,z163]),(0,[z28,z2,z333,z3,z4,z5]),(0,[z1,z1189,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z131,z5]),(0,[z1,z2,z3,z29,z4,z271]),(0,[z1,z2,z75,z4,z719,z6]),(0,[z1,z2,z3,z1190,z4,z6])],[(0,[z590,z2,z116,z4,z5,z6]),(0,[z1,z2,z409,z4,z78,z6]),(0,[z1,z2,z3,z153,z29,z18])],[(0,[z1,z2,z3,z4,z5,z1191]),(0,[z1,z2,z32,z3,z4,z20]),(0,[z1,z1192,z2,z3,z4,z5]),(0,[z248,z2,z3,z4,z5,z147]),(0,[z1,z2,z32,z3,z207,z6])],[(0,[z1,z2,z3,z4,z534,z6]),(0,[z28,z456,z2,z3,z4,z5]),(0,[z1,z2,z3,z346,z5,z132]),(0,[z1,z2,z1193,z3,z4,z6]),(0,[z1,z2,z3,z4,z1194,z6]),(0,[z1,z2,z3,z29,z704,z6])],[(0,[z35,z7,z2,z3,z4,z155]),(0,[z484,z1,z2,z3,z346,z5]),(0,[z28,z306,z2,z3,z4,z5])],[(0,[z28,z1,z2,z3,z4,z19]),(0,[z1,z2,z3,z1195,z5,z6]),(0,[z1,z2,z3,z29,z309,z6])],[(0,[z1,z2,z375,z3,z4,z94]),(0,[z1,z2,z32,z3,z4,z734])],[(0,[z7,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z1196,z6]),(0,[z28,z1,z2,z3,z253,z163]),(0,[z1,z2,z3,z253,z132,z6]),(0,[z2,z3,z29,z4,z6,z334])],[(0,[z1,z2,z32,z3,z49,z4]),(0,[z85,z7,z1,z2,z32,z3]),(0,[z1,z2,z3,z29,z107,z6]),(0,[z1,z2,z12,z156,z4,z5]),(0,[z1,z2,z255,z3,z5,z57]),(0,[z1,z2,z3,z4,z5,z1197]),(0,[z1,z2,z3,z339,z58,z6])],[(0,[z28,z138,z2,z3,z4,z163]),(0,[z1,z2,z750,z4,z5,z6]),(0,[z1,z15,z3,z4,z5,z57]),(0,[z1198,z2,z3,z4,z5,z6])],[(0,[z1,z2,z32,z3,z173,z6]),(0,[z1,z2,z282,z3,z76,z6])],[(0,[z1,z2,z3,z4,z5,z1199]),(1,[z2,z3,z992,z5,z6]),(0,[z1,z2,z3,z4,z53,z135]),(0,[z9,z1,z101,z4,z5,z6])]],
   [[],[(0,[z1,z2,z32,z3,z339,z6]),(0,[z1,z2,z32,z3,z631,z6])],[(0,[z1,z2,z603,z4,z76,z6])],[(0,[z1,z2,z3,z4,z5,z1200]),(0,[z1,z2,z3,z4,z1201,z6])],[(0,[z1,z2,z3,z4,z5,z1202]),(0,[z138,z2,z32,z3,z118,z6]),(0,[z1,z2,z3,z1203,z5,z6]),(0,[z607,z7,z2,z3,z4,z5]),(0,[z1,z2,z1204,z3,z4,z5])],[(0,[z99,z1,z2,z3,z253,z5]),(0,[z2,z3,z4,z5,z6,z1205])],[(0,[z1,z2,z3,z4,z5,z189]),(0,[z1,z2,z3,z4,z5,z1162])],[(0,[z1,z2,z3,z4,z1206,z6]),(0,[z1,z2,z1207,z3,z4,z6]),(0,[z248,z2,z3,z4,z5,z120]),(0,[z1,z2,z3,z29,z735,z6])],[(0,[z1,z2,z3,z4,z5,z1208]),(0,[z300,z1,z396,z3,z4,z5]),(0,[z1,z2,z12,z4,z5,z746])],[(0,[z1,z3,z4,z1209,z5,z6]),(0,[z1,z2,z3,z4,z5,z1210]),(0,[z28,z1,z710,z3,z4,z5]),(0,[z28,z206,z2,z3,z4,z5]),(0,[z1,z41,z3,z192,z4,z6])],[(0,[z28,z1,z2,z3,z4,z1169])],[(0,[z1,z2,z32,z3,z253,z6])],[(0,[z1,z2,z3,z1211,z5,z6]),(0,[z1,z128,z3,z29,z37,z6])],[(0,[z1,z2,z1157,z3,z29,z4])],[(0,[z1,z2,z3,z4,z163,z6]),(0,[z1,z142,z730,z4,z5,z6]),(0,[z1,z41,z3,z4,z955,z6])],[(0,[z2,z3,z992,z118,z5,z6]),(0,[z1,z2,z32,z3,z4,z131]),(0,[z1,z2,z3,z346,z5,z148]),(0,[z248,z2,z56,z3,z4,z5])]],
   [[(0,[z28,z138,z2,z32,z3,z6]),(0,[z28,z2,z3,z29,z4,z146]),(0,[z1,z2,z3,z4,z5,z905])],[(0,[z2,z293,z3,z60,z4,z5]),(0,[z28,z1,z2,z32,z3,z153])],[(0,[z28,z1,z2,z67,z119,z5]),(0,[z248,z2,z32,z3,z4,z6])],[(0,[z28,z1,z2,z3,z29,z4]),(0,[z1212,z2,z3,z4,z5,z6])],[(0,[z28,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1213,z6]),(0,[z7,z1,z2,z103,z38,z5])],[(0,[z1,z59,z2,z32,z3,z4]),(0,[z1,z2,z1214,z3,z5,z6]),(0,[z1,z2,z32,z3,z148,z57]),(0,[z1,z2,z3,z29,z4,z715])],[(0,[z1,z2,z1215,z4,z5,z6]),(0,[z28,z1,z1091,z3,z4,z5]),(0,[z643,z7,z2,z3,z4,z5]),(0,[z7,z1,z2,z3,z316,z5]),(0,[z1,z2,z32,z3,z235,z6])],[(0,[z28,z1,z2,z156,z4,z163]),(0,[z7,z1,z2,z32,z3,z57]),(0,[z1,z2,z119,z677,z5,z6])],[(0,[z1,z2,z3,z4,z989,z6]),(0,[z2,z3,z60,z748,z4,z5])],[(0,[z1,z2,z3,z29,z4,z20]),(0,[z28,z1,z41,z3,z4,z223]),(0,[z1,z36,z3,z4,z52,z6]),(0,[z1,z2,z165,z3,z4,z6])],[(0,[z7,z1,z2,z122,z4,z5]),(0,[z1,z2,z3,z4,z1216,z6]),(0,[z1,z2,z3,z4,z5,z1217]),(0,[z1,z2,z1218,z3,z4,z5]),(0,[z1,z778,z32,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z1219]),(0,[z1,z2,z332,z3,z4,z95])],[(0,[z204,z7,z2,z97,z4,z5]),(0,[z1,z2,z815,z3,z4,z6]),(0,[z1,z112,z214,z4,z5,z6]),(0,[z1,z2,z103,z29,z38,z6])],[(0,[z138,z85,z2,z32,z3,z6])],[(0,[z1,z2,z282,z3,z223,z6]),(0,[z28,z1,z2,z3,z788,z5])],[(0,[z1,z2,z3,z4,z163,z135]),(0,[z1,z112,z32,z3,z109,z6])]],
   [[(0,[z1,z2,z1220,z4,z5,z6]),(0,[z1,z450,z3,z37,z5,z6])],[(0,[z99,z1,z2,z156,z4,z5]),(0,[z7,z1,z2,z3,z4,z19]),(0,[z1,z2,z3,z4,z5,z1221]),(0,[z1,z2,z1222,z3,z4,z5]),(0,[z1,z2,z32,z3,z58,z296])],[(0,[z1,z2,z984,z4,z5,z6]),(0,[z9,z1,z54,z285,z5,z6]),(0,[z1,z2,z4,z719,z76,z6])],[(0,[z72,z106,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z976,z6]),(0,[z28,z1,z2,z3,z4,z712]),(0,[z7,z1,z2,z3,z4,z717]),(0,[z1,z2,z67,z716,z5,z6])],[(0,[z28,z1,z128,z3,z37,z5]),(0,[z1223,z2,z3,z4,z5,z6]),(0,[z1,z2,z1224,z3,z4,z6])],[(0,[z99,z1,z2,z3,z4,z132]),(0,[z1,z2,z3,z724,z346,z6]),(0,[z1,z2,z3,z4,z5,z271]),(0,[z1,z2,z3,z4,z6,z1225]),(0,[z1,z2,z3,z1226,z5,z6])],[(0,[z1,z2,z3,z4,z1227,z6]),(0,[z1,z2,z282,z3,z78,z6]),(0,[z1,z2,z3,z4,z6,z19])],[(0,[z1,z2,z3,z1228,z4,z6]),(0,[z1,z2,z375,z3,z29,z4]),(0,[z1,z2,z32,z156,z4,z6]),(0,[z1,z2,z3,z4,z1229,z6])],[(0,[z1,z2,z1230,z3,z4,z6]),(0,[z1,z2,z3,z4,z1231,z6]),(0,[z1,z2,z32,z3,z6,z446]),(0,[z1,z2,z375,z3,z4,z5]),(0,[z28,z1,z1088,z3,z4,z5]),(0,[z1232,z1,z2,z3,z4,z5]),(0,[z28,z2,z3,z4,z522,z5]),(0,[z1,z2,z1233,z4,z5,z6]),(0,[z1,z2,z3,z4,z324,z6]),(0,[z1,z2,z83,z3,z4,z33])],[(0,[z1,z2,z4,z5,z188,z148]),(0,[z1,z2,z3,z4,z5,z1234]),(1,[z1,z2,z156,z346,z5]),(0,[z9,z369,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1161])],[(0,[z1,z2,z3,z4,z329,z6])],[(0,[z1,z2,z3,z4,z5,z1235]),(0,[z2,z3,z4,z5,z200,z189])],[(0,[z1,z2,z48,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1236]),(0,[z1,z2,z168,z156,z4,z5]),(0,[z1,z2,z56,z3,z5,z57])],[(0,[z1,z3,z4,z955,z52,z6]),(0,[z411,z1,z2,z3,z4,z296])],[(0,[z1,z2,z3,z107,z5,z6]),(0,[z150,z2,z3,z4,z155,z6]),(0,[z28,z1,z2,z103,z38,z5])],[(0,[z1,z2,z3,z5,z20,z707]),(0,[z1,z15,z3,z253,z5,z6]),(0,[z1,z2,z1237,z3,z4,z6]),(0,[z1,z2,z3,z5,z296,z57])]],
   [[(0,[z248,z2,z3,z203,z5,z6])],[(0,[z1,z2,z3,z759,z5,z6]),(0,[z1,z2,z3,z4,z1238,z6]),(0,[z1,z3,z4,z5,z180,z147]),(0,[z28,z1,z2,z32,z3,z57])],[(0,[z1,z2,z1239,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1240]),(0,[z1,z2,z1241,z3,z4,z6]),(0,[z28,z1,z2,z168,z346,z5]),(0,[z28,z1,z2,z3,z861,z253]),(0,[z782,z240,z2,z3,z4,z5])],[(0,[z28,z1,z15,z32,z3,z4]),(0,[z1,z2,z1242,z3,z4,z6])],[(0,[z7,z1,z79,z3,z4,z5]),(0,[z1,z2,z15,z3,z346,z5]),(0,[z7,z1,z2,z3,z4,z1177]),(0,[z1056,z369,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z314,z1234]),(0,[z1,z2,z3,z1243,z5,z6]),(0,[z1,z2,z3,z4,z1244,z6]),(0,[z1,z2,z1245,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1246]),(0,[z28,z1,z2,z3,z1247,z5]),(0,[z369,z7,z2,z3,z4,z5]),(0,[z240,z2,z3,z285,z5,z6]),(0,[z1,z2,z103,z32,z38,z6]),(0,[z248,z2,z3,z29,z4,z6])],[(0,[z1,z2,z3,z4,z1248,z6]),(0,[z1,z2,z744,z4,z5,z6])],[(0,[z1,z2,z3,z1247,z5,z6]),(0,[z1,z2,z3,z253,z5,z61]),(0,[z1,z2,z122,z4,z5,z6])],[(0,[z1,z2,z32,z3,z4,z349]),(0,[z1,z2,z3,z4,z5,z1249]),(0,[z248,z2,z3,z4,z5,z95])],[(0,[z1,z2,z3,z1250,z5,z6]),(0,[z7,z1,z2,z32,z3,z153]),(0,[z1,z1251,z2,z3,z4,z5]),(0,[z1,z2,z32,z3,z512,z6]),(0,[z1,z2,z32,z3,z147,z57]),(0,[z1,z2,z441,z4,z5,z120])],[(0,[z138,z1,z2,z32,z3,z33]),(0,[z7,z1,z2,z67,z119,z5]),(0,[z1,z2,z3,z285,z30,z6]),(0,[z1,z1252,z2,z3,z4,z5])],[(0,[z1,z2,z1253,z3,z4,z6]),(0,[z35,z2,z3,z4,z155,z20]),(0,[z7,z1,z2,z3,z29,z4]),(0,[z1,z2,z3,z316,z301,z6]),(0,[z1,z2,z3,z4,z30,z182])],[(0,[z530,z2,z97,z4,z5,z6]),(0,[z28,z1,z2,z3,z1243,z5]),(0,[z1,z2,z32,z3,z120,z57])],[(0,[z1,z2,z3,z4,z314,z6]),(0,[z499,z1,z2,z32,z3,z6]),(0,[z1,z2,z3,z861,z4,z6]),(0,[z1,z2,z32,z3,z4,z839])],[(0,[z1,z112,z3,z285,z5,z6]),(0,[z1,z2,z3,z4,z1254,z6]),(0,[z1,z2,z32,z3,z153,z57])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 499) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 499).take 493) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 992).take 402) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1394)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [499, 493, 402] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 114).take 123).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 237).take 127).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 364).take 133).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 497).take 15).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [114, 123, 127, 133, 15] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_38801

theorem PEqualNP.Outside.L_meta_38801 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4274055360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4274055360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38801.solve
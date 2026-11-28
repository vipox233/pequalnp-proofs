import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40503

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4242596000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x002148416388615c#64 ++ 0x4002148416388615#64 ++ 0x5067d8c7e388e3ff#64 ++ 0xb5067d8c7e388e3f#64 : BitVec 256),
   (0x208b0b1b01bb2cc8#64 ++ 0x8208b0b1b01bb2cc#64 ++ 0xe19b2f3b03ff3ccf#64 ++ 0x7e19b2f3b03ff3cc#64 : BitVec 256),
   (0x0614302c0c0596a1#64 ++ 0x00614302c0c0596a#64 ++ 0xfe1c303c3c0ffffe#64 ++ 0xefe1c303c3c0ffff#64 : BitVec 256),
   (0x1b603dc036d03b0e#64 ++ 0x01b603dc036d03b0#64 ++ 0x3fe03fc03ff03f0d#64 ++ 0xf3fe03fc03ff03f0#64 : BitVec 256),
   (0x8dffc0003b6ec000#64 ++ 0x08dffc0003b6ec00#64 ++ 0xbfffc0003fffc00b#64 ++ 0xebfffc0003fffc00#64 : BitVec 256),
   (0x4fdeb6b680000000#64 ++ 0x04fdeb6b68000000#64 ++ 0xcfffffffc0000007#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x002148416388615c 0x4002148416388615 0x5067d8c7e388e3ff 0xb5067d8c7e388e3f

def z1 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe1c303c3c0ffffe 0xefe1c303c3c0ffff

def z2 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe7ff8fffc0fffff 0xffe7ff8fffc0ffff

def z3 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe03fc03ff03f0d 0xf3fe03fc03ff03f0

def z4 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe19b2f3b03ff3ccf 0x7e19b2f3b03ff3cc

def z5 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcfffffffc0000007 0xfcfffffffc000000

def z6 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbfffc0003fffc00b 0xebfffc0003fffc00

def z7 : W := mkw 0xcffff6bebf6fd6a1 0x0cffff6bebf6fd6a 0xffffffffffffffff 0xffffffffffffffff

def z8 : W := mkw 0x0960000032400000 0x0096000003240000 0x3fe000003ff00009 0xe3fe000003ff0000

def z9 : W := mkw 0x849fc000092ec000 0x0849fc000092ec00 0x801fc000000fc002 0x0801fc000000fc00

def z10 : W := mkw 0x20000b1b00912cc8 0x820000b1b00912cc 0x40002f3b00003cc4 0x140002f3b00003cc

def z11 : W := mkw 0x8d74c0003a44c000 0x08d74c0003a44c00 0x1e64c0003c00c000 0x81e64c0003c00c00

def z12 : W := mkw 0x12003dc004903b0e 0x012003dc004903b0 0x3e003fc03c003f0c 0xf3e003fc03c003f0

def z13 : W := mkw 0x20000b5b40912ddc 0xc20000b5b40912dd 0x40003fffc0003ff4 0x140003fffc0003ff

def z14 : W := mkw 0x0000090000902808 0x0000009000090280 0x21802f0003f03c0d 0x721802f0003f03c0

def z15 : W := mkw 0x208a031a00330c80 0x8208a031a00330c8 0xa198273800771c00 0x4a198273800771c0

def z16 : W := mkw 0x420036b680000000 0x0420036b68000000 0x4067ffffc0000007 0xb4067ffffc000000

def z17 : W := mkw 0x8ffff02c3f6fd6a1 0x08ffff02c3f6fd6a 0xfffff03c3fffffff 0xefffff03c3ffffff

def z18 : W := mkw 0x2615392d0dbfbee9 0x82615392d0dbfbee 0xfe1c303c3ffffffe 0xefe1c303c3ffffff

def z19 : W := mkw 0x208a031200320800 0x8208a03120032080 0x0180070000700000 0x0018007000070000

def z20 : W := mkw 0x8dffc8403beee10c 0x08dffc8403beee10 0xbfffd8c03fffe30f 0xfbfffd8c03fffe30

def z21 : W := mkw 0x8d75c0003b4cc000 0x08d75c0003b4cc00 0x1e67c0003f88c00b 0xa1e67c0003f88c00

def z22 : W := mkw 0x000008414080215c 0x4000008414080215 0x400018c7c00023f4 0x1400018c7c00023f

def z23 : W := mkw 0x09eb0000336a0000 0x009eb0000336a000 0xbffb00003fff000b 0xebffb00003fff000

def z24 : W := mkw 0x3beb3fdb37fb3fce 0x83beb3fdb37fb3fc 0xfffb3ffb3fff3fcf 0xffffb3ffb3fff3fc

def z25 : W := mkw 0x002148416388615c 0x4002148416388615 0x0063c8c3c3800001 0x10063c8c3c380000

def z26 : W := mkw 0x002008402280210c 0x0002008402280210 0x106018c02380230d 0xb106018c02380230

def z27 : W := mkw 0x1b40358014501a02 0x01b40358014501a0 0x2f8027001c701c00 0x42f8027001c701c0

def z28 : W := mkw 0x208a0b1a00b32c88 0x8208a0b1a00b32c8 0xa1982f3803f73c0d 0x7a1982f3803f73c0

def z29 : W := mkw 0x008a000000220000 0x0008a00000022000 0xa198000000770000 0x4a19800000077000

def z30 : W := mkw 0x0000000800010480 0x0000000080001048 0x4000203800003cc4 0x04000203800003cc

def z31 : W := mkw 0x0200390004903a08 0x00200390004903a0 0x3f803f003ff03f0d 0xf3f803f003ff03f0

def z32 : W := mkw 0x269f3b3f0dbfbee9 0x8269f3b3f0dbfbee 0xff9f3f3f3fffffff 0xfff9f3f3f3ffffff

def z33 : W := mkw 0x1b6034c036401306 0x01b6034c03640130 0x1e6010c03c000300 0x81e6010c03c00030

def z34 : W := mkw 0x1b617dc177d87b5e 0x41b617dc177d87b5 0x7fe7ffc7fff8ffff 0xf7fe7ffc7fff8fff

def z35 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe1ffffffc3ff3ccf 0xfe1ffffffc3ff3cc

def z36 : W := mkw 0x8dde800018668000 0x08dde80001866800 0xaf9800001c770000 0x4af9800001c77000

def z37 : W := mkw 0x8dffc8417beee15c 0x48dffc8417beee15 0xbfffc8c3ffffc00b 0xfbfffc8c3ffffc00

def z38 : W := mkw 0x002148416388615c 0x4002148416388615 0x5007c007e388e3fa 0x05007c007e388e3f

def z39 : W := mkw 0x4b4036b680000000 0x04b4036b68000000 0x4fe03fffc0000005 0xf4fe03fffc000000

def z40 : W := mkw 0x002008416280215c 0x4002008416280215 0x506018c7e38023fd 0xb506018c7e38023f

def z41 : W := mkw 0x89ebc84173ea615c 0x489ebc84173ea615 0x01e3c8c3c3f00001 0x101e3c8c3c3f0000

def z42 : W := mkw 0x19600dc036d03b0e 0x019600dc036d03b0 0x31e00fc03ff03f09 0x131e00fc03ff03f0

def z43 : W := mkw 0x0415402d490dc4f1 0x40415402d490dc4f 0xc01fc03fc00fc0f2 0x0c01fc03fc00fc0f

def z44 : W := mkw 0x8dffc8417beee15c 0x48dffc8417beee15 0xffffd8c7ffffe3ff 0xfffffd8c7ffffe3f

def z45 : W := mkw 0x00000008080584a1 0x000000008080584a 0x00000000000fc0f0 0x000000000000fc0f

def z46 : W := mkw 0x0000000800010480 0x0000000080001048 0xe0182038000f3cce 0x6e0182038000f3cc

def z47 : W := mkw 0x002148416388615c 0x4002148416388615 0x500410042388e3fe 0xa500410042388e3f

def z48 : W := mkw 0x269e333e0c379ea1 0x8269e333e0c379ea 0xaf9827381c771c00 0x4af9827381c771c0

def z49 : W := mkw 0x902149403ffefb0e 0x0902149403ffefb0 0x300000003fffff08 0x0300000003fffff0

def z50 : W := mkw 0x0000000000000000 0x0000000000000000 0x100400002008c00a 0xa100400002008c00

def z51 : W := mkw 0x0414000008048000 0x0041400000804800 0xbe1c00003c0fc00a 0xebe1c00003c0fc00

def z52 : W := mkw 0x628b3fbf81bb2cc8 0x8628b3fbf81bb2cc 0xe19b3fffc3ff3ccf 0x7e19b3fffc3ff3cc

def z53 : W := mkw 0x49ebced3e388615c 0x449ebced3e388615 0x01e3cfc3c3800001 0x101e3cfc3c380000

def z54 : W := mkw 0x020030080c0596a1 0x0020030080c0596a 0x3e0030003c0ffffc 0xe3e0030003c0ffff

def z55 : W := mkw 0x869ff02c0d2fd6a1 0x0869ff02c0d2fd6a 0xfe1ff03c3c0ffffe 0xefe1ff03c3c0ffff

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0x500410042008e3fe 0xa500410042008e3f

def z57 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0x8f98273800000000 0x48f9827380000000

def z58 : W := mkw 0xadffcb5b7bffeddc 0xcadffcb5b7bffedd 0xffffffffffffffff 0xffffffffffffffff

def z59 : W := mkw 0x4dde86b680000000 0x04dde86b68000000 0xc1ffcfffc0000003 0x1c1ffcfffc000000

def z60 : W := mkw 0x4bcab6b680000000 0x04bcab6b68000000 0x41e3ffffc0000005 0x141e3ffffc000000

def z61 : W := mkw 0x0b40348000000000 0x00b4034800000000 0x0fe03fc000000005 0xf0fe03fc00000000

def z62 : W := mkw 0x449e823680000000 0x0449e82368000000 0xc01fc03fc0000002 0x0c01fc03fc000000

def z63 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xee1820381c0f3cce 0x6ee1820381c0f3cc

def z64 : W := mkw 0x22003b3f04913ee9 0x822003b3f04913ee 0x40003f3f00003ff4 0x140003f3f00003ff

def z65 : W := mkw 0x4fdeb6b688048000 0x04fdeb6b68804800 0xfffffffffc0fc00f 0xffffffffffc0fc00

def z66 : W := mkw 0x0fdeb02c0c0596a1 0x00fdeb02c0c0596a 0xfffff03c3c0fffff 0xefffff03c3c0ffff

def z67 : W := mkw 0x00ab4000232a4000 0x000ab4000232a400 0xb1ffc00023ffc00b 0xeb1ffc00023ffc00

def z68 : W := mkw 0x0021400023084000 0x0002140002308400 0x1067c0002388c00b 0xa1067c0002388c00

def z69 : W := mkw 0x0200300004001200 0x0020030000400120 0x3e0030003c003f0c 0xe3e0030003c003f0

def z70 : W := mkw 0x0414002c080584a1 0x00414002c080584a 0xc01c003c000fc0f2 0x0c01c003c000fc0f

def z71 : W := mkw 0x0020404062004114 0x4002040406200411 0x5064d0c4e008e3fe 0xa5064d0c4e008e3f

def z72 : W := mkw 0x420036be840116a1 0x0420036be840116a 0x40003fffc0003ff4 0x140003fffc0003ff

def z73 : W := mkw 0x2000010800330c80 0x82000010800330c8 0x2000000000771c00 0x02000000000771c0

def z74 : W := mkw 0x1020004036401306 0x0102000403640130 0x100000003c000300 0x0100000003c00030

def z75 : W := mkw 0x30ab0b5b37fb3fce 0x830ab0b5b37fb3fc 0xf19b2f3b3fff3fcf 0x7f19b2f3b3fff3fc

def z76 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0x3e0410043c0ffff8 0x83e0410043c0ffff

def z77 : W := mkw 0xa49fc21b092fc4c0 0x8a49fc21b092fc4c 0xc01fc03b000fc0c2 0x0c01fc03b000fc0c

def z78 : W := mkw 0x0634386c2e85b7ad 0x00634386c2e85b7a 0xfe7c38fc3f8fffff 0xffe7c38fc3f8ffff

def z79 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x01e03fc003f03f05 0x101e03fc003f03f0

def z80 : W := mkw 0x8dffc0407b6ec114 0x48dffc0407b6ec11 0xbfffd0c4ffffc33b 0xebfffd0c4ffffc33

def z81 : W := mkw 0x002148416388615c 0x4002148416388615 0x100000002388e3f8 0x0100000002388e3f

def z82 : W := mkw 0x4ffffef7e388615c 0x44ffffef7e388615 0xdfffffffe388e3ff 0xfdfffffffe388e3f

def z83 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000002008e3f8 0x0100000002008e3f

def z84 : W := mkw 0x20ab4b5b63bb6ddc 0xc20ab4b5b63bb6dd 0xe1fbeffbc3ff3ccf 0x7e1fbeffbc3ff3cc

def z85 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xee1c203c1c0fdcf2 0x4ee1c203c1c0fdcf

def z86 : W := mkw 0x008b0000012a0000 0x0008b0000012a000 0x0183000003f00001 0x00183000003f0000

def z87 : W := mkw 0x20010009012b04c0 0x820010009012b04c 0x00000000000f00c0 0x000000000000f00c

def z88 : W := mkw 0x208b021b012b04c0 0x8208b021b012b04c 0xc19b2f3b000f00c7 0x7c19b2f3b000f00c

def z89 : W := mkw 0x420036b680000000 0x0420036b68000000 0x40003fffc0000004 0x140003fffc000000

def z90 : W := mkw 0x802140003b6ec000 0x0802140003b6ec00 0x300000003fffc008 0x0300000003fffc00

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0x4067d8c7c0000007 0xb4067d8c7c000000

def z92 : W := mkw 0x8dffc8417beee15c 0x48dffc8417beee15 0xbfffc0003fffe3fb 0xebfffc0003fffe3f

def z93 : W := mkw 0x8fdeb02c1c6796a1 0x08fdeb02c1c6796a 0xff9c303c3c7ffffe 0xeff9c303c3c7ffff

def z94 : W := mkw 0x1f7434e43e449327 0x01f7434e43e44932 0x1e6410c43c00c330 0x81e6410c43c00c33

def z95 : W := mkw 0x002048416280615c 0x4002048416280615 0x5064d8c7e000e3f4 0x95064d8c7e000e3f

def z96 : W := mkw 0x0635786d6f8df7fd 0x40635786d6f8df7f 0xfe7ff8ffff8fffff 0xffe7ff8ffff8ffff

def z97 : W := mkw 0x49ca869280000000 0x049ca86928000000 0x0180070000000000 0x0018007000000000

def z98 : W := mkw 0x0940000010400000 0x0094000001040000 0x2f8000001c700000 0x42f8000001c70000

def z99 : W := mkw 0x269f3b3f0dbfbee9 0x8269f3b3f0dbfbee 0xef9b2f3b1fff3ccf 0x7ef9b2f3b1fff3cc

def z100 : W := mkw 0x0021400023084000 0x0002140002308400 0x100000002388c008 0x0100000002388c00

def z101 : W := mkw 0x4fdeb6be8c0596a1 0x04fdeb6be8c0596a 0xaf9827381c071c00 0x4af9827381c071c0

def z102 : W := mkw 0x2001090901bb2cc8 0x82001090901bb2cc 0x2000000003ff3cc8 0x02000000003ff3cc

def z103 : W := mkw 0x4fdeb6be8c0596a1 0x04fdeb6be8c0596a 0xfffffffffc0fffff 0xffffffffffc0ffff

def z104 : W := mkw 0x8dffc0083f6fd6a1 0x08dffc0083f6fd6a 0xbfffc0003ffffffb 0xebfffc0003ffffff

def z105 : W := mkw 0x16143dec0c95bfaf 0x016143dec0c95bfa 0xfe1c3ffc3c0ffffe 0xffe1c3ffc3c0ffff

def z106 : W := mkw 0x8d75c8417bcce15c 0x48d75c8417bcce15 0x5e67d8c7ff88e3ff 0xb5e67d8c7ff88e3f

def z107 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xffffd8c7ffffc00f 0xfffffd8c7ffffc00

def z108 : W := mkw 0x12003dec04913faf 0x012003dec04913fa 0x40003ffc00003ff4 0x140003ffc00003ff

def z109 : W := mkw 0x0960000032400000 0x0096000003240000 0x01e0000003f00001 0x001e0000003f0000

def z110 : W := mkw 0x000000080c0596a1 0x0000000080c0596a 0x300000003c0ffff8 0x0300000003c0ffff

def z111 : W := mkw 0x49ca869280000000 0x049ca86928000000 0x01e3cfc3c0000001 0x101e3cfc3c000000

def z112 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xc01c303c000ffff6 0x0c01c303c000ffff

def z113 : W := mkw 0x061430240c049221 0x0061430240c04922 0xde1c303c3c00c336 0xede1c303c3c00c33

def z114 : W := mkw 0x1960094036d03b0e 0x01960094036d03b0 0x3fe000003ff03f09 0xe3fe000003ff03f0

def z115 : W := mkw 0x8dfe80003a668000 0x08dfe80003a66800 0xbff800003ff70009 0xebff800003ff7000

def z116 : W := mkw 0x208b0b5b41bb2ddc 0xc208b0b5b41bb2dd 0xe19b3fffc3ff3fff 0x7e19b3fffc3ff3ff

def z117 : W := mkw 0x19600dc032d0290e 0x019600dc032d0290 0x01e00fc003f00001 0x101e00fc003f0000

def z118 : W := mkw 0x0001400141084050 0x4000140014108405 0x4007c007c008c0f2 0x04007c007c008c0f

def z119 : W := mkw 0x20ab4b1b23bb6cc8 0x820ab4b1b23bb6cc 0xf1ffef3b23fffccf 0xff1ffef3b23fffcc

def z120 : W := mkw 0x19600dc032d0290e 0x019600dc032d0290 0x3fe00fc03ff00009 0xf3fe00fc03ff0000

def z121 : W := mkw 0x4414802480000000 0x0441480248000000 0x0004c004c0000000 0x00004c004c000000

def z122 : W := mkw 0xcffff6b6bb6ec000 0x0cffff6b6bb6ec00 0xffffffffffffc00f 0xfffffffffffffc00

def z123 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xee18303c1c073ff4 0x4ee18303c1c073ff

def z124 : W := mkw 0x002148416388615c 0x4002148416388615 0x1067c8c3e388c00b 0xb1067c8c3e388c00

def z125 : W := mkw 0x1f743dec3ed5bfaf 0x01f743dec3ed5bfa 0xbff83ff83ff73f0d 0xfbff83ff83ff73f0

def z126 : W := mkw 0x208b4b1b41bb6cd8 0xc208b4b1b41bb6cd 0xe19fef3fc3fffcff 0x7e19fef3fc3fffcf

def z127 : W := mkw 0x0001080101882048 0x0000108010188204 0x40030803038820cf 0x340030803038820c

def z128 : W := mkw 0x20ab4b5b63bb6ddc 0xc20ab4b5b63bb6dd 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z129 : W := mkw 0x008a021200000000 0x0008a02120000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z130 : W := mkw 0x89ebc000336a4000 0x089ebc000336a400 0x01e3c00003f00001 0x001e3c00003f0000

def z131 : W := mkw 0x0200302c040116a1 0x00200302c040116a 0x4000303c00003ff4 0x04000303c00003ff

def z132 : W := mkw 0x5f74b4e4b6401306 0x05f74b4e4b640130 0x1e64d0c4fc000300 0x81e64d0c4fc00030

def z133 : W := mkw 0x1940058010500802 0x0194005801050080 0x0180070000700000 0x0018007000070000

def z134 : W := mkw 0x208a031a00330c80 0x8208a031a00330c8 0xe1982738007f3cce 0x6e1982738007f3cc

def z135 : W := mkw 0x249f0b3f09bface9 0x8249f0b3f09bface 0xe19f2f3f03fffcff 0x7e19f2f3f03fffcf

def z136 : W := mkw 0xdffffff6bffefb0e 0x0dffffff6bffefb0 0xffffffffffffff0f 0xfffffffffffffff0

def z137 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xbe1820383c0ffff8 0x4be1820383c0ffff

def z138 : W := mkw 0x80ab40003b6ec000 0x080ab40003b6ec00 0xb19b00003fffc00b 0x6b19b00003fffc00

def z139 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xf19f3f3f23ffffff 0xff19f3f3f23fffff

def z140 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0x8fffe73800000003 0xe8fffe7380000000

def z141 : W := mkw 0x249f023f092f84e1 0x8249f023f092f84e 0xc01f003f000fc0f2 0x0c01f003f000fc0f

def z142 : W := mkw 0x002008402280210c 0x0002008402280210 0x5067d8c7e380230f 0xb5067d8c7e380230

def z143 : W := mkw 0x2001090901bb2cc8 0x82001090901bb2cc 0x21802f0003ff3ccd 0x721802f0003ff3cc

def z144 : W := mkw 0x0021400163084050 0x4002140016308405 0x5067c007e388c0fb 0xa5067c007e388c0f

def z145 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xbe1c20383c0fdc0a 0xebe1c20383c0fdc0

def z146 : W := mkw 0x0940048000000000 0x0094004800000000 0x01e00fc000000001 0x101e00fc00000000

def z147 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0x0fe7dfc7c0000001 0x90fe7dfc7c000000

def z148 : W := mkw 0x1f743de43ed4bb2f 0x01f743de43ed4bb2 0x3fe43fc43ff0ff3d 0xf3fe43fc43ff0ff3

def z149 : W := mkw 0x000008414080215c 0x4000008414080215 0x000008c3c0000000 0x1000008c3c000000

def z150 : W := mkw 0x0614302400000000 0x0061430240000000 0xde1c303c2008e3fe 0xede1c303c2008e3f

def z151 : W := mkw 0x0000000800010480 0x0000000080001048 0xc0180038000f00c2 0x0c0180038000f00c

def z152 : W := mkw 0x120034c004001306 0x0120034c00400130 0x000010c000000300 0x0000010c00000030

def z153 : W := mkw 0x002008402280210c 0x0002008402280210 0x006008c003800001 0x1006008c00380000

def z154 : W := mkw 0x0414002c080584a1 0x00414002c080584a 0x8018003800070000 0x0801800380007000

def z155 : W := mkw 0x32003fdb04913fce 0x832003fdb04913fc 0x40003ffb00003fc4 0x140003ffb00003fc

def z156 : W := mkw 0x1b603dc176d03b5e 0x41b603dc176d03b5 0x7fe03fc7fff03ffd 0xf7fe03fc7fff03ff

def z157 : W := mkw 0x49ca869280000000 0x049ca86928000000 0xc1fbeffbc0000007 0x7c1fbeffbc000000

def z158 : W := mkw 0x449e823e880584a1 0x0449e823e880584a 0xc01fc03fc00fc0f2 0x0c01fc03fc00fc0f

def z159 : W := mkw 0x0001480141886058 0x4000148014188605 0x4007c807c388e0ff 0x34007c807c388e0f

def z160 : W := mkw 0x0000000140000050 0x4000000014000005 0x40000007c00000f0 0x040000007c00000f

def z161 : W := mkw 0x1b603dc032d0290e 0x01b603dc032d0290 0x0fe03fc003f00005 0xf0fe03fc003f0000

def z162 : W := mkw 0x5ffebff6b6d03b0e 0x05ffebff6b6d03b0 0xfffffffffff03f0f 0xffffffffffff03f0

def z163 : W := mkw 0xadde831a18778c80 0x8adde831a18778c8 0xaf9827381c771c00 0x4af9827381c771c0

def z164 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xbe1830383c073f0c 0xebe1830383c073f0

def z165 : W := mkw 0x2001090901bb2cc8 0x82001090901bb2cc 0xe018203803ff3cce 0x6e018203803ff3cc

def z166 : W := mkw 0x4f75fce5e388615c 0x44f75fce5e388615 0x5e67d8c7e388e3ff 0xb5e67d8c7e388e3f

def z167 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xffffd0043fffe3ff 0xeffffd0043fffe3f

def z168 : W := mkw 0x002009402290290c 0x0002009402290290 0x31e03fc023f03f0d 0xf31e03fc023f03f0

def z169 : W := mkw 0x200109090dbfbee9 0x8200109090dbfbee 0x300000003ffffff8 0x0300000003ffffff

def z170 : W := mkw 0xcfdff6b6892ec000 0x0cfdff6b6892ec00 0xcfffffffc00fc007 0xfcfffffffc00fc00

def z171 : W := mkw 0xadffcb1b3bffecc8 0x8adffcb1b3bffecc 0xffffef3b3ffffccf 0xfffffef3b3ffffcc

def z172 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0180000000f000a 0x6a0180000000f000

def z173 : W := mkw 0x8dffc0083b6fc480 0x08dffc0083b6fc48 0xffffe0383ffffccf 0xeffffe0383ffffcc

def z174 : W := mkw 0x5fdeb7b694501a02 0x05fdeb7b694501a0 0xaf9827381c701c00 0x4af9827381c701c0

def z175 : W := mkw 0x12003dc004903b0e 0x012003dc004903b0 0x00003fc000003f04 0x100003fc000003f0

def z176 : W := mkw 0x649f823f812b04c0 0x8649f823f812b04c 0xc01fc03fc00f00c2 0x0c01fc03fc00f00c

def z177 : W := mkw 0x000108414188215c 0x4000108414188215 0x400318c7c38823ff 0x3400318c7c38823f

def z178 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xa198273803ff3cc8 0x4a198273803ff3cc

def z179 : W := mkw 0x002148416388615c 0x4002148416388615 0x1063d8c3e380230d 0xb1063d8c3e380230

def z180 : W := mkw 0x89ebc84173ea615c 0x489ebc84173ea615 0x51e7d8c7e3f8e3ff 0xb51e7d8c7e3f8e3f

def z181 : W := mkw 0x1b403dc004903b0e 0x01b403dc004903b0 0x0fe03fc000003f05 0xf0fe03fc000003f0

def z182 : W := mkw 0x8dffc0017b6ec050 0x48dffc0017b6ec05 0xffffc007ffffc0fb 0xeffffc007ffffc0f

def z183 : W := mkw 0x1b6074c076405316 0x41b6074c07640531 0x1e64d0c4fc00c330 0x81e64d0c4fc00c33

def z184 : W := mkw 0x0615382d0d8db6e9 0x00615382d0d8db6e 0xfe1f383f3f8fffff 0xffe1f383f3f8ffff

def z185 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xbe1c303c3c07df30 0xcbe1c303c3c07df3

def z186 : W := mkw 0x4ffff6b6a3084000 0x04ffff6b6a308400 0xdfffffffe388c00f 0xfdfffffffe388c00

def z187 : W := mkw 0x8fdeb02c1c6796a1 0x08fdeb02c1c6796a 0xaf9820381c771c00 0x4af9820381c771c0

def z188 : W := mkw 0x4f54b4a480000000 0x04f54b4a48000000 0x0e64d0c4c0000000 0x80e64d0c4c000000

def z189 : W := mkw 0x049f0000092e8000 0x0049f0000092e800 0xbf9f00003fffc00b 0xebf9f00003fffc00

def z190 : W := mkw 0x449fc237c1084050 0x4449fc237c108405 0xc01fc03fc008c0f2 0x0c01fc03fc008c0f

def z191 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x7fe43fc43ff8ffff 0xf7fe43fc43ff8fff

def z192 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fe0000000000001 0xe0fe000000000000

def z193 : W := mkw 0x0200302c0c0596a1 0x00200302c0c0596a 0x7000303c3c0ffffc 0x07000303c3c0ffff

def z194 : W := mkw 0x0000000800010480 0x0000000080001048 0xf01c303c200ffffe 0xef01c303c200ffff

def z195 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbf9800003fffc008 0x4bf9800003fffc00

def z196 : W := mkw 0x208b021b012b04c0 0x8208b021b012b04c 0xc01b003b000f00c2 0x0c01b003b000f00c

def z197 : W := mkw 0x9ffffdc03ffefb0e 0x09ffffdc03ffefb0 0xbfffffc03fffff0f 0xfbfffffc03fffff0

def z198 : W := mkw 0x0020404062004114 0x4002040406200411 0x5067d8c7e000c337 0xb5067d8c7e000c33

def z199 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcf9c373c00000006 0xecf9c373c0000000

def z200 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xae1820381c071c00 0x4ae1820381c071c0

def z201 : W := mkw 0x0200300004001200 0x0020030000400120 0x2e0020001c001c00 0x42e0020001c001c0

def z202 : W := mkw 0x1020094036d03b0e 0x01020094036d03b0 0x300000003ff03f08 0x0300000003ff03f0

def z203 : W := mkw 0x6fdfbfbf81bb2cc8 0x86fdfbfbf81bb2cc 0xefffffffc3ff3ccf 0xfefffffffc3ff3cc

def z204 : W := mkw 0x0614302c040116a1 0x00614302c040116a 0xce1c303c00003ff6 0xece1c303c00003ff

def z205 : W := mkw 0x0d7400003a448000 0x00d7400003a44800 0xbffc00003fffc00b 0xebffc00003fffc00

def z206 : W := mkw 0x1b603dc83ed5bfaf 0x01b603dc83ed5bfa 0x3fe03fc03ffffffd 0xf3fe03fc03ffffff

def z207 : W := mkw 0x69cb8f9b81bb2cc8 0x869cb8f9b81bb2cc 0xe1fbeffbc3ff3ccf 0x7e1fbeffbc3ff3cc

def z208 : W := mkw 0x0200300004001200 0x0020030000400120 0x0000300000003f04 0x00000300000003f0

def z209 : W := mkw 0x0200302400000000 0x0020030240000000 0x4000303c00000004 0x04000303c0000000

def z210 : W := mkw 0x4fdeb6be840116a1 0x04fdeb6be840116a 0xcfffffffc0003ff7 0xfcfffffffc0003ff

def z211 : W := mkw 0x3b613dc937fb3fce 0x83b613dc937fb3fc 0x3fe03fc03fff3fcd 0xf3fe03fc03fff3fc

def z212 : W := mkw 0x008a021200000000 0x0008a02120000000 0x8198273800000000 0x4819827380000000

def z213 : W := mkw 0x802148417beee15c 0x4802148417beee15 0x300000003fffe3f8 0x0300000003fffe3f

def z214 : W := mkw 0x000148414188615c 0x4000148414188615 0x4007d8c7c008e3f6 0x14007d8c7c008e3f

def z215 : W := mkw 0x2bcb3f9b01bb2cc8 0x82bcb3f9b01bb2cc 0xeffb3ffb03ff3ccf 0xfeffb3ffb03ff3cc

def z216 : W := mkw 0x0020000032400000 0x0002000003240000 0x300000003ff00008 0x0300000003ff0000

def z217 : W := mkw 0x4fdeb6be8c0596a1 0x04fdeb6be8c0596a 0xff9c373c3c0ffffe 0xeff9c373c3c0ffff

def z218 : W := mkw 0x9f74f4c03e44d306 0x09f74f4c03e44d30 0x1e64d0c03c00c300 0x81e64d0c03c00c30

def z219 : W := mkw 0x4000069280000000 0x0400006928000000 0x00000fc3c0000000 0x100000fc3c000000

def z220 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3e6010c03ff03f08 0x83e6010c03ff03f0

def z221 : W := mkw 0x208b0b1301ba2848 0x8208b0b1301ba284 0x41830f0303f820cf 0x341830f0303f820c

def z222 : W := mkw 0x0000000000000000 0x0000000000000000 0x4007c007c0000002 0x04007c007c000000

def z223 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0x8ffcf7fcc0000000 0xc8ffcf7fcc000000

def z224 : W := mkw 0x2000031a00110c80 0x82000031a00110c8 0x0000273800001c00 0x00000273800001c0

def z225 : W := mkw 0xcffffef7fbeee15c 0x4cffffef7fbeee15 0xffffffffffffe3ff 0xfffffffffffffe3f

def z226 : W := mkw 0x208b031a013b0c80 0x8208b031a013b0c8 0xa19b273803ff1c0b 0x6a19b273803ff1c0

def z227 : W := mkw 0x8dffc9003bfee808 0x08dffc9003bfee80 0xbfffef003ffffc0f 0xfbfffef003ffffc0

def z228 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x1e603fc03c003f04 0x91e603fc03c003f0

def z229 : W := mkw 0x49ca869280000000 0x049ca86928000000 0x41e7dfc7c0000007 0xb41e7dfc7c000000

def z230 : W := mkw 0x8dffc8013beee048 0x08dffc8013beee04 0xffffc8033fffe0cf 0xfffffc8033fffe0c

def z231 : W := mkw 0x208b421b412b44d0 0xc208b421b412b44d 0xc01fc03fc00fc0f2 0x0c01fc03fc00fc0f

def z232 : W := mkw 0x0001080101882048 0x0000108010188204 0x4067d8c7c38820cf 0xb4067d8c7c38820c

def z233 : W := mkw 0x0000000000000000 0x0000000000000000 0x4004100400000006 0xa400410040000000

def z234 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xaffbc0001ff70001 0x4affbc0001ff7000

def z235 : W := mkw 0x89ebc0003b6ec000 0x089ebc0003b6ec00 0x31e3c0003fffc009 0x031e3c0003fffc00

def z236 : W := mkw 0x208b090901bb2cc8 0x8208b090901bb2cc 0xa19b000003ff3ccb 0x6a19b000003ff3cc

def z237 : W := mkw 0x061430240c049221 0x0061430240c04922 0x1e0410043c00c330 0x81e0410043c00c33

def z238 : W := mkw 0x1021494177d87b5e 0x41021494177d87b5 0x7067d8c7fff8ffff 0xb7067d8c7fff8fff

def z239 : W := mkw 0x59ea8fd2b2d0290e 0x059ea8fd2b2d0290 0x01e3cfc3c3f00001 0x101e3cfc3c3f0000

def z240 : W := mkw 0x008a021200000000 0x0008a02120000000 0xc19b2f3b00000007 0x7c19b2f3b0000000

def z241 : W := mkw 0x0200300804011680 0x0020030080401168 0xfe1830383c0f3fce 0xefe1830383c0f3fc

def z242 : W := mkw 0x39eb0fd333fa294e 0x839eb0fd333fa294 0x01e30fc303f00001 0x101e30fc303f0000

def z243 : W := mkw 0x0960000032400000 0x0096000003240000 0x1e6000003c000000 0x81e6000003c00000

def z244 : W := mkw 0x1bea3fd236d03b0e 0x01bea3fd236d03b0 0xfffb3ffb3ff03f0f 0xffffb3ffb3ff03f0

def z245 : W := mkw 0xcdffc236bb6ec000 0x0cdffc236bb6ec00 0xffffc03fffffc00b 0xeffffc03fffffc00

def z246 : W := mkw 0x0000010000100800 0x0000001000010080 0x2180270000701c00 0x42180270000701c0

def z247 : W := mkw 0x0614302400000000 0x0061430240000000 0xce1c303c00000006 0xece1c303c0000000

def z248 : W := mkw 0x4f54b4a48c049221 0x04f54b4a48c04922 0x1e64d0c4fc00c330 0x81e64d0c4fc00c33

def z249 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xde1c103c3c0fc3f2 0x8de1c103c3c0fc3f

def z250 : W := mkw 0x002148416388615c 0x4002148416388615 0x4063c8c3c38820cf 0x34063c8c3c38820c

def z251 : W := mkw 0x249f0b1b09bfacc8 0x8249f0b1b09bfacc 0xff9f2f3b3ffffccf 0xfff9f2f3b3ffffcc

def z252 : W := mkw 0x00000008040116a1 0x000000008040116a 0x0000000000003ff0 0x00000000000003ff

def z253 : W := mkw 0x9b617dc03ffefb0e 0x09b617dc03ffefb0 0x3fe03fc03fffff0d 0xf3fe03fc03fffff0

def z254 : W := mkw 0x0001400141084050 0x4000140014108405 0x0003c003c0000000 0x00003c003c000000

def z255 : W := mkw 0x44bfca77e388615c 0x444bfca77e388615 0xd07fd8ffe388e3ff 0xbd07fd8ffe388e3f

def z256 : W := mkw 0x5f74bde4b6d03b0e 0x05f74bde4b6d03b0 0x3fe4ffc4fff03f0d 0xf3fe4ffc4fff03f0

def z257 : W := mkw 0x0021400023084000 0x0002140002308400 0x0063c00003800001 0x00063c0000380000

def z258 : W := mkw 0x1000010014501a02 0x01000010014501a0 0x200000001c701c00 0x0200000001c701c0

def z259 : W := mkw 0x8dde800018668000 0x08dde80001866800 0xafffc0001c770003 0xeafffc0001c77000

def z260 : W := mkw 0x1b60358036501a02 0x01b60358036501a0 0x3fe027003ff01c09 0xe3fe027003ff01c0

def z261 : W := mkw 0x208b0b1301ba2848 0x8208b0b1301ba284 0x01830f0303f00001 0x101830f0303f0000

def z262 : W := mkw 0x069e323e0c0596a1 0x0069e323e0c0596a 0xff9f3f3f3c0fffff 0xfff9f3f3f3c0ffff

def z263 : W := mkw 0x2021494963bb6ddc 0xc2021494963bb6dd 0x3000000023fffff8 0x03000000023fffff

def z264 : W := mkw 0x2001090901bb2cc8 0x82001090901bb2cc 0x6003080303ff3ccf 0x36003080303ff3cc

def z265 : W := mkw 0x1b617dc037d87b0e 0x01b617dc037d87b0 0x3fe7ffc03ff8ff0f 0xf3fe7ffc03ff8ff0

def z266 : W := mkw 0x208b021b012b04c0 0x8208b021b012b04c 0xe01b203b000f3cce 0x6e01b203b000f3cc

def z267 : W := mkw 0x2001090101ba2848 0x82001090101ba284 0x0000000003f00000 0x00000000003f0000

def z268 : W := mkw 0x0200302c040116a1 0x00200302c040116a 0x7e00303c3c003ffc 0xe7e00303c3c003ff

def z269 : W := mkw 0x0000000800010480 0x0000000080001048 0x20000000000f3cc8 0x020000000000f3cc

def z270 : W := mkw 0x0614302400000000 0x0061430240000000 0xce7ff8ffc0000007 0xfce7ff8ffc000000

def z271 : W := mkw 0x000000080c0596a1 0x0000000080c0596a 0x200000001c071c00 0x0200000001c071c0

def z272 : W := mkw 0x0020404062004114 0x4002040406200411 0x1064d0c4e000c330 0x81064d0c4e000c33

def z273 : W := mkw 0x4f54b4a480000000 0x04f54b4a48000000 0x0e00000000000000 0x00e0000000000000

def z274 : W := mkw 0x0961484173c8615c 0x40961484173c8615 0x7fe7d8c7fff8e3ff 0xf7fe7d8c7fff8e3f

def z275 : W := mkw 0x002148416388615c 0x4002148416388615 0x1064d0c4e388e3f8 0x81064d0c4e388e3f

def z276 : W := mkw 0x0dde800000000000 0x00dde80000000000 0x8f98000000000000 0x48f9800000000000

def z277 : W := mkw 0x4dde823680000000 0x04dde82368000000 0xcfffc03fc0000003 0xecfffc03fc000000

def z278 : W := mkw 0x2021494963bb6ddc 0xc2021494963bb6dd 0x7067d8c7e3ffffff 0xb7067d8c7e3fffff

def z279 : W := mkw 0x0414000008048000 0x0041400000804800 0xae1800001c070000 0x4ae1800001c07000

def z280 : W := mkw 0x1b6034c036401306 0x01b6034c03640130 0x3e6030c03c003f0c 0xe3e6030c03c003f0

def z281 : W := mkw 0x1634396c3ed5bfaf 0x01634396c3ed5bfa 0xfe1c303c3ffffffe 0xefe1c303c3ffffff

def z282 : W := mkw 0x0200386d448137fd 0x40200386d448137f 0x400038ffc0003ff4 0x1400038ffc0003ff

def z283 : W := mkw 0x1b403dc014d03b0e 0x01b403dc014d03b0 0x2f803fc01c703f04 0x52f803fc01c703f0

def z284 : W := mkw 0x0001400141084050 0x4000140014108405 0x4067d8c7c008c0f7 0xb4067d8c7c008c0f

def z285 : W := mkw 0x428a36b680000000 0x0428a36b68000000 0xc19b3fffc0000007 0x7c19b3fffc000000

def z286 : W := mkw 0x208a031a00330c80 0x8208a031a00330c8 0xe19b2f3b00771c07 0x7e19b2f3b00771c0

def z287 : W := mkw 0x84bfc8416baee15c 0x484bfc8416baee15 0xd07fd8c7e38fe3ff 0xbd07fd8c7e38fe3f

def z288 : W := mkw 0x26143b3f0c95bee9 0x826143b3f0c95bee 0xfe1c3f3f3c0ffffe 0xffe1c3f3f3c0ffff

def z289 : W := mkw 0xcffff6b6b36a4000 0x0cffff6b6b36a400 0xcfffffffc3f00007 0xfcfffffffc3f0000

def z290 : W := mkw 0x208b021b012b04c0 0x8208b021b012b04c 0xe19b003b03ff00cb 0x6e19b003b03ff00c

def z291 : W := mkw 0x002008402280210c 0x0002008402280210 0x1000000023802308 0x0100000002380230

def z292 : W := mkw 0xadffc31a3b7fcc80 0x8adffc31a3b7fcc8 0xbfffe7383fffdc0b 0xebfffe7383fffdc0

def z293 : W := mkw 0x0b40348000000000 0x00b4034800000000 0x0e6010c000000000 0x80e6010c00000000

def z294 : W := mkw 0x19614dc173d8695e 0x419614dc173d8695 0x51e7dfc7e3f8e3ff 0xb51e7dfc7e3f8e3f

def z295 : W := mkw 0x461436be8c0596a1 0x0461436be8c0596a 0xfe1c3ffffc0ffffe 0xffe1c3ffffc0ffff

def z296 : W := mkw 0x8ffff86d7feff7fd 0x48ffff86d7feff7f 0xfffff8ffffffffff 0xffffff8fffffffff

def z297 : W := mkw 0x8000000018668000 0x0800000001866800 0x200000001c770000 0x0200000001c77000

def z298 : W := mkw 0x000000000c049221 0x0000000000c04922 0x100000003c00c330 0x0100000003c00c33

def z299 : W := mkw 0x649f8b3f81bb2cc8 0x8649f8b3f81bb2cc 0xe19fef3fc3ff3ccf 0x7e19fef3fc3ff3cc

def z300 : W := mkw 0xcfdeb6b698668000 0x0cfdeb6b69866800 0xaf9827381c770000 0x4af9827381c77000

def z301 : W := mkw 0x12003dc144903b5e 0x412003dc144903b5 0x40003fc7c0003ff4 0x140003fc7c0003ff

def z302 : W := mkw 0x4fdff6b7c1084050 0x44fdff6b7c108405 0xcfffffffc008c0f7 0xfcfffffffc008c0f

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0x4003080300000007 0x3400308030000000

def z304 : W := mkw 0x002149416398695c 0x4002149416398695 0x71e7ffc7e3f8ffff 0xf71e7ffc7e3f8fff

def z305 : W := mkw 0x9fdeb5801c769a02 0x09fdeb5801c769a0 0xaf9827001c771c00 0x4af9827001c771c0

def z306 : W := mkw 0x461436b680000000 0x0461436b68000000 0xce1c3fffc0000006 0xfce1c3fffc000000

def z307 : W := mkw 0x20ab4a5b63ab65dc 0xc20ab4a5b63ab65d 0xd07fd8ffe38fe3ff 0xbd07fd8ffe38fe3f

def z308 : W := mkw 0x4f54b4a480000000 0x04f54b4a48000000 0x0fe4ffc4c0000005 0xf0fe4ffc4c000000

def z309 : W := mkw 0x4ffffef7e388615c 0x44ffffef7e388615 0xcfffffffc3800007 0xfcfffffffc380000

def z310 : W := mkw 0x1f743dec3ed5bfaf 0x01f743dec3ed5bfa 0xfffc3ffc3fffffff 0xffffc3ffc3ffffff

def z311 : W := mkw 0x69cb8f9381ba2848 0x869cb8f9381ba284 0x01e3cfc3c3f00001 0x101e3cfc3c3f0000

def z312 : W := mkw 0x000008414080215c 0x4000008414080215 0x500418c7e008e3fe 0xb500418c7e008e3f

def z313 : W := mkw 0x0960090032d02808 0x00960090032d0280 0x3fe02f003ff03c0d 0xf3fe02f003ff03c0

def z314 : W := mkw 0x2ddf8b1b01bb2cc8 0x82ddf8b1b01bb2cc 0xefffef3b03ff3ccf 0xfefffef3b03ff3cc

def z315 : W := mkw 0x3beb7fdb77fb7fde 0xc3beb7fdb77fb7fd 0xffffffffffffffff 0xffffffffffffffff

def z316 : W := mkw 0x002148496f8df7fd 0x4002148496f8df7f 0x7067d8c7ff8fffff 0xb7067d8c7ff8ffff

def z317 : W := mkw 0x0000000008048000 0x0000000000804800 0x300000003c0fc008 0x0300000003c0fc00

def z318 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xce7fd0ffc0000002 0x8ce7fd0ffc000000

def z319 : W := mkw 0x002008402280210c 0x0002008402280210 0x506418c42388e3ff 0xb506418c42388e3f

def z320 : W := mkw 0x3fff3fff3fffbfef 0x83fff3fff3fffbfe 0xffff3fff3fffffff 0xfffff3fff3ffffff

def z321 : W := mkw 0x6fdeb7be80330c80 0x86fdeb7be80330c8 0xaf98273800771c00 0x4af98273800771c0

def z322 : W := mkw 0x1021494177d87b5e 0x41021494177d87b5 0x300000003ff8fff8 0x0300000003ff8fff

def z323 : W := mkw 0x0200302404001221 0x0020030240400122 0x0000100400000330 0x0000010040000033

def z324 : W := mkw 0x8d75c0003b6ec000 0x08d75c0003b6ec00 0x3e64c0003fffc008 0x83e64c0003fffc00

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x100410042000c330 0x8100410042000c33

def z326 : W := mkw 0x208a021a00230480 0x8208a021a0023048 0x8018003800070000 0x0801800380007000

def z327 : W := mkw 0x1020094032d0290e 0x01020094032d0290 0x0000000003f00000 0x00000000003f0000

def z328 : W := mkw 0x09ca800000000000 0x009ca80000000000 0x01e3c00000000001 0x001e3c0000000000

def z329 : W := mkw 0x20ab4b5363ba695c 0xc20ab4b5363ba695 0x51e7dfc7e3f8e3ff 0xb51e7dfc7e3f8e3f

def z330 : W := mkw 0x0200300004001200 0x0020030000400120 0x1e0010003c000300 0x81e0010003c00030

def z331 : W := mkw 0x8ffff0003f6ed200 0x08ffff0003f6ed20 0xbffff0003fffff0f 0xebffff0003fffff0

def z332 : W := mkw 0x802140083f6fd6a1 0x0802140083f6fd6a 0x300000003ffffff8 0x0300000003ffffff

def z333 : W := mkw 0x8f74f02c3e45d6a1 0x08f74f02c3e45d6a 0xfe7cf03c3c0ffffe 0xefe7cf03c3c0ffff

def z334 : W := mkw 0x9dffcdc03bfee90e 0x09dffcdc03bfee90 0xbfffcfc03fffc00b 0xfbfffcfc03fffc00

def z335 : W := mkw 0x002148416388615c 0x4002148416388615 0x1063c8c3e388e3f9 0x11063c8c3e388e3f

def z336 : W := mkw 0x0b40348000000000 0x00b4034800000000 0x0f80270000000000 0x40f8027000000000

def z337 : W := mkw 0x8dffc000336a4000 0x08dffc000336a400 0x8fffc00003f00003 0xe8fffc00003f0000

def z338 : W := mkw 0x00010809018924c8 0x000010809018924c 0xe01b283b038f3ccf 0x7e01b283b038f3cc

def z339 : W := mkw 0x5beabfd2b6d03b0e 0x05beabfd2b6d03b0 0x3fe3ffc3fff03f0d 0xf3fe3ffc3fff03f0

def z340 : W := mkw 0x1b617cc177c8735e 0x41b617cc177c8735 0x5e67d8c7ff88e3ff 0xb5e67d8c7ff88e3f

def z341 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0x5e04303c3c00fff4 0x85e04303c3c00fff

def z342 : W := mkw 0x0b60348032400000 0x00b6034803240000 0x3fe03fc03ff0000d 0xf3fe03fc03ff0000

def z343 : W := mkw 0x1020094036d03b0e 0x01020094036d03b0 0x306018c03ff03f0d 0xb306018c03ff03f0

def z344 : W := mkw 0xcdffc692bb6ec000 0x0cdffc692bb6ec00 0xbfffcfc3ffffc00b 0xfbfffcfc3ffffc00

def z345 : W := mkw 0x002148416388615c 0x4002148416388615 0x106018c02388e3fd 0xb106018c02388e3f

def z346 : W := mkw 0x008b0000012a0000 0x0008b0000012a000 0xa19b000003ff000b 0x6a19b000003ff000

def z347 : W := mkw 0x10000dc00090290e 0x010000dc00090290 0x00000fc000000000 0x100000fc00000000

def z348 : W := mkw 0x0414000000000000 0x0041400000000000 0x8e1c000000000002 0xe8e1c00000000000

def z349 : W := mkw 0x5ffeb6f6b6401306 0x05ffeb6f6b640130 0xdffffffffc000307 0xfdffffffffc00030

def z350 : W := mkw 0x1b6035c036501b06 0x01b6035c036501b0 0x3fe037c03c701f00 0xc3fe037c03c701f0

def z351 : W := mkw 0x0634706c6e05d7b5 0x40634706c6e05d7b 0xfe7cf0fcfc0ffffe 0xefe7cf0fcfc0ffff

def z352 : W := mkw 0x1b603dec36d13faf 0x01b603dec36d13fa 0x7fe03ffc3ff03ffd 0xf7fe03ffc3ff03ff

def z353 : W := mkw 0x2000090900912cc8 0x82000090900912cc 0x0000000000003cc0 0x00000000000003cc

def z354 : W := mkw 0x0dde800000000000 0x00dde80000000000 0x8fffc00000000003 0xe8fffc0000000000

def z355 : W := mkw 0x008b080101aa2048 0x0008b080101aa204 0xe19b080303ff20cf 0x7e19b080303ff20c

def z356 : W := mkw 0xcfdeb6b698668000 0x0cfdeb6b69866800 0xefffffffdc770007 0xfefffffffdc77000

def z357 : W := mkw 0x19600dc032d0290e 0x019600dc032d0290 0x21e02fc003f03c0d 0x721e02fc003f03c0

def z358 : W := mkw 0x0020000022000000 0x0002000002200000 0x1060000023800009 0xa106000002380000

def z359 : W := mkw 0x4fdfbeb781882048 0x04fdfbeb78188204 0xcfffffffc38820cf 0xfcfffffffc38820c

def z360 : W := mkw 0x9ffebdc03ef6bb0e 0x09ffebdc03ef6bb0 0xbff83fc03ff73f0d 0xfbff83fc03ff73f0

def z361 : W := mkw 0x0614392c0c95bea9 0x00614392c0c95bea 0xff9c3f3c3fffffff 0xfff9c3f3c3ffffff

def z362 : W := mkw 0x0614302c00010480 0x00614302c0001048 0xee1c303c000f3cce 0xeee1c303c000f3cc

def z363 : W := mkw 0x061430240c049221 0x0061430240c04922 0x0e0000001c000000 0x00e0000001c00000

def z364 : W := mkw 0x8f74f0243e44d221 0x08f74f0243e44d22 0x1e64d0043c00c330 0x81e64d0043c00c33

def z365 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0x8ffbeffbc0000001 0x58ffbeffbc000000

def z366 : W := mkw 0x20ab0b5b23bb2dcc 0x820ab0b5b23bb2dc 0xf1fb3ffb23ff3fcf 0xff1fb3ffb23ff3fc

def z367 : W := mkw 0x449e823680000000 0x0449e82368000000 0x8018003800000000 0x0801800380000000

def z368 : W := mkw 0x8414c0000804c000 0x08414c0000804c00 0x0004c0000000c000 0x00004c0000000c00

def z369 : W := mkw 0x208b0213012a0040 0x8208b0213012a004 0x0003000300000000 0x0000300030000000

def z370 : W := mkw 0x80214000336a4000 0x080214000336a400 0x0000000003f00000 0x00000000003f0000

def z371 : W := mkw 0x6fdfb6bf812b04c0 0x86fdfb6bf812b04c 0xcfffffffc00f00c7 0xfcfffffffc00f00c

def z372 : W := mkw 0x449e823680000000 0x0449e82368000000 0xc19fef3fc0000007 0x7c19fef3fc000000

def z373 : W := mkw 0x0001080101882048 0x0000108010188204 0x00000000038820c8 0x000000000038820c

def z374 : W := mkw 0x0dde800000000000 0x00dde80000000000 0xcfffd8c7c0000007 0xfcfffd8c7c000000

def z375 : W := mkw 0x0960084032c0210c 0x00960084032c0210 0x3fe018c03ff0230d 0xf3fe018c03ff0230

def z376 : W := mkw 0x0f5434a400000000 0x00f5434a40000000 0xcffc3ffc00000007 0xfcffc3ffc0000000

def z377 : W := mkw 0x4f54b6b680000000 0x04f54b6b68000000 0x4e64ffffc0000004 0x94e64ffffc000000

def z378 : W := mkw 0x5fdebff684903b0e 0x05fdebff684903b0 0xcfffffffc0003f07 0xfcfffffffc0003f0

def z379 : W := mkw 0x4f54b4a480000000 0x04f54b4a48000000 0x4e67d8c7c0000007 0xb4e67d8c7c000000

def z380 : W := mkw 0x0414002c080584a1 0x00414002c080584a 0xe01c203c000ffcfe 0x6e01c203c000ffcf

def z381 : W := mkw 0x1b607dc076d07b1e 0x41b607dc076d07b1 0x3fe4ffc4fff0ff3d 0xf3fe4ffc4fff0ff3

def z382 : W := mkw 0x4940848080000000 0x0494084808000000 0x0060c0c0c0000000 0x00060c0c0c000000

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x5067d8c7e008e3ff 0xb5067d8c7e008e3f

def z384 : W := mkw 0x0d54800000000000 0x00d5480000000000 0x0e64c00000000000 0x80e64c0000000000

def z385 : W := mkw 0x20010b1b01992cc8 0x820010b1b01992cc 0x40032f3b03883ccf 0x340032f3b03883cc

def z386 : W := mkw 0x063578656388615c 0x4063578656388615 0xde7ff8ffe388e3ff 0xfde7ff8ffe388e3f

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x400400040008c0f2 0x0400400040008c0f

def z388 : W := mkw 0x1b403d8014d03a0a 0x01b403d8014d03a0 0x2f802f001ff03c0d 0x72f802f001ff03c0

def z389 : W := mkw 0x808bc000012a4000 0x0808bc000012a400 0x0003c00000000000 0x00003c0000000000

def z390 : W := mkw 0x19600dc032d0290e 0x019600dc032d0290 0x11e01fc023f0230d 0xb11e01fc023f0230

def z391 : W := mkw 0x20214b5b63996ddc 0xc20214b5b63996dd 0x5067ffffe388ffff 0xb5067ffffe388fff

def z392 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xa19b2f3b03f71c01 0x5a19b2f3b03f71c0

def z393 : W := mkw 0xa49fcb1b09bfecc8 0x8a49fcb1b09bfecc 0xe19fef3b03fffccf 0x7e19fef3b03fffcc

def z394 : W := mkw 0x0414000808058480 0x0041400080805848 0xfe1c20383c0ffcce 0xefe1c20383c0ffcc

def z395 : W := mkw 0x008a021200000000 0x0008a02120000000 0xc01b003b00000002 0x0c01b003b0000000

def z396 : W := mkw 0x0dde800008048000 0x00dde80000804800 0xbfffc0003c0fc00b 0xebfffc0003c0fc00

def z397 : W := mkw 0x9ffffdc17ffefb5e 0x49ffffdc17ffefb5 0xffffffc7ffffffff 0xfffffffc7fffffff

def z398 : W := mkw 0x1b40348014401202 0x01b4034801440120 0x0e0000001c000000 0x00e0000001c00000

def z399 : W := mkw 0x20ab4b5363ba695c 0xc20ab4b5363ba695 0x01e3cfc3c3f00001 0x101e3cfc3c3f0000

def z400 : W := mkw 0x0021404163084154 0x4002140416308415 0x5067d0c7e008c3f2 0x85067d0c7e008c3f

def z401 : W := mkw 0x469eb6b680000000 0x0469eb6b68000000 0xc01fffffc0000006 0x1c01fffffc000000

def z402 : W := mkw 0x4fdeb4a480000000 0x04fdeb4a48000000 0x8fffd0c4c0000003 0xe8fffd0c4c000000

def z403 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3f8027003ff03f08 0x43f8027003ff03f0

def z404 : W := mkw 0x00214849638965dc 0x400214849638965d 0xf07ff8ffe38fffff 0xff07ff8ffe38ffff

def z405 : W := mkw 0x002148402388610c 0x0002148402388610 0x1067d8c02388e30f 0xb1067d8c02388e30

def z406 : W := mkw 0x1ffebdc036d03b0e 0x01ffebdc036d03b0 0xbfffffc03ff03f0f 0xfbfffffc03ff03f0

def z407 : W := mkw 0x0020004022000104 0x0002000402200010 0x106010c020000300 0x8106010c02000030

def z408 : W := mkw 0x4ffef6f6e2004114 0x44ffef6f6e200411 0xdfffffffe000c337 0xfdfffffffe000c33

def z409 : W := mkw 0x0000090800912c88 0x00000090800912c8 0xe1982f3803ff3ccf 0x7e1982f3803ff3cc

def z410 : W := mkw 0x52003ff684903b0e 0x052003ff684903b0 0x40003fffc0003f04 0x140003fffc0003f0

def z411 : W := mkw 0x0001400141084050 0x4000140014108405 0x5007d007e008e3fe 0xa5007d007e008e3f

def z412 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x7fe7ffc7fff03f0f 0xf7fe7ffc7fff03f0

def z413 : W := mkw 0x3bca379a14731e82 0x83bca379a14731e8 0xaf9827381c771c00 0x4af9827381c771c0

def z414 : W := mkw 0xcf74f4a4ba44c000 0x0cf74f4a4ba44c00 0x1e64d0c4fc00c000 0x81e64d0c4fc00c00

def z415 : W := mkw 0x0615702d4d0dd6f1 0x40615702d4d0dd6f 0xfe1ff03ffc0ffffe 0xefe1ff03ffc0ffff

def z416 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcf983fffc0000004 0x5cf983fffc000000

def z417 : W := mkw 0x4fdeb6be880584a1 0x04fdeb6be880584a 0xcfffffffc00fc0f7 0xfcfffffffc00fc0f

def z418 : W := mkw 0x0021400023084000 0x0002140002308400 0x5067d0042388e3ff 0xa5067d0042388e3f

def z419 : W := mkw 0xbfffffdb3fffffce 0x8bfffffdb3fffffc 0xfffffffb3fffffcf 0xffffffffb3fffffc

def z420 : W := mkw 0xcffff6b6bb6ec000 0x0cffff6b6bb6ec00 0xbfffe7383fffc00b 0xebfffe7383fffc00

def z421 : W := mkw 0x1b617dc177d87b5e 0x41b617dc177d87b5 0x3fe3ffc3fff03f0d 0xf3fe3ffc3fff03f0

def z422 : W := mkw 0x000008400080210c 0x0000008400080210 0x000018c000002304 0x1000018c00000230

def z423 : W := mkw 0x8ddfc000196ec000 0x08ddfc000196ec00 0xaf9fc0001c7fc002 0x4af9fc0001c7fc00

def z424 : W := mkw 0x0001400141084050 0x4000140014108405 0x000000000008c0f0 0x0000000000008c0f

def z425 : W := mkw 0x8dffc02c3b6fc4a1 0x08dffc02c3b6fc4a 0xffffc03c3fffc0fb 0xeffffc03c3fffc0f

def z426 : W := mkw 0x20ab4b5b63bb6ddc 0xc20ab4b5b63bb6dd 0xf19b2f3b23ffffff 0x7f19b2f3b23fffff

def z427 : W := mkw 0x0dffc8416388615c 0x40dffc8416388615 0xdfffd8c7e388e3ff 0xfdfffd8c7e388e3f

def z428 : W := mkw 0x000000080c0596a1 0x0000000080c0596a 0x700410043c0ffffe 0xa700410043c0ffff

def z429 : W := mkw 0x5ffebff6b6d03b0e 0x05ffebff6b6d03b0 0xbff83ff83ff03f0d 0xfbff83ff83ff03f0

def z430 : W := mkw 0x0000000000000000 0x0000000000000000 0x40001004000023f4 0x040001004000023f

def z431 : W := mkw 0x0200302c040116a1 0x00200302c040116a 0x5004303c2008fffe 0xa5004303c2008fff

def z432 : W := mkw 0x8960c00032404000 0x08960c0003240400 0x0060c00000000000 0x00060c0000000000

def z433 : W := mkw 0x4ffffeffef8df7fd 0x44ffffeffef8df7f 0xffffffffff8fffff 0xfffffffffff8ffff

def z434 : W := mkw 0x0b40348000000000 0x00b4034800000000 0x4fe7ffc7c0000007 0xf4fe7ffc7c000000

def z435 : W := mkw 0x8dfec0003a66c000 0x08dfec0003a66c00 0xbffcc0003c77c000 0xcbffcc0003c77c00

def z436 : W := mkw 0x8ddf8000196e8000 0x08ddf8000196e800 0xaf9b00001fff000b 0x6af9b00001fff000

def z437 : W := mkw 0x1f5435ac1c559ea3 0x01f5435ac1c559ea 0xaf9827381c771c00 0x4af9827381c771c0

def z438 : W := mkw 0x9ffff4c03f6ed306 0x09ffff4c03f6ed30 0xbfffd0c03fffc30b 0xebfffd0c03fffc30

def z439 : W := mkw 0x208b0b1301ba2848 0x8208b0b1301ba284 0xc19b2f3b03f00007 0x7c19b2f3b03f0000

def z440 : W := mkw 0x0000000000000000 0x0000000000000000 0x3e0000003c000008 0xe3e0000003c00000

def z441 : W := mkw 0x0414000008048000 0x0041400000804800 0x801c0000000fc002 0x0801c0000000fc00

def z442 : W := mkw 0x00010000012a0000 0x000010000012a000 0x2000000003ff0008 0x02000000003ff000

def z443 : W := mkw 0x000008414080215c 0x4000008414080215 0x4067d8c7c00023f7 0xb4067d8c7c00023f

def z444 : W := mkw 0x4fdeb6b68c049221 0x04fdeb6b68c04922 0xdffffffffc00c337 0xfdffffffffc00c33

def z445 : W := mkw 0x0001000001080000 0x0000100000108000 0x000300000388000b 0x2000300000388000

def z446 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x2fe02fc01ff01c01 0x52fe02fc01ff01c0

def z447 : W := mkw 0x002148416388615c 0x4002148416388615 0x4067d8c7c3800007 0xb4067d8c7c380000

def z448 : W := mkw 0x4f54b4ac8c0596a1 0x04f54b4ac8c0596a 0xfe7cf0fcfc0ffffe 0xefe7cf0fcfc0ffff

def z449 : W := mkw 0x1beb3dc037fa3b0e 0x01beb3dc037fa3b0 0xbffb3fc03fff3f0f 0xfbffb3fc03fff3f0

def z450 : W := mkw 0x0961400033484000 0x0096140003348400 0x3fe7c0003ff8c00b 0xe3fe7c0003ff8c00

def z451 : W := mkw 0x4fdeb6b684001200 0x04fdeb6b68400120 0xfffffffffc003f0f 0xffffffffffc003f0

def z452 : W := mkw 0x8ddfc000092ec000 0x08ddfc000092ec00 0x8fffc000000fc003 0xe8fffc000000fc00

def z453 : W := mkw 0x061430000c049200 0x0061430000c04920 0xbe1c30003c0fff0e 0xebe1c30003c0fff0

def z454 : W := mkw 0x12217dc167987b5e 0x412217dc167987b5 0x5067ffc7e388ffff 0xb5067ffc7e388fff

def z455 : W := mkw 0x0614302408048000 0x0061430240804800 0xfe1c303c3c0fc00e 0xefe1c303c3c0fc00

def z456 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xdfffffffe008e3ff 0xfdfffffffe008e3f

def z457 : W := mkw 0x0614302400000000 0x0061430240000000 0x8e18203800000000 0x48e1820380000000

def z458 : W := mkw 0x1f743dc03ed4bb0e 0x01f743dc03ed4bb0 0xbffc3fc03fffff0f 0xfbffc3fc03fffff0

def z459 : W := mkw 0x0000021200000000 0x0000002120000000 0x40002f3b00000004 0x140002f3b0000000

def z460 : W := mkw 0x4f54b4a480000000 0x04f54b4a48000000 0xce7cf0fcc0000006 0xece7cf0fcc000000

def z461 : W := mkw 0x0001080101882048 0x0000108010188204 0x0003080303800001 0x1000308030380000

def z462 : W := mkw 0xadffc21b3b6fc4c0 0x8adffc21b3b6fc4c 0xffffc03b3fffc0cb 0xeffffc03b3fffc0c

def z463 : W := mkw 0x0414002408048021 0x0041400240804802 0x000400040000c030 0x0000400040000c03

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0xc018203800000006 0x6c01820380000000

def z465 : W := mkw 0x4ffebef6a280210c 0x04ffebef6a280210 0xdfffffffe380230f 0xfdfffffffe380230

def z466 : W := mkw 0x0635786d6f8df7fd 0x40635786d6f8df7f 0xfe1c303c3f8ffffe 0xefe1c303c3f8ffff

def z467 : W := mkw 0x8dffc2123b6ec000 0x08dffc2123b6ec00 0xffffef3b3fffc00f 0xfffffef3b3fffc00

def z468 : W := mkw 0x26bf7b7f6fbffffd 0xc26bf7b7f6fbffff 0xffffffffffffffff 0xffffffffffffffff

def z469 : W := mkw 0x5ffebff6b2d0290e 0x05ffebff6b2d0290 0xcfffffffc3f00007 0xfcfffffffc3f0000

def z470 : W := mkw 0x208b0b1301ba2848 0x8208b0b1301ba284 0xa19b0f0303ff000b 0x7a19b0f0303ff000

def z471 : W := mkw 0x5b603ff6b6d03b0e 0x05b603ff6b6d03b0 0x7fe03ffffff03f0d 0xf7fe03ffffff03f0

def z472 : W := mkw 0x1b617dc177d87b5e 0x41b617dc177d87b5 0x3fe03fc03ff8fffd 0xf3fe03fc03ff8fff

def z473 : W := mkw 0x208b0a1b01ab24c8 0x8208b0a1b01ab24c 0xc01b083b038f20cf 0x3c01b083b038f20c

def z474 : W := mkw 0x1200358004101a02 0x01200358004101a0 0x0000270000001c00 0x00000270000001c0

def z475 : W := mkw 0x8d54800018448000 0x08d5480001844800 0x0e0000001c000000 0x00e0000001c00000

def z476 : W := mkw 0x8d74c0407a44c114 0x48d74c0407a44c11 0x1e64d0c4fc00c330 0x81e64d0c4fc00c33

def z477 : W := mkw 0x0000000004001200 0x0000000000400120 0x300000003c003f08 0x0300000003c003f0

def z478 : W := mkw 0x061430240c049221 0x0061430240c04922 0x3e0430043c00ff3c 0xe3e0430043c00ff3

def z479 : W := mkw 0x069f302c0d2f96a1 0x0069f302c0d2f96a 0xff9f303c3fffffff 0xeff9f303c3ffffff

def z480 : W := mkw 0x063470646e04d335 0x4063470646e04d33 0x1e64d0c4fc00c330 0x81e64d0c4fc00c33

def z481 : W := mkw 0x3b603fdb36d13fce 0x83b603fdb36d13fc 0x7fe03ffb3ff03fcd 0xf7fe03ffb3ff03fc

def z482 : W := mkw 0x0000000000000000 0x0000000000000000 0x0063c8c3c0000001 0x10063c8c3c000000

def z483 : W := mkw 0x043540002b0cc000 0x0043540002b0cc00 0xbe7fc0003f8fc00b 0xebe7fc0003f8fc00

def z484 : W := mkw 0x8ffff02c3f6fd6a1 0x08ffff02c3f6fd6a 0xbfffe0383fffdc0b 0xebfffe0383fffdc0

def z485 : W := mkw 0x208b031b013b0cc0 0x8208b031b013b0cc 0xe19b273b007f1cc2 0x4e19b273b007f1cc

def z486 : W := mkw 0x5ffffff7f7d87b5e 0x45ffffff7f7d87b5 0xfffffffffff8ffff 0xffffffffffff8fff

def z487 : W := mkw 0x1b603cc036c0330e 0x01b603cc036c0330 0x1e6018c03f80230d 0xb1e6018c03f80230

def z488 : W := mkw 0x20000b1b00912cc8 0x820000b1b00912cc 0xe0182f3b000f3cce 0x7e0182f3b000f3cc

def z489 : W := mkw 0x80014000092ec000 0x080014000092ec00 0x00000000000fc000 0x000000000000fc00

def z490 : W := mkw 0x99ebcdc033fa690e 0x099ebcdc033fa690 0x01e3cfc003f00001 0x101e3cfc003f0000

def z491 : W := mkw 0x00ab484163aa615c 0x400ab484163aa615 0xf1ffd8c7e3ffe3ff 0xff1ffd8c7e3ffe3f

def z492 : W := mkw 0x0001400001084000 0x0000140000108400 0x0007c0000008c002 0x00007c0000008c00

def z493 : W := mkw 0x0221786d678977fd 0x40221786d678977f 0x5067f8ffe388ffff 0xb5067f8ffe388fff

def z494 : W := mkw 0x0b617cc16388615c 0x40b617cc16388615 0x5fe7ffc7e388e3ff 0xf5fe7ffc7e388e3f

def z495 : W := mkw 0x0000000000000000 0x0000000000000000 0x006018c000000005 0xb006018c00000000

def z496 : W := mkw 0x002148496f8df7fd 0x4002148496f8df7f 0x300000003f8ffff8 0x0300000003f8ffff

def z497 : W := mkw 0x29eb0b1b33fb2cc8 0x829eb0b1b33fb2cc 0xfffb2f3b3fff3ccf 0xffffb2f3b3fff3cc

def z498 : W := mkw 0xa9ebcb1333fa6848 0x8a9ebcb1333fa684 0x01e3cf0303f00001 0x101e3cf0303f0000

def z499 : W := mkw 0xc49fc236892ec000 0x0c49fc236892ec00 0xc01fc03fc00fc002 0x0c01fc03fc00fc00

def z500 : W := mkw 0x269e333e0c379ea1 0x8269e333e0c379ea 0xff9c373c3c7ffffe 0xeff9c373c3c7ffff

def z501 : W := mkw 0x063578656f8cf37d 0x4063578656f8cf37 0x5e67d8c7ff88e3ff 0xb5e67d8c7ff88e3f

def z502 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xc01b2f3b000f3cc6 0x1c01b2f3b000f3cc

def z503 : W := mkw 0x0414002c080584a1 0x00414002c080584a 0xfe1c003c3c0fc0fa 0xefe1c003c3c0fc0f

def z504 : W := mkw 0x041400080c0596a1 0x0041400080c0596a 0xbe1c00003c0ffffa 0xebe1c00003c0ffff

def z505 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xee1c303c1c071c06 0xeee1c303c1c071c0

def z506 : W := mkw 0x0bca369200000000 0x00bca36920000000 0xcffb3ffb00000007 0xfcffb3ffb0000000

def z507 : W := mkw 0xadffc9093bffecc8 0x8adffc9093bffecc 0xbfffc0003ffffccb 0xebfffc0003ffffcc

def z508 : W := mkw 0x9f74fdc03ed4fb0e 0x09f74fdc03ed4fb0 0x3fe4ffc03ff0ff0d 0xf3fe4ffc03ff0ff0

def z509 : W := mkw 0x408a821280000000 0x0408a82128000000 0x0003c003c0000000 0x00003c003c000000

def z510 : W := mkw 0x843540003b6ec000 0x0843540003b6ec00 0xbe1c00003fffc00a 0xebe1c00003fffc00

def z511 : W := mkw 0x0b60300036401200 0x00b6030003640120 0x3fe030003ff03f0d 0xe3fe030003ff03f0

def z512 : W := mkw 0x0020404062004114 0x4002040406200411 0x100000002000c330 0x0100000002000c33

def z513 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcf9b2f3b00000007 0x7cf9b2f3b0000000

def z514 : W := mkw 0x0414002c080584a1 0x00414002c080584a 0xd01c103c200fe3fe 0xad01c103c200fe3f

def z515 : W := mkw 0x008a0b1200902808 0x0008a0b120090280 0xe19b2f3b03f03c0f 0x7e19b2f3b03f03c0

def z516 : W := mkw 0x0dfe800032400000 0x00dfe80003240000 0xbfffc0003ff0000b 0xebfffc0003ff0000

def z517 : W := mkw 0x1000094004903b0e 0x01000094004903b0 0x0000000000003f00 0x00000000000003f0

def z518 : W := mkw 0x002148416388615c 0x4002148416388615 0x500018c7e388e3fc 0x1500018c7e388e3f

def z519 : W := mkw 0x42217ef7e388615c 0x442217ef7e388615 0x5067ffffe388e3ff 0xb5067ffffe388e3f

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z521 : W := mkw 0x4fdeb6be8c0596a1 0x04fdeb6be8c0596a 0xefffffffdc071c07 0xfefffffffdc071c0

def z522 : W := mkw 0xaddf8b1b19ffacc8 0x8addf8b1b19ffacc 0xef9b2f3b1fff3ccf 0x7ef9b2f3b1fff3cc

def z523 : W := mkw 0x6fdebfbf80912cc8 0x86fdebfbf80912cc 0xcfffffffc0003cc7 0xfcfffffffc0003cc

def z524 : W := mkw 0x849fc001492ec050 0x4849fc001492ec05 0xc01fc007c00fc0f2 0x0c01fc007c00fc0f

def z525 : W := mkw 0xadffcb133bfee848 0x8adffcb133bfee84 0xbfffcf033fffc00b 0xfbfffcf033fffc00

def z526 : W := mkw 0x1b40358014501a02 0x01b40358014501a0 0x3f8037003c703f0c 0xe3f8037003c703f0

def z527 : W := mkw 0x42003ef7c080215c 0x442003ef7c080215 0x40003fffc00023f4 0x140003fffc00023f

def z528 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xc19b0f3b03ff00c3 0x1c19b0f3b03ff00c

def z529 : W := mkw 0x008b0008012b0480 0x0008b0008012b048 0xe19b203803ff3ccf 0x6e19b203803ff3cc

def z530 : W := mkw 0x0021404063084114 0x4002140406308411 0x1067d0c4e388c33b 0xa1067d0c4e388c33

def z531 : W := mkw 0x208a0b1b00912cc8 0x8208a0b1b00912cc 0xc19b2f3b00003cc7 0x7c19b2f3b00003cc

def z532 : W := mkw 0x008b0212012a0000 0x0008b0212012a000 0xe19b2f3b03ff000f 0x7e19b2f3b03ff000

def z533 : W := mkw 0x4fdeb6be80010480 0x04fdeb6be8001048 0xefffffffc00f3ccf 0xfefffffffc00f3cc

def z534 : W := mkw 0x89ca800010620000 0x089ca80001062000 0x0180000000700000 0x0018000000070000

def z535 : W := mkw 0x0b40348004001200 0x00b4034800400120 0x3fe03fc03c003f0d 0xf3fe03fc03c003f0

def z536 : W := mkw 0x0200348000000000 0x0020034800000000 0x00003fc000000004 0x100003fc00000000

def z537 : W := mkw 0x849fc000092ec000 0x0849fc000092ec00 0xbe1fc0003c0fc00a 0xebe1fc0003c0fc00

def z538 : W := mkw 0x6fdfbfb781ba2848 0x86fdfbfb781ba284 0xcfffffffc3f00007 0xfcfffffffc3f0000

def z539 : W := mkw 0x002148416388615c 0x4002148416388615 0x1067d8c7e380c331 0x91067d8c7e380c33

def z540 : W := mkw 0x896140003b6ec000 0x0896140003b6ec00 0x3fe000003fffc009 0xe3fe000003fffc00

def z541 : W := mkw 0x0000004040000114 0x4000000404000011 0x000010c4c0000330 0x0000010c4c000033

def z542 : W := mkw 0x102009483ed5bfaf 0x0102009483ed5bfa 0x300000003ffffff8 0x0300000003ffffff

def z543 : W := mkw 0x069e323600000000 0x0069e32360000000 0xcf9f3f3f00000007 0xfcf9f3f3f0000000

def z544 : W := mkw 0x0000080000802008 0x0000008000080200 0x000008000380200d 0x3000008000380200

def z545 : W := mkw 0x228b3b1b05bb3ec8 0x8228b3b1b05bb3ec 0xff9b3f3b3fff3fcf 0xfff9b3f3b3fff3fc

def z546 : W := mkw 0x4fdfb6b6812a0000 0x04fdfb6b6812a000 0xefffffffc3ff000f 0xfefffffffc3ff000

def z547 : W := mkw 0x802140003b6ec000 0x0802140003b6ec00 0x3067c0003fffc00b 0xa3067c0003fffc00

def z548 : W := mkw 0x62003fbf80912cc8 0x862003fbf80912cc 0x40003fffc0003cc4 0x140003fffc0003cc

def z549 : W := mkw 0x0001090101982848 0x0000109010198284 0x61832f0303f83ccf 0x761832f0303f83cc

def z550 : W := mkw 0x9ffffdec3fffffaf 0x09ffffdec3fffffa 0xfffffffc3fffffff 0xffffffffc3ffffff

def z551 : W := mkw 0x008b0000012a0000 0x0008b0000012a000 0x801b0000000f0002 0x0801b0000000f000

def z552 : W := mkw 0x0fdeb02400000000 0x00fdeb0240000000 0xcffff03c00000007 0xecffff03c0000000

def z553 : W := mkw 0x0200300004001200 0x0020030000400120 0x7e0430043c08fffe 0xe7e0430043c08fff

def z554 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x1fe01fc03ff00301 0x91fe01fc03ff0030

def z555 : W := mkw 0x12203dc026903b0e 0x012203dc026903b0 0x10603fc023803f0d 0xb10603fc023803f0

def z556 : W := mkw 0x7fffbfffb7fb3fce 0x87fffbfffb7fb3fc 0xffffffffffff3fcf 0xfffffffffffff3fc

def z557 : W := mkw 0x196004c032400106 0x0196004c03240010 0x006000c000000000 0x0006000c00000000

def z558 : W := mkw 0xaffffb3f3ffffee9 0x8affffb3f3ffffee 0xffffff3f3fffffff 0xfffffff3f3ffffff

def z559 : W := mkw 0x061430240c049221 0x0061430240c04922 0xbe1c10043c0fc33a 0xebe1c10043c0fc33

def z560 : W := mkw 0x8635702c3f6fd6a1 0x08635702c3f6fd6a 0xfe1c303c3ffffffe 0xefe1c303c3ffffff

def z561 : W := mkw 0x0fdeb48000000000 0x00fdeb4800000000 0x8fffffc000000007 0xf8fffffc00000000

def z562 : W := mkw 0xa02149093bffecc8 0x8a02149093bffecc 0x300000003ffffcc8 0x0300000003ffffcc

def z563 : W := mkw 0x0200302c040116a1 0x00200302c040116a 0x0000203800001c00 0x00000203800001c0

def z564 : W := mkw 0x5fdeb7b694501a02 0x05fdeb7b694501a0 0xefffffffdc701c07 0xfefffffffdc701c0

def z565 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0x9e7fc0003c0fc002 0x89e7fc0003c0fc00

def z566 : W := mkw 0x1020094036d03b0e 0x01020094036d03b0 0x31802f003ff03f0d 0x731802f003ff03f0

def z567 : W := mkw 0x0020400022004000 0x0002040002200400 0x1064c0002000c000 0x81064c0002000c00

def z568 : W := mkw 0x0435486d6b8de5fd 0x40435486d6b8de5f 0xd07fd8ffe38fe3ff 0xbd07fd8ffe38fe3f

def z569 : W := mkw 0x8dfec0003a44c000 0x08dfec0003a44c00 0x9fffc0003c00c003 0xe9fffc0003c00c00

def z570 : W := mkw 0x208b0b1301ba2848 0x8208b0b1301ba284 0x21832f0303f03c0d 0x721832f0303f03c0

def z571 : W := mkw 0x0f74302c3e4596a1 0x00f74302c3e4596a 0xfffc303c3fffffff 0xefffc303c3ffffff

def z572 : W := mkw 0x0b403d8000902808 0x00b403d800090280 0x2fe03fc003f03c0d 0xf2fe03fc003f03c0

def z573 : W := mkw 0xcffef6b6ba44c000 0x0cffef6b6ba44c00 0xdffffffffc00c007 0xfdffffffffc00c00

def z574 : W := mkw 0x002148416388615c 0x4002148416388615 0x1067c0002388e3fb 0xa1067c0002388e3f

def z575 : W := mkw 0x8d74c0003a44c000 0x08d74c0003a44c00 0xbe7cc0003c0fc00a 0xebe7cc0003c0fc00

def z576 : W := mkw 0x849fc000092ec000 0x0849fc000092ec00 0xa19fc00003ffc00b 0x6a19fc00003ffc00

def z577 : W := mkw 0x2000021b000104c0 0x82000021b000104c 0x4000003b000000c0 0x04000003b000000c

def z578 : W := mkw 0x049e800000000000 0x0049e80000000000 0x801fc00000000002 0x0801fc0000000000

def z579 : W := mkw 0x469eb23e8c0596a1 0x0469eb23e8c0596a 0xfe1ff03ffc0ffffe 0xefe1ff03ffc0ffff

def z580 : W := mkw 0x4000023680000000 0x0400002368000000 0x4000003fc0000000 0x04000003fc000000

def z581 : W := mkw 0x0614386d4c85b7fd 0x40614386d4c85b7f 0xfe1c38fffc0ffffe 0xffe1c38fffc0ffff

def z582 : W := mkw 0x8ffff0243f6ed221 0x08ffff0243f6ed22 0xbfffd0043fffc33b 0xebfffd0043fffc33

def z583 : W := mkw 0x4fdebef7c080215c 0x44fdebef7c080215 0xcfffffffc00023f7 0xfcfffffffc00023f

def z584 : W := mkw 0x469eb23680000000 0x0469eb2368000000 0xce1ff03fc0000006 0xece1ff03fc000000

def z585 : W := mkw 0x20010b1b01bb2cc8 0x820010b1b01bb2cc 0x60002f3b03ff3ccc 0x160002f3b03ff3cc

def z586 : W := mkw 0x000008414080215c 0x4000008414080215 0x00000000000023f0 0x000000000000023f

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000200000003c0c 0x62000200000003c0

def z588 : W := mkw 0x20000b1300902848 0x820000b130090284 0x00000f0300000000 0x100000f030000000

def z589 : W := mkw 0x008a021a00010480 0x0008a021a0001048 0xe19b2f3b000f3ccf 0x7e19b2f3b000f3cc

def z590 : W := mkw 0x4dde869280000000 0x04dde86928000000 0x8fffcfc3c0000003 0xf8fffcfc3c000000

def z591 : W := mkw 0x1b40358014501a02 0x01b40358014501a0 0x2fe03fc01c701c05 0xf2fe03fc01c701c0

def z592 : W := mkw 0x0b603cc02280210c 0x00b603cc02280210 0x1fe03fc02380230d 0xf1fe03fc02380230

def z593 : W := mkw 0x0000090000902808 0x0000009000090280 0x00002f0000003c04 0x100002f0000003c0

def z594 : W := mkw 0x0f5434ac0c0596a1 0x00f5434ac0c0596a 0xfffc3ffc3c0fffff 0xffffc3ffc3c0ffff

def z595 : W := mkw 0x002148416388615c 0x4002148416388615 0x0000000003800000 0x0000000000380000

def z596 : W := mkw 0x0000000000000000 0x0000000000000000 0x0064d0c4c0000000 0x80064d0c4c000000

def z597 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0x1fe7c0003ff0c001 0x81fe7c0003ff0c00

def z598 : W := mkw 0x9ffff5803f7eda02 0x09ffff5803f7eda0 0xbfffe7003fffdc0b 0xebfffe7003fffdc0

def z599 : W := mkw 0x0200300000000000 0x0020030000000000 0x0e00300000000004 0xe0e0030000000000

def z600 : W := mkw 0x1f743de436d03b0e 0x01f743de436d03b0 0xfffc3ffc3ff03f0f 0xffffc3ffc3ff03f0

def z601 : W := mkw 0x802040003a44c000 0x0802040003a44c00 0x100000003c00c000 0x0100000003c00c00

def z602 : W := mkw 0x1f757ded7fddffff 0x41f757ded7fddfff 0xffffffffffffffff 0xffffffffffffffff

def z603 : W := mkw 0x8d74c0003a44c000 0x08d74c0003a44c00 0x3fe4c0003ff0c009 0xe3fe4c0003ff0c00

def z604 : W := mkw 0x0414002c0c0596a1 0x00414002c0c0596a 0xf01c003c3c0ffffa 0x0f01c003c3c0ffff

def z605 : W := mkw 0x20000b1b00912cc8 0x820000b1b00912cc 0x61802f3b03f03ccd 0x761802f3b03f03cc

def z606 : W := mkw 0x0dde821200000000 0x00dde82120000000 0xcfffef3b00000007 0xfcfffef3b0000000

def z607 : W := mkw 0x228b3b3f05bb3ee9 0x8228b3b3f05bb3ee 0xe19b3f3f03ff3fff 0x7e19b3f3f03ff3ff

def z608 : W := mkw 0x1b6034c036401306 0x01b6034c03640130 0x3fe010c03ff00309 0xe3fe010c03ff0030

def z609 : W := mkw 0x802148417beee15c 0x4802148417beee15 0x7067d8c7ffffe3ff 0xb7067d8c7ffffe3f

def z610 : W := mkw 0x0dffc00023084000 0x00dffc0002308400 0x9fffc0002388c00b 0xe9fffc0002388c00

def z611 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0x81ffc00003ffc003 0x081ffc00003ffc00

def z612 : W := mkw 0x5ffebffebed5bfaf 0x05ffebffebed5bfa 0xffffffffffffffff 0xffffffffffffffff

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x01802f0000000005 0x701802f000000000

def z614 : W := mkw 0x89ebc000336a4000 0x089ebc000336a400 0x11e7c00023f8c00b 0xa11e7c00023f8c00

def z615 : W := mkw 0x022178416788735c 0x4022178416788735 0x7e67f8c7ff88ffff 0xf7e67f8c7ff88fff

def z616 : W := mkw 0x002148416388615c 0x4002148416388615 0x4067c8c7c388c0f3 0x14067c8c7c388c0f

def z617 : W := mkw 0x1b6034c036401306 0x01b6034c03640130 0x1fe03fc03c000305 0xf1fe03fc03c00030

def z618 : W := mkw 0x12003dc004903b0e 0x012003dc004903b0 0x21803fc003f03f0d 0x721803fc003f03f0

def z619 : W := mkw 0x0020404062004114 0x4002040406200411 0x0060c0c0c0000000 0x00060c0c0c000000

def z620 : W := mkw 0x0635702c2f0dd6a1 0x00635702c2f0dd6a 0xfe7ff03c3f8fffff 0xefe7ff03c3f8ffff

def z621 : W := mkw 0x0614302400000000 0x0061430240000000 0x0e04100400000000 0x80e0410040000000

def z622 : W := mkw 0x002048406280611c 0x4002048406280611 0x1064d8c4e380e33d 0xb1064d8c4e380e33

def z623 : W := mkw 0xefffffbfbbffecc8 0x8efffffbfbbffecc 0xfffffffffffffccf 0xffffffffffffffcc

def z624 : W := mkw 0x0001000101080040 0x0000100010108004 0x40030003000800c2 0x040030003000800c

def z625 : W := mkw 0x0414002400000000 0x0041400240000000 0xc01c003c00000002 0x0c01c003c0000000

def z626 : W := mkw 0x0001080101882048 0x0000108010188204 0x500718072388e3ff 0xb500718072388e3f

def z627 : W := mkw 0x4f74f4e4e2004114 0x44f74f4e4e200411 0x1e64d0c4e000c330 0x81e64d0c4e000c33

def z628 : W := mkw 0x420036b680000000 0x0420036b68000000 0x0000273800000000 0x0000027380000000

def z629 : W := mkw 0x39eb0fdb33fb2dce 0x839eb0fdb33fb2dc 0xe1fb2ffb03ff3ccf 0x7e1fb2ffb03ff3cc

def z630 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0x41832f3b03f03cc5 0x141832f3b03f03cc

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x100010002000230c 0xa100010002000230

def z632 : W := mkw 0x6fffffffe3bb6ddc 0xc6fffffffe3bb6dd 0xffffffffe3ffffff 0xfffffffffe3fffff

def z633 : W := mkw 0x6fdfbfbf81bb2cc8 0x86fdfbfbf81bb2cc 0xef9b2f3b03ff3ccf 0x7ef9b2f3b03ff3cc

def z634 : W := mkw 0x3bcb3f9b15fb3eca 0x83bcb3f9b15fb3ec 0xef9b2f3b1fff3ccf 0x7ef9b2f3b1fff3cc

def z635 : W := mkw 0x00ab4a536388615c 0x400ab4a536388615 0xd1ffffffe388e3ff 0xfd1ffffffe388e3f

def z636 : W := mkw 0x89ebc000336a4000 0x089ebc000336a400 0x3fe3c0003ff00009 0xe3fe3c0003ff0000

def z637 : W := mkw 0x269f3b3f01bb2cc8 0x8269f3b3f01bb2cc 0xef9f3f3f03ff3ccf 0xfef9f3f3f03ff3cc

def z638 : W := mkw 0x8ffff0243b6ec000 0x08ffff0243b6ec00 0xfffff03c3fffc00f 0xefffff03c3fffc00

def z639 : W := mkw 0x0614302404001200 0x0061430240400120 0xfe1c303c3c003f0e 0xefe1c303c3c003f0

def z640 : W := mkw 0x008a000000000000 0x0008a00000000000 0x819b000000000003 0x6819b00000000000

def z641 : W := mkw 0x8ffff4803b6ec000 0x08ffff4803b6ec00 0xbfffffc03fffc00f 0xfbfffffc03fffc00

def z642 : W := mkw 0xcffff4a4bb6ec000 0x0cffff4a4bb6ec00 0xbfffd0c4ffffc00b 0xebfffd0c4ffffc00

def z643 : W := mkw 0x849e800008268000 0x0849e80000826800 0x8018000000070000 0x0801800000007000

def z644 : W := mkw 0x0414000008048000 0x0041400000804800 0xfe1c10043c0fe3fe 0xefe1c10043c0fe3f

def z645 : W := mkw 0x002148416388615c 0x4002148416388615 0x500308032388e3ff 0x3500308032388e3f

def z646 : W := mkw 0x89ebc000336a4000 0x089ebc000336a400 0xa1fbc00003ff000b 0x6a1fbc00003ff000

def z647 : W := mkw 0xa9ebcb1b33fb6cc8 0x8a9ebcb1b33fb6cc 0xe1fbef3b03ff3ccf 0x7e1fbef3b03ff3cc

def z648 : W := mkw 0x449e823680000000 0x0449e82368000000 0xc07fd8ffc0000007 0xbc07fd8ffc000000

def z649 : W := mkw 0x0021400023084000 0x0002140002308400 0x5067d8c7e388c00f 0xb5067d8c7e388c00

def z650 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0x21830f0303ff3cc9 0x121830f0303ff3cc

def z651 : W := mkw 0x002148416388615c 0x4002148416388615 0x4063d8c7c38023f5 0x14063d8c7c38023f

def z652 : W := mkw 0x269f323f0d2f96e1 0x8269f323f0d2f96e 0xfe1f303f3c0ffffe 0xefe1f303f3c0ffff

def z653 : W := mkw 0x3bea3fda36f33f8e 0x83bea3fda36f33f8 0xbff83ff83ff73f0d 0xfbff83ff83ff73f0

def z654 : W := mkw 0x1b603dc836d13f8e 0x01b603dc836d13f8 0xfff83ff83fff3fcf 0xffff83ff83fff3fc

def z655 : W := mkw 0x0414000008048000 0x0041400000804800 0x1e0400003c00c000 0x81e0400003c00c00

def z656 : W := mkw 0x4ffeb6b6b2400000 0x04ffeb6b6b240000 0xfffffffffff0000f 0xffffffffffff0000

def z657 : W := mkw 0x849fc02c092fc4a1 0x0849fc02c092fc4a 0xc01fc03c000fc0f2 0x0c01fc03c000fc0f

def z658 : W := mkw 0xc9ebc692b36a4000 0x0c9ebc692b36a400 0x01e3cfc3c3f00001 0x101e3cfc3c3f0000

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x400018c7c0000004 0x1400018c7c000000

def z660 : W := mkw 0x3beb3fd337fa3b4e 0x83beb3fd337fa3b4 0x3fe33fc33ff03f0d 0xf3fe33fc33ff03f0

def z661 : W := mkw 0x000000080c0596a1 0x0000000080c0596a 0xf01820383c0ffffe 0x6f01820383c0ffff

def z662 : W := mkw 0x12203dc036d03b0e 0x012203dc036d03b0 0x30003fc03ff03f0c 0x130003fc03ff03f0

def z663 : W := mkw 0x008b0a1301882048 0x0008b0a130188204 0xc19b2f3b038820cf 0x7c19b2f3b038820c

def z664 : W := mkw 0x008b090001ba2808 0x0008b090001ba280 0xa19b2f0003ff3c0f 0x7a19b2f0003ff3c0

def z665 : W := mkw 0x1f5435ac1c559ea3 0x01f5435ac1c559ea 0xff9c373c3c7ffffe 0xeff9c373c3c7ffff

def z666 : W := mkw 0x6fdfbfbf8dbfbee9 0x86fdfbfbf8dbfbee 0xffffffffffffffff 0xffffffffffffffff

def z667 : W := mkw 0x8dde800018668000 0x08dde80001866800 0xbf9c00003c7fc00a 0xebf9c00003c7fc00

def z668 : W := mkw 0x328b3fdb05bb3fce 0x8328b3fdb05bb3fc 0xe19b3ffb03ff3fcf 0x7e19b3ffb03ff3fc

def z669 : W := mkw 0x008a021200000000 0x0008a02120000000 0x01830f0300000001 0x101830f030000000

def z670 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe01b003b03ff3cca 0x0e01b003b03ff3cc

def z671 : W := mkw 0x4bcab69280000000 0x04bcab6928000000 0x0fe3ffc3c0000005 0xf0fe3ffc3c000000

def z672 : W := mkw 0x0000090000902808 0x0000009000090280 0x2000000003f03c08 0x02000000003f03c0

def z673 : W := mkw 0x9bebfdc037fa7b0e 0x09bebfdc037fa7b0 0x3fe3ffc03ff03f0d 0xf3fe3ffc03ff03f0

def z674 : W := mkw 0x022038402680330c 0x0022038402680330 0x3e6038c03f803f0d 0xf3e6038c03f803f0

def z675 : W := mkw 0x49ebced3e388615c 0x449ebced3e388615 0x51e7dfc7e388e3ff 0xb51e7dfc7e388e3f

def z676 : W := mkw 0x0000002c000104a1 0x00000002c000104a 0x4000003c000000f0 0x04000003c000000f

def z677 : W := mkw 0x1f7434ec3e4597a7 0x01f7434ec3e4597a 0xfe7c30fc3c0ffffe 0xefe7c30fc3c0ffff

def z678 : W := mkw 0x84bfc0003b6ec000 0x084bfc0003b6ec00 0xb01fc0003fffc00a 0x0b01fc0003fffc00

def z679 : W := mkw 0x043548416b8ce15c 0x4043548416b8ce15 0xfe7fd8c7ff8fe3ff 0xffe7fd8c7ff8fe3f

def z680 : W := mkw 0x4fdebfb680902808 0x04fdebfb68090280 0xefffffffc3f03c0f 0xfefffffffc3f03c0

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0x2180000003f00009 0x62180000003f0000

def z682 : W := mkw 0x19614dc173d8695e 0x419614dc173d8695 0x01e3cfc3c3f00001 0x101e3cfc3c3f0000

def z683 : W := mkw 0x0614302c080584a1 0x00614302c080584a 0xce1c303c000fc0f6 0xece1c303c000fc0f

def z684 : W := mkw 0x0000400040004010 0x4000040004000401 0x0004c004c000c030 0x00004c004c000c03

def z685 : W := mkw 0x0000090000902808 0x0000009000090280 0x01800f0003f00001 0x101800f0003f0000

def z686 : W := mkw 0x9dffc9403ffefb0e 0x09dffc9403ffefb0 0xbfffc0003fffff0b 0xebfffc0003fffff0

def z687 : W := mkw 0x0021480123886048 0x0002148012388604 0x5067c8032388e0cf 0xb5067c8032388e0c

def z688 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000000820ce 0x240000000000820c

def z689 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcf9fe73fc0000002 0x4cf9fe73fc000000

def z690 : W := mkw 0x0000000800010480 0x0000000080001048 0xa018203800071c00 0x4a018203800071c0

def z691 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0x8ff83ff800000005 0xf8ff83ff80000000

def z692 : W := mkw 0x6fdeb7be80330c80 0x86fdeb7be80330c8 0xefffffffc0771c07 0xfefffffffc0771c0

def z693 : W := mkw 0x1b613dc137d83b4e 0x01b613dc137d83b4 0x7fe33fc33ff83fcf 0xf7fe33fc33ff83fc

def z694 : W := mkw 0x1220394036d03b0e 0x01220394036d03b0 0x3e0030003ff03f0c 0xe3e0030003ff03f0

def z695 : W := mkw 0x0ddf8000012a0000 0x00ddf8000012a000 0xafffc00003ff000b 0xeafffc00003ff000

def z696 : W := mkw 0x420034a480000000 0x0420034a48000000 0x000010c4c0000000 0x0000010c4c000000

def z697 : W := mkw 0x3021094937fb3fce 0x83021094937fb3fc 0x300000003fff3fc8 0x0300000003fff3fc

def z698 : W := mkw 0x0000080100802048 0x0000008010080204 0x40000803000020c4 0x140000803000020c

def z699 : W := mkw 0x002108412388214c 0x0002108412388214 0x506318c3238823cf 0xb506318c3238823c

def z700 : W := mkw 0x84bfc0002b2ec000 0x084bfc0002b2ec00 0x907fc000238fc00b 0xa907fc000238fc00

def z701 : W := mkw 0x061430240c049221 0x0061430240c04922 0x5e0410043c08e3fe 0xa5e0410043c08e3f

def z702 : W := mkw 0x0000000000000000 0x0000000000000000 0x0067c00000000003 0xa0067c0000000000

def z703 : W := mkw 0x208a0b1b00b32cc8 0x8208a0b1b00b32cc 0xe1982f3b00773cc4 0x5e1982f3b00773cc

def z704 : W := mkw 0x208b0b1b0dbfbee9 0x8208b0b1b0dbfbee 0xf19b2f3b3fffffff 0x7f19b2f3b3ffffff

def z705 : W := mkw 0x0200302c040116a1 0x00200302c040116a 0xe018303c000f3ffe 0x6e018303c000f3ff

def z706 : W := mkw 0xa0ab4b1b3bffecc8 0x8a0ab4b1b3bffecc 0xf19b2f3b3ffffccf 0x7f19b2f3b3ffffcc

def z707 : W := mkw 0x0021484173c8615c 0x40021484173c8615 0x7067d8c7fff8e3ff 0xb7067d8c7fff8e3f

def z708 : W := mkw 0x54be8b76b6d03b0e 0x054be8b76b6d03b0 0xf01fc03ffff03f0a 0x0f01fc03ffff03f0

def z709 : W := mkw 0xcf74f4a4be44d221 0x0cf74f4a4be44d22 0x1e64d0c4fc00c330 0x81e64d0c4fc00c33

def z710 : W := mkw 0x5b603de4b6d03b0e 0x05b603de4b6d03b0 0x3fe03fc4fff03f0d 0xf3fe03fc4fff03f0

def z711 : W := mkw 0x0020404062004114 0x4002040406200411 0x5067d8c7e008e3ff 0xb5067d8c7e008e3f

def z712 : W := mkw 0x4fdeb6b68c049221 0x04fdeb6b68c04922 0xdffffffffc08e3ff 0xfdffffffffc08e3f

def z713 : W := mkw 0xa49f821b092f84c0 0x8a49f821b092f84c 0xc01b003b000f00c2 0x0c01b003b000f00c

def z714 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xbe1c303c3c0ffff8 0xcbe1c303c3c0ffff

def z715 : W := mkw 0x002149416398695c 0x4002149416398695 0x5067ffc7e388ffff 0xb5067ffc7e388fff

def z716 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe027003ff03f09 0xe3fe027003ff03f0

def z717 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbfffe0003ffffc0f 0xebfffe0003ffffc0

def z718 : W := mkw 0x32003fda04913f8e 0x832003fda04913f8 0x00003ff800003f04 0x100003ff800003f0

def z719 : W := mkw 0x0001080101882048 0x0000108010188204 0x5067d8c7e388e3ff 0xb5067d8c7e388e3f

def z720 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xce7fffffc0000006 0x9ce7fffffc000000

def z721 : W := mkw 0x969ffdc00dbefb0e 0x0969ffdc00dbefb0 0x801fffc0000fff06 0x1801fffc0000fff0

def z722 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xffffd0043fffc00f 0xeffffd0043fffc00

def z723 : W := mkw 0x0021404163084154 0x4002140416308415 0x5067d0c7e388c3fb 0xa5067d0c7e388c3f

def z724 : W := mkw 0x4dde86b680000000 0x04dde86b68000000 0xcfffcfffc0000003 0xfcfffcfffc000000

def z725 : W := mkw 0xcdffc692bb6ec000 0x0cdffc692bb6ec00 0xffffeffbffffc00f 0xfffffeffbffffc00

def z726 : W := mkw 0x8dde884158e6a15c 0x48dde884158e6a15 0xef9818c7dc7723f4 0x5ef9818c7dc7723f

def z727 : W := mkw 0x8d7540003b6ec000 0x08d7540003b6ec00 0xbffc00003fffc00b 0xebffc00003fffc00

def z728 : W := mkw 0xc22176b6bb6ec000 0x0c22176b6bb6ec00 0x70003fffffffc00c 0x170003fffffffc00

def z729 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe43fc43ff0ff3d 0xf3fe43fc43ff0ff3

def z730 : W := mkw 0x0ddf8000092e8000 0x00ddf8000092e800 0xbfffc0003fffc00b 0xebfffc0003fffc00

def z731 : W := mkw 0xad74cb1b3ad5ecc8 0x8ad74cb1b3ad5ecc 0x5e64ef3b3c00fcc4 0x95e64ef3b3c00fcc

def z732 : W := mkw 0x0635786d6f8df7fd 0x40635786d6f8df7f 0xae7be8fbdf871c01 0x5ae7be8fbdf871c0

def z733 : W := mkw 0x202149496fbffffd 0xc202149496fbffff 0x300000003ffffff8 0x0300000003ffffff

def z734 : W := mkw 0xdf74f4e4be44d306 0x0df74f4e4be44d30 0x1e64d0c4fc00c300 0x81e64d0c4fc00c30

def z735 : W := mkw 0x4fdeb6b684001200 0x04fdeb6b68400120 0xcfffffffc0003f07 0xfcfffffffc0003f0

def z736 : W := mkw 0x802140003b6ec000 0x0802140003b6ec00 0x3e0000003fffc008 0xe3e0000003fffc00

def z737 : W := mkw 0x608b8b1b81bb2cc8 0x8608b8b1b81bb2cc 0xe19bef3bc3ff3ccf 0x7e19bef3bc3ff3cc

def z738 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xffffc0043fffc0fb 0xeffffc0043fffc0f

def z739 : W := mkw 0x461436b680000000 0x0461436b68000000 0xce7fffffc0000007 0xfce7fffffc000000

def z740 : W := mkw 0x4fdeb6b684001200 0x04fdeb6b68400120 0xefffffffdc001c07 0xfefffffffdc001c0

def z741 : W := mkw 0x0414002c0c0596a1 0x00414002c0c0596a 0xfe1c003c3c0ffffa 0xefe1c003c3c0ffff

def z742 : W := mkw 0x1b41758155585a52 0x41b41758155585a5 0x6f87e707dc78dcf2 0x46f87e707dc78dcf

def z743 : W := mkw 0x1b603dc176d03b5e 0x41b603dc176d03b5 0x3fe03fc03ff03ffd 0xf3fe03fc03ff03ff

def z744 : W := mkw 0x52003ffe84913faf 0x052003ffe84913fa 0x40003fffc0003ff4 0x140003fffc0003ff

def z745 : W := mkw 0x4ffffef7e388615c 0x44ffffef7e388615 0x9f9827382388e3f8 0x49f9827382388e3f

def z746 : W := mkw 0x0414000008048000 0x0041400000804800 0xbf9c00003fffc00b 0xebf9c00003fffc00

def z747 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xa19b2f3b03ff1c0b 0x7a19b2f3b03ff1c0

def z748 : W := mkw 0x0414000808058480 0x0041400080805848 0xfe1c303c3c0ffffe 0xefe1c303c3c0ffff

def z749 : W := mkw 0x269f3b370dbeba69 0x8269f3b370dbeba6 0x1f871f073ff0c331 0x91f871f073ff0c33

def z750 : W := mkw 0x002148416388615c 0x4002148416388615 0x7067f8c7e388ffff 0xf7067f8c7e388fff

def z751 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe1ff03ffc0ffffe 0xefe1ff03ffc0ffff

def z752 : W := mkw 0x09cb0000116a0000 0x009cb0000116a000 0xaf9b00001fff000b 0x6af9b00001fff000

def z753 : W := mkw 0x49ca869280000000 0x049ca86928000000 0x81fbeffbc0000001 0x581fbeffbc000000

def z754 : W := mkw 0x4fdeb6b680220000 0x04fdeb6b68022000 0xefffffffc0770007 0xfefffffffc077000

def z755 : W := mkw 0x002048416280615c 0x4002048416280615 0x5067d8c7e000e3f7 0xb5067d8c7e000e3f

def z756 : W := mkw 0x8dffc0407b6ec114 0x48dffc0407b6ec11 0xbfffc0c0ffffc00b 0xebfffc0c0ffffc00

def z757 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe3ffc3fff03f0d 0xf3fe3ffc3fff03f0

def z758 : W := mkw 0x1b607dc036d07b0e 0x01b607dc036d07b0 0x3fe4ffc03ff0ff0d 0xf3fe4ffc03ff0ff0

def z759 : W := mkw 0x843540003b6ec000 0x0843540003b6ec00 0x3e0400003fffc008 0x83e0400003fffc00

def z760 : W := mkw 0x002148416388615c 0x4002148416388615 0x5067d8c7e380e3f5 0x95067d8c7e380e3f

def z761 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbff800003fffc009 0xebff800003fffc00

def z762 : W := mkw 0x208b0b1b41bb2cd8 0xc208b0b1b41bb2cd 0xe19b2f3fc3ff3cff 0x7e19b2f3fc3ff3cf

def z763 : W := mkw 0x002148416388615c 0x4002148416388615 0x5067d8c7e388c3f3 0x95067d8c7e388c3f

def z764 : W := mkw 0x32003f9b04913eca 0x832003f9b04913ec 0x40002f3b00003cc4 0x140002f3b00003cc

def z765 : W := mkw 0x20aa435a62334d94 0xc20aa435a62334d9 0xb1fcf7fce077df30 0xcb1fcf7fce077df3

def z766 : W := mkw 0xcfdeb6b688268000 0x0cfdeb6b68826800 0xcfffffffc0070007 0xfcfffffffc007000

def z767 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xa19b273803ff3ccb 0x6a19b273803ff3cc

def z768 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z769 : W := mkw 0x208a0b1a00b32c88 0x8208a0b1a00b32c8 0xa198273803f73c08 0x4a198273803f73c0

def z770 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbffbc0003fffc009 0x4bffbc0003fffc00

def z771 : W := mkw 0x1f7474e47e44d337 0x41f7474e47e44d33 0x1e64d0c4fc00c330 0x81e64d0c4fc00c33

def z772 : W := mkw 0x4dde86b680000000 0x04dde86b68000000 0xc1ffdfffc0000007 0xbc1ffdfffc000000

def z773 : W := mkw 0x22003b3f04913ee9 0x822003b3f04913ee 0x40002f3b00003cc4 0x140002f3b00003cc

def z774 : W := mkw 0x8bebf02c376b56a1 0x08bebf02c376b56a 0x41e3f03c03f03ff5 0x041e3f03c03f03ff

def z775 : W := mkw 0x0960000032400000 0x0096000003240000 0xbff800003fff000b 0xebff800003fff000

def z776 : W := mkw 0x0000090000902808 0x0000009000090280 0x3f802f003ff03c0d 0xf3f802f003ff03c0

def z777 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbf9fc0003fffc00a 0x4bf9fc0003fffc00

def z778 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe01fc03ff03f09 0x93fe01fc03ff03f0

def z779 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0xbff83fc03fff3f0f 0xfbff83fc03fff3f0

def z780 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x7fe03fc43ff03ffd 0xf7fe03fc43ff03ff

def z781 : W := mkw 0x208b4b1b01bb6cc8 0x8208b4b1b01bb6cc 0xe19fef3b03fffccf 0x7e19fef3b03fffcc

def z782 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xa19b2f3b03f73c0d 0x7a19b2f3b03f73c0

def z783 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcfffffffc00023f7 0xfcfffffffc00023f

def z784 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0x4fe7ffffc0000005 0x94fe7ffffc000000

def z785 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xdfffffffe000c337 0xfdfffffffe000c33

def z786 : W := mkw 0x8dffc0013b6ec040 0x08dffc0013b6ec04 0xffffc0033fffc0cb 0xeffffc0033fffc0c

def z787 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xa198273803f71c00 0x4a198273803f71c0

def z788 : W := mkw 0x9dffc4c03b6ec106 0x09dffc4c03b6ec10 0xbfffc0c03fffc00b 0xebfffc0c03fffc00

def z789 : W := mkw 0x1f7434e43e449327 0x01f7434e43e44932 0x1e6010c03c000300 0x81e6010c03c00030

def z790 : W := mkw 0x8dff80003b6e8000 0x08dff80003b6e800 0xbffb00003fff000b 0xebffb00003fff000

def z791 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe1f383f3c0fffff 0xffe1f383f3c0ffff

def z792 : W := mkw 0x4f54b6b680000000 0x04f54b6b68000000 0x4e67ffffc0000007 0xb4e67ffffc000000

def z793 : W := mkw 0x0021484163aa615c 0x40021484163aa615 0x7067d8c7e3ffe3ff 0xb7067d8c7e3ffe3f

def z794 : W := mkw 0x0200300804011680 0x0020030080401168 0xfe1c303c3c0ffffe 0xefe1c303c3c0ffff

def z795 : W := mkw 0x008a0b1a00912c88 0x0008a0b1a00912c8 0xe19b2f3b03ff3ccf 0x7e19b2f3b03ff3cc

def z796 : W := mkw 0x1b603dc076d03b1e 0x41b603dc076d03b1 0x3fe03fc4fff03f3d 0xf3fe03fc4fff03f3

def z797 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0x9fffc0003fffc003 0x89fffc0003fffc00

def z798 : W := mkw 0x20000b1b00912cc8 0x820000b1b00912cc 0xe1982f3b03ff3ccf 0x7e1982f3b03ff3cc

def z799 : W := mkw 0x208b031b013b0cc0 0x8208b031b013b0cc 0xe19b273b03ff1ccb 0x6e19b273b03ff1cc

def z800 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xdfffffffe000230f 0xfdfffffffe000230

def z801 : W := mkw 0x49ca869a8c0596a1 0x049ca869a8c0596a 0x31e3cfc3fc0ffff9 0x131e3cfc3fc0ffff

def z802 : W := mkw 0x0b60348036401200 0x00b6034803640120 0x3fe03fc03ff03f0d 0xf3fe03fc03ff03f0

def z803 : W := mkw 0x208b4b1b41bb6cd8 0xc208b4b1b41bb6cd 0xe1ffffffc3fffcff 0xfe1ffffffc3fffcf

def z804 : W := mkw 0x4fdeb6b68c049221 0x04fdeb6b68c04922 0xcfffffffdc000007 0xfcfffffffdc00000

def z805 : W := mkw 0x12003dc804913f8e 0x012003dc804913f8 0x40003ff800003fc4 0x140003ff800003fc

def z806 : W := mkw 0x4dde869280000000 0x04dde86928000000 0xcfffeffbc0000007 0xfcfffeffbc000000

def z807 : W := mkw 0x1b603dc176d03b5e 0x41b603dc176d03b5 0x7fe43fc7fff8ffff 0xf7fe43fc7fff8fff

def z808 : W := mkw 0x1d740dec3ad5adaf 0x01d740dec3ad5ada 0xc1fc0ffc03ffc0f3 0x1c1fc0ffc03ffc0f

def z809 : W := mkw 0x2021494963bb6ddc 0xc2021494963bb6dd 0x2000000003ff3cc8 0x02000000003ff3cc

def z810 : W := mkw 0xa49fc23f092fc4e1 0x8a49fc23f092fc4e 0xc01fc03f000fc0f2 0x0c01fc03f000fc0f

def z811 : W := mkw 0x208b0b5b41bb2ddc 0xc208b0b5b41bb2dd 0xe1ffffffc3ff3fff 0xfe1ffffffc3ff3ff

def z812 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcfffffffc00820cf 0xfcfffffffc00820c

def z813 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xfffffffffc00000f 0xffffffffffc00000

def z814 : W := mkw 0x8dffc0017b6ec050 0x48dffc0017b6ec05 0xffffd8c7ffffc0ff 0xfffffd8c7ffffc0f

def z815 : W := mkw 0x002148416388615c 0x4002148416388615 0xf07fd8c7e38fe3ff 0xff07fd8c7e38fe3f

def z816 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcffbeffbc0000007 0x7cffbeffbc000000

def z817 : W := mkw 0x649f823f892f84e1 0x8649f823f892f84e 0xc01fc03fc00fc0f2 0x0c01fc03fc00fc0f

def z818 : W := mkw 0x8dde800018668000 0x08dde80001866800 0xaf9800001ff70009 0x6af9800001ff7000

def z819 : W := mkw 0x896140003b6ec000 0x0896140003b6ec00 0x3e6000003fffc008 0x83e6000003fffc00

def z820 : W := mkw 0x061434ac0c0596a1 0x0061434ac0c0596a 0xfe1c3ffc3c0ffffe 0xffe1c3ffc3c0ffff

def z821 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe1fb3ffb03ff3ccf 0xfe1fb3ffb03ff3cc

def z822 : W := mkw 0x002148416388615c 0x4002148416388615 0x5067d8c7e008e3f6 0x95067d8c7e008e3f

def z823 : W := mkw 0x0bca369200000000 0x00bca36920000000 0xcfffffffc0000007 0xfcfffffffc000000

def z824 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe7ff03c3c0fffff 0xefe7ff03c3c0ffff

def z825 : W := mkw 0x008b021a012b0480 0x0008b021a012b048 0xe19b2f3b03ff3ccf 0x7e19b2f3b03ff3cc

def z826 : W := mkw 0x1b60358036501a02 0x01b60358036501a0 0x3f8027003ff01c08 0x43f8027003ff01c0

def z827 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcfffefffc0000003 0x5cfffefffc000000

def z828 : W := mkw 0x0220394026903b0c 0x00220394026903b0 0x3fe03fc03ff03f0d 0xf3fe03fc03ff03f0

def z829 : W := mkw 0xa9ebcb5373fa695c 0xca9ebcb5373fa695 0x01e3cfc3c3f00001 0x101e3cfc3c3f0000

def z830 : W := mkw 0x1021494173d8695e 0x41021494173d8695 0x5067d8c7e3f8e3ff 0xb5067d8c7e3f8e3f

def z831 : W := mkw 0x0b60390036d03a08 0x00b60390036d03a0 0x3fe03f003ff03f0d 0xf3fe03f003ff03f0

def z832 : W := mkw 0x0b403d8004903a08 0x00b403d8004903a0 0x3fe03fc03ff03f0d 0xf3fe03fc03ff03f0

def z833 : W := mkw 0x1b607dc076d07b1e 0x41b607dc076d07b1 0x3fe0ffc0fff03f0d 0xf3fe0ffc0fff03f0

def z834 : W := mkw 0x469eb6b680000000 0x0469eb6b68000000 0xc07fffffc0000007 0xbc07fffffc000000

def z835 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xaffbc0001fff000b 0x6affbc0001fff000

def z836 : W := mkw 0x8dffc0017b6ec050 0x48dffc0017b6ec05 0xffffd007ffffe3ff 0xeffffd007ffffe3f

def z837 : W := mkw 0x8021484173ea615c 0x48021484173ea615 0x5067d8c7e3f8e3ff 0xb5067d8c7e3f8e3f

def z838 : W := mkw 0x1b607dc076d07b1e 0x41b607dc076d07b1 0x7fe7ffc7fff0ff3f 0xf7fe7ffc7fff0ff3

def z839 : W := mkw 0x8d75c0003b6ec000 0x08d75c0003b6ec00 0x3fe4c0003fffc009 0xe3fe4c0003fffc00

def z840 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x7fe43fc43ff03f0f 0xf7fe43fc43ff03f0

def z841 : W := mkw 0x843540003b6ec000 0x0843540003b6ec00 0xbe7fc0003fffc00b 0xebe7fc0003fffc00

def z842 : W := mkw 0x8dffc2123b6ec000 0x08dffc2123b6ec00 0xffffffffffffc00f 0xfffffffffffffc00

def z843 : W := mkw 0xcdffc692bb6ec000 0x0cdffc692bb6ec00 0xffffdfc7ffffc00f 0xfffffdfc7ffffc00

def z844 : W := mkw 0x4bcab6b680000000 0x04bcab6b68000000 0x4fe3ffffc0000005 0xf4fe3ffffc000000

def z845 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x7fe33fc33ff03f0f 0xf7fe33fc33ff03f0

def z846 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbfffd0c4ffffc00b 0xebfffd0c4ffffc00

def z847 : W := mkw 0x008b0b1201ba2808 0x0008b0b1201ba280 0xe19b2f3b03ff3c0f 0x7e19b2f3b03ff3c0

def z848 : W := mkw 0x4fdeb6b688048021 0x04fdeb6b68804802 0xcfffffffc000c037 0xfcfffffffc000c03

def z849 : W := mkw 0xcfdeb6b698668000 0x0cfdeb6b69866800 0xfffffffffc7fc00f 0xffffffffffc7fc00

def z850 : W := mkw 0x5fdeb7be9c559ea3 0x05fdeb7be9c559ea 0xaf9827381c771c00 0x4af9827381c771c0

def z851 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xefffffffc00f000f 0xfefffffffc00f000

def z852 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xf19b2f3b23ffffff 0x7f19b2f3b23fffff

def z853 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe19b3f3f03ff3fff 0x7e19b3f3f03ff3ff

def z854 : W := mkw 0x8d75c0003b6ec000 0x08d75c0003b6ec00 0xbe7cc0003fffc00a 0xebe7cc0003fffc00

def z855 : W := mkw 0x208b0b5b41bb2ddc 0xc208b0b5b41bb2dd 0xe19b2ffbc3ff3ccf 0x7e19b2ffbc3ff3cc

def z856 : W := mkw 0x6f55bdad81bb2cc8 0x86f55bdad81bb2cc 0x2e64d0c4c3ff3cc8 0x82e64d0c4c3ff3cc

def z857 : W := mkw 0x208b4b1b41bb6cd8 0xc208b4b1b41bb6cd 0xe19b2f3b03fffcff 0x7e19b2f3b03fffcf

def z858 : W := mkw 0x6fdeb7be8c379ea1 0x86fdeb7be8c379ea 0xaf9827381c771c00 0x4af9827381c771c0

def z859 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xffffc8033fffc00f 0xfffffc8033fffc00

def z860 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe19f2f3f03fffcff 0x7e19f2f3f03fffcf

def z861 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbfffc8c3ffffc00b 0xfbfffc8c3ffffc00

def z862 : W := mkw 0x8dffc2123b6ec000 0x08dffc2123b6ec00 0xffffc03b3fffc00b 0xeffffc03b3fffc00

def z863 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xffffc0003fffe0cf 0xeffffc0003fffe0c

def z864 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbfffd0043fffc33b 0xebfffd0043fffc33

def z865 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe19f3f3f03ff3ccf 0xfe19f3f3f03ff3cc

def z866 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xf19f2f3b23fffccf 0xff19f2f3b23fffcc

def z867 : W := mkw 0x208b0b5b41bb2ddc 0xc208b0b5b41bb2dd 0xe19b2f3b03ff3fff 0x7e19b2f3b03ff3ff

def z868 : W := mkw 0x49ca86b680000000 0x049ca86b68000000 0x41e3cfffc0000001 0x141e3cfffc000000

def z869 : W := mkw 0x002148416388615c 0x4002148416388615 0x4067d8c7c388e3f7 0x14067d8c7c388e3f

def z870 : W := mkw 0x32003fff04913fef 0x832003fff04913fe 0x40003fff00003ff4 0x140003fff00003ff

def z871 : W := mkw 0x208a0b1a00b32c88 0x8208a0b1a00b32c8 0xa1982f3803f71c01 0x5a1982f3803f71c0

def z872 : W := mkw 0x4fdeb6b68c049221 0x04fdeb6b68c04922 0xfffffffffc0fc33f 0xffffffffffc0fc33

def z873 : W := mkw 0x208b031a013b0c80 0x8208b031a013b0c8 0xa198273803ff1c08 0x4a198273803ff1c0

def z874 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xc1ffffffc0000007 0x1c1ffffffc000000

def z875 : W := mkw 0xa49fc21b492fc4d0 0xca49fc21b492fc4d 0xc01fc03fc00fc0f2 0x0c01fc03fc00fc0f

def z876 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe4ffc4fff03f0d 0xf3fe4ffc4fff03f0

def z877 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3f803fc03ff03f0c 0x53f803fc03ff03f0

def z878 : W := mkw 0x04150000092e8000 0x004150000092e800 0xbe1c00003fffc00a 0xebe1c00003fffc00

def z879 : W := mkw 0x12003ded44913fff 0x412003ded44913ff 0x40003fffc0003ff4 0x140003fffc0003ff

def z880 : W := mkw 0x002008402280210c 0x0002008402280210 0x5067d8c7e388e3ff 0xb5067d8c7e388e3f

def z881 : W := mkw 0x8dffc0243b6ec000 0x08dffc0243b6ec00 0xffffc03c3fffc00b 0xeffffc03c3fffc00

def z882 : W := mkw 0x84bf40003b6ec000 0x084bf40003b6ec00 0xbf9f00003fffc00b 0xebf9f00003fffc00

def z883 : W := mkw 0x0b603d8032d02808 0x00b603d8032d0280 0x3fe03fc03ff03c0d 0xf3fe03fc03ff03c0

def z884 : W := mkw 0x4fdeb6b688048000 0x04fdeb6b68804800 0xcfffffffc00fc007 0xfcfffffffc00fc00

def z885 : W := mkw 0x8dffc4803b6ec000 0x08dffc4803b6ec00 0xbfffcfc03fffc00b 0xfbfffcfc03fffc00

def z886 : W := mkw 0x1200396c04913faf 0x01200396c04913fa 0x4000303c00003ff4 0x04000303c00003ff

def z887 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0x8fffeffbc0000003 0xf8fffeffbc000000

def z888 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xa1982f3803ff3ccd 0x7a1982f3803ff3cc

def z889 : W := mkw 0xa02149497bffeddc 0xca02149497bffedd 0x300000003ffffff8 0x0300000003ffffff

def z890 : W := mkw 0x09ea000032620000 0x009ea00003262000 0xbff800003ff70009 0xebff800003ff7000

def z891 : W := mkw 0x84bfc0003b6ec000 0x084bfc0003b6ec00 0xbe1fc0003fffc00a 0xebe1fc0003fffc00

def z892 : W := mkw 0x0021400023084000 0x0002140002308400 0x5067d8c7e388e3ff 0xb5067d8c7e388e3f

def z893 : W := mkw 0x002148416388615c 0x4002148416388615 0xd07ff8ffe388e3ff 0xfd07ff8ffe388e3f

def z894 : W := mkw 0x32003dc904913fce 0x832003dc904913fc 0x00003fc000003fc4 0x100003fc000003fc

def z895 : W := mkw 0x8dffc0243b6ec021 0x08dffc0243b6ec02 0xbfffc0043fffc03b 0xebfffc0043fffc03

def z896 : W := mkw 0x1b403d8014d03a0a 0x01b403d8014d03a0 0x3f803f003ff03f0d 0xf3f803f003ff03f0

def z897 : W := mkw 0x420036b680000000 0x0420036b68000000 0x4063ffffc0000005 0x14063ffffc000000

def z898 : W := mkw 0x9b60fdc036d07b0e 0x09b60fdc036d07b0 0x3fe0ffc03ff03f0d 0xf3fe0ffc03ff03f0

def z899 : W := mkw 0x1b60358036501a02 0x01b60358036501a0 0x3fe037003ff03f0d 0xe3fe037003ff03f0

def z900 : W := mkw 0x0021404163084154 0x4002140416308415 0x5067d0c7e008e3fe 0xa5067d0c7e008e3f

def z901 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbf9c00003fffc00a 0xebf9c00003fffc00

def z902 : W := mkw 0x3beb36db376b17c6 0x83beb36db376b17c 0xde7b10fb3c0f03c2 0x8de7b10fb3c0f03c

def z903 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbfffc0003fffe3fb 0xebfffc0003fffe3f

def z904 : W := mkw 0x1b603dc176d03b5e 0x41b603dc176d03b5 0x7fe7ffc7fff03fff 0xf7fe7ffc7fff03ff

def z905 : W := mkw 0x8d75c0003b6ec000 0x08d75c0003b6ec00 0x3e0000003fffc008 0x03e0000003fffc00

def z906 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0xfff83ff83ff03f0f 0xffff83ff83ff03f0

def z907 : W := mkw 0x002148416388615c 0x4002148416388615 0x71e7d8c7e3f8e3ff 0xf71e7d8c7e3f8e3f

def z908 : W := mkw 0x208a0b1a00b32c88 0x8208a0b1a00b32c8 0xe19b2f3b03f73c0f 0x7e19b2f3b03f73c0

def z909 : W := mkw 0x8ddf8000196e8000 0x08ddf8000196e800 0xafffc0001fff000b 0xeafffc0001fff000

def z910 : W := mkw 0x8dffc0407b6ec114 0x48dffc0407b6ec11 0xbfffc0003fffc33b 0xebfffc0003fffc33

def z911 : W := mkw 0xcdffc480bb6ec000 0x0cdffc480bb6ec00 0xbfffc0c0ffffc00b 0xebfffc0c0ffffc00

def z912 : W := mkw 0x0200392c04913ea9 0x00200392c04913ea 0x40003f3c00003ff4 0x140003f3c00003ff

def z913 : W := mkw 0x09eb4000336a4000 0x009eb4000336a400 0xbfffc0003fffc00b 0xebfffc0003fffc00

def z914 : W := mkw 0x1b403d8014d03a0a 0x01b403d8014d03a0 0x2f802f001ff01c01 0x52f802f001ff01c0

def z915 : W := mkw 0x49ca869280000000 0x049ca86928000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z916 : W := mkw 0xadffc2133b6ec040 0x8adffc2133b6ec04 0xbfffc0033fffc00b 0xebfffc0033fffc00

def z917 : W := mkw 0x096000003a448000 0x0096000003a44800 0x3fe000003fffc009 0xe3fe000003fffc00

def z918 : W := mkw 0x1b60358036501a02 0x01b60358036501a0 0x2fe027001ff01c01 0x42fe027001ff01c0

def z919 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe03fc03ff8fffd 0xf3fe03fc03ff8fff

def z920 : W := mkw 0x8dfec0003a66c000 0x08dfec0003a66c00 0xbffcc0003ff7c009 0xebffcc0003ff7c00

def z921 : W := mkw 0x8d75c0003b6ec000 0x08d75c0003b6ec00 0x3e67c0003fffc00b 0xa3e67c0003fffc00

def z922 : W := mkw 0x0000021200000000 0x0000002120000000 0x4067ffffc0000007 0xb4067ffffc000000

def z923 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xefffffffc0003c0f 0xfefffffffc0003c0

def z924 : W := mkw 0x0001090901992cc8 0x00001090901992cc 0xe19b2f3b03ff3ccf 0x7e19b2f3b03ff3cc

def z925 : W := mkw 0x9f74f4e43e44d327 0x09f74f4e43e44d32 0x1e64d0c43c00c330 0x81e64d0c43c00c33

def z926 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x7fe7ffc7fff8ffff 0xf7fe7ffc7fff8fff

def z927 : W := mkw 0x4bcab6b680000000 0x04bcab6b68000000 0xc1fbffffc0000007 0x7c1fbffffc000000

def z928 : W := mkw 0x89eb40003b6ec000 0x089eb40003b6ec00 0xbffb00003fffc00b 0xebffb00003fffc00

def z929 : W := mkw 0x8dfe80003a668000 0x08dfe80003a66800 0xaff800001ff70001 0x4aff800001ff7000

def z930 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe03fc03ff01f01 0xd3fe03fc03ff01f0

def z931 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xff9b2f3b3fff3ccf 0xfff9b2f3b3fff3cc

def z932 : W := mkw 0x8dffc0407b6ec114 0x48dffc0407b6ec11 0xffffd0c4ffffe3ff 0xeffffd0c4ffffe3f

def z933 : W := mkw 0x043400003a448000 0x0043400003a44800 0xbe1c00003fffc00a 0xebe1c00003fffc00

def z934 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x2fe03fc01ff01c05 0xf2fe03fc01ff01c0

def z935 : W := mkw 0x843540003b6ec000 0x0843540003b6ec00 0xbe1800003fffc008 0x4be1800003fffc00

def z936 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x2f8027001ff01c00 0x42f8027001ff01c0

def z937 : W := mkw 0x249f021b092f84c0 0x8249f021b092f84c 0xc01f003b000fc0c2 0x0c01f003b000fc0c

def z938 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe198273803ff3cce 0x6e198273803ff3cc

def z939 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3f802f003ff03f0d 0x73f802f003ff03f0

def z940 : W := mkw 0x1b603d8036d03a0a 0x01b603d8036d03a0 0x3fe02f003ff03c0d 0xf3fe02f003ff03c0

def z941 : W := mkw 0x208b0b5b01bb2dcc 0x8208b0b5b01bb2dc 0xe19b3ffb03ff3fcf 0x7e19b3ffb03ff3fc

def z942 : W := mkw 0x8dfe80003a668000 0x08dfe80003a66800 0xbfffc0003ff7000b 0xebfffc0003ff7000

def z943 : W := mkw 0x002148416388615c 0x4002148416388615 0x7e67d8c7ff88e3ff 0xf7e67d8c7ff88e3f

def z944 : W := mkw 0x002148416388615c 0x4002148416388615 0x5067d0c7e388e3fa 0x85067d0c7e388e3f

def z945 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe19b2f3b03f71c07 0x7e19b2f3b03f71c0

def z946 : W := mkw 0xcdffc236bb6ec000 0x0cdffc236bb6ec00 0xbfffc0383fffc00b 0xebfffc0383fffc00

def z947 : W := mkw 0x4fdeb6b68c049221 0x04fdeb6b68c04922 0xfffffffffc00ff3f 0xffffffffffc00ff3

def z948 : W := mkw 0x449e823680000000 0x0449e82368000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z949 : W := mkw 0x49ca869280000000 0x049ca86928000000 0x41e3effbc0000005 0x141e3effbc000000

def z950 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xa19b2f3b03ff3cc9 0x5a19b2f3b03ff3cc

def z951 : W := mkw 0x1b403d8014d03a0a 0x01b403d8014d03a0 0x2fe03fc01ff03c0d 0xf2fe03fc01ff03c0

def z952 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbfffc0003ff7c001 0xcbfffc0003ff7c00

def z953 : W := mkw 0x0f5434a400000000 0x00f5434a40000000 0xcfffffffc0000007 0xfcfffffffc000000

def z954 : W := mkw 0x5f74b4e4be449327 0x05f74b4e4be44932 0x1e64d0c4fc00c330 0x81e64d0c4fc00c33

def z955 : W := mkw 0x8dffc0007b6ec010 0x48dffc0007b6ec01 0xbfffc004ffffc03b 0xebfffc004ffffc03

def z956 : W := mkw 0x208b4b1b41bb6cd8 0xc208b4b1b41bb6cd 0xf19fff3fe3ffffff 0xff19fff3fe3fffff

def z957 : W := mkw 0x1220394036d03b0e 0x01220394036d03b0 0x3f803f003ff03f0d 0xf3f803f003ff03f0

def z958 : W := mkw 0x12003dc004903b0e 0x012003dc004903b0 0x3f803fc03ff03f0d 0xf3f803fc03ff03f0

def z959 : W := mkw 0x4fdeb6b688048000 0x04fdeb6b68804800 0xdffffffffc00c007 0xfdffffffffc00c00

def z960 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe19b3fffc3ff3ccf 0x7e19b3fffc3ff3cc

def z961 : W := mkw 0x8ddf8000196e8000 0x08ddf8000196e800 0xaf9b00001ff70001 0x4af9b00001ff7000

def z962 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe1c38fffc0ffffe 0xffe1c38fffc0ffff

def z963 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe43fc03ff8ff0f 0xf3fe43fc03ff8ff0

def z964 : W := mkw 0x0960010032500800 0x0096001003250080 0x3fe027003ff01c09 0xe3fe027003ff01c0

def z965 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x2fe03fc01ff03f05 0x52fe03fc01ff03f0

def z966 : W := mkw 0x8dffc0417b6ec154 0x48dffc0417b6ec15 0xffffd0c7ffffc3fb 0xeffffd0c7ffffc3f

def z967 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbfffd8c03fffc00f 0xfbfffd8c03fffc00

def z968 : W := mkw 0x896140003b6ec000 0x0896140003b6ec00 0x3f8000003fffc008 0x43f8000003fffc00

def z969 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xf19b3f3b23ff3fcf 0xff19b3f3b23ff3fc

def z970 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcfffdfffc0000003 0x9cfffdfffc000000

def z971 : W := mkw 0x0dff00003b6e8000 0x00dff00003b6e800 0xbfff00003fffc00b 0xebfff00003fffc00

def z972 : W := mkw 0xa08bcb1b01bb6cc8 0x8a08bcb1b01bb6cc 0xe19bef3b03ff3ccf 0x7e19bef3b03ff3cc

def z973 : W := mkw 0x4fdeb6b68c049200 0x04fdeb6b68c04920 0xfffffffffc0fff0f 0xffffffffffc0fff0

def z974 : W := mkw 0x461434ac8c0596a1 0x0461434ac8c0596a 0xfe1c30fcfc0ffffe 0xefe1c30fcfc0ffff

def z975 : W := mkw 0x4b4036b680000000 0x04b4036b68000000 0x4fe7ffffc0000007 0xf4fe7ffffc000000

def z976 : W := mkw 0x002149416398695c 0x4002149416398695 0x51e7dfc7e3f8e3ff 0xb51e7dfc7e3f8e3f

def z977 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcffbffffc0000005 0x5cffbffffc000000

def z978 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbffcc0003fffc008 0xcbffcc0003fffc00

def z979 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x7fe03fc7fff03f0d 0xf7fe03fc7fff03f0

def z980 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbfffd0003fffe30f 0xebfffd0003fffe30

def z981 : W := mkw 0x896140003b6ec000 0x0896140003b6ec00 0x3fe7c0003fffc00b 0xe3fe7c0003fffc00

def z982 : W := mkw 0xcdffc6b6bb6ec000 0x0cdffc6b6bb6ec00 0xffffcfffffffc00b 0xfffffcfffffffc00

def z983 : W := mkw 0x102149497fddffff 0x4102149497fddfff 0x300000003ffffff8 0x0300000003ffffff

def z984 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe7cf0fcfc0ffffe 0xefe7cf0fcfc0ffff

def z985 : W := mkw 0x8dffc2123b6ec000 0x08dffc2123b6ec00 0xbfffcf033fffc00b 0xfbfffcf033fffc00

def z986 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe02fc03ff03f09 0x53fe02fc03ff03f0

def z987 : W := mkw 0x002148416388615c 0x4002148416388615 0x51e7ffc7e388e3ff 0xf51e7ffc7e388e3f

def z988 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x2fe02fc01ff03c0d 0x72fe02fc01ff03c0

def z989 : W := mkw 0x8dffc0017b6ec050 0x48dffc0017b6ec05 0xbfffc003ffffc00b 0xebfffc003ffffc00

def z990 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe1982f3b03ff3ccc 0x5e1982f3b03ff3cc

def z991 : W := mkw 0x000008414080215c 0x4000008414080215 0x5067d8c7e008e3ff 0xb5067d8c7e008e3f

def z992 : W := mkw 0x22003b1b04913ec8 0x822003b1b04913ec 0x40003f3b00003fc4 0x140003f3b00003fc

def z993 : W := mkw 0x208a0b1a00b32c88 0x8208a0b1a00b32c8 0xe1982f3803ff3ccf 0x7e1982f3803ff3cc

def z994 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe1ffef3b03ff3ccf 0xfe1ffef3b03ff3cc

def z995 : W := mkw 0x020030080c0596a1 0x0020030080c0596a 0xfe1830383c0ffffe 0xefe1830383c0ffff

def z996 : W := mkw 0x8ddf8000196e8000 0x08ddf8000196e800 0xaf9800001fff0008 0x4af9800001fff000

def z997 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe19b273b03ff3cca 0x4e19b273b03ff3cc

def z998 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe1820383c0ffffe 0x6fe1820383c0ffff

def z999 : W := mkw 0x0940090010d02808 0x00940090010d0280 0x2f802f001ff03c0d 0x72f802f001ff03c0

def z1000 : W := mkw 0x041400080c0596a1 0x0041400080c0596a 0xfe1c20383c0ffffe 0xefe1c20383c0ffff

def z1001 : W := mkw 0xcfdeb6b698448000 0x0cfdeb6b69844800 0xcfffffffdc000007 0xfcfffffffdc00000

def z1002 : W := mkw 0x208b031a013b0c80 0x8208b031a013b0c8 0xe19b2f3b03ff1c0f 0x7e19b2f3b03ff1c0

def z1003 : W := mkw 0x0001400141084050 0x4000140014108405 0x5067d8c7e008e3ff 0xb5067d8c7e008e3f

def z1004 : W := mkw 0x2001090901bb2cc8 0x82001090901bb2cc 0xe1982f3803ff3ccf 0x7e1982f3803ff3cc

def z1005 : W := mkw 0x1b607dc076d07b1e 0x41b607dc076d07b1 0x7fe4ffc4fff8ffff 0xf7fe4ffc4fff8fff

def z1006 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xffffd8c7ffffe3ff 0xfffffd8c7ffffe3f

def z1007 : W := mkw 0x208b031a013b0c80 0x8208b031a013b0c8 0xa19b273803f71c01 0x4a19b273803f71c0

def z1008 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbf9b00003fffc00b 0x6bf9b00003fffc00

def z1009 : W := mkw 0x1b40358014501a02 0x01b40358014501a0 0x2f8027001ff01c09 0x62f8027001ff01c0

def z1010 : W := mkw 0x428a36b680000000 0x0428a36b68000000 0xc1ffffffc0000007 0xfc1ffffffc000000

def z1011 : W := mkw 0x19600dc032d0290e 0x019600dc032d0290 0x3fe02fc03ff03c0d 0xf3fe02fc03ff03c0

def z1012 : W := mkw 0x208a031a00330c80 0x8208a031a00330c8 0xa198273803f71c09 0x6a198273803f71c0

def z1013 : W := mkw 0x0960094032d0290c 0x00960094032d0290 0x3fe03fc03ff03f0d 0xf3fe03fc03ff03f0

def z1014 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x7fe03fc03ff83fcf 0xf7fe03fc03ff83fc

def z1015 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xffffe0383fffc00f 0xeffffe0383fffc00

def z1016 : W := mkw 0x208b031a013b0c80 0x8208b031a013b0c8 0xe19b273803ff3ccf 0x6e19b273803ff3cc

def z1017 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe7c38fc3c0fffff 0xffe7c38fc3c0ffff

def z1018 : W := mkw 0x1b603de436d03b2f 0x01b603de436d03b2 0x3fe03fc43ff03f3d 0xf3fe03fc43ff03f3

def z1019 : W := mkw 0x19600dc036d03b0e 0x019600dc036d03b0 0x3fe00fc03ff03f09 0xf3fe00fc03ff03f0

def z1020 : W := mkw 0x4fdeb6b688048000 0x04fdeb6b68804800 0xfffffffffc0fe3ff 0xffffffffffc0fe3f

def z1021 : W := mkw 0x069e323600000000 0x0069e32360000000 0xcfffffffc0000007 0xfcfffffffc000000

def z1022 : W := mkw 0x008a021200000000 0x0008a02120000000 0xc1fbeffbc0000007 0x7c1fbeffbc000000

def z1023 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xbe1c20383c0ffffa 0xebe1c20383c0ffff

def z1024 : W := mkw 0x4bcab6b680000000 0x04bcab6b68000000 0x01e3effbc0000001 0x101e3effbc000000

def z1025 : W := mkw 0x1b6035c036501b06 0x01b6035c036501b0 0x3fe037c03ff01f09 0xe3fe037c03ff01f0

def z1026 : W := mkw 0x2021494963996ddc 0xc2021494963996dd 0x100000002388fff8 0x0100000002388fff

def z1027 : W := mkw 0xc49fc23e892fc4a1 0x0c49fc23e892fc4a 0xc01fc03fc00fc0f2 0x0c01fc03fc00fc0f

def z1028 : W := mkw 0x89ebc0003b6ec000 0x089ebc0003b6ec00 0x3fe3c0003fffc009 0xe3fe3c0003fffc00

def z1029 : W := mkw 0xcdffc692bb6ec000 0x0cdffc692bb6ec00 0xbfffc7003fffc00b 0xebfffc7003fffc00

def z1030 : W := mkw 0x8d74c0003a44c000 0x08d74c0003a44c00 0xbffcc0003fffc00b 0xebffcc0003fffc00

def z1031 : W := mkw 0x04bf40002b2ec000 0x004bf40002b2ec00 0xbfffc0003fffc00b 0xebfffc0003fffc00

def z1032 : W := mkw 0xa49fc21a092fc480 0x8a49fc21a092fc48 0x801fc038000fc002 0x0801fc038000fc00

def z1033 : W := mkw 0x0dfe80003a448000 0x00dfe80003a44800 0xbfffc0003fffc00b 0xebfffc0003fffc00

def z1034 : W := mkw 0x8dfe80003a668000 0x08dfe80003a66800 0xbf9800003ff70008 0x4bf9800003ff7000

def z1035 : W := mkw 0x12003dec04913faf 0x012003dec04913fa 0x00003ff800003f04 0x100003ff800003f0

def z1036 : W := mkw 0x249f023f092f84e1 0x8249f023f092f84e 0xc01b003b000f00c2 0x0c01b003b000f00c

def z1037 : W := mkw 0x208b4b5b41bb6ddc 0xc208b4b5b41bb6dd 0xe19fffffc3ffffff 0x7e19fffffc3fffff

def z1038 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0x8ffbfffbc0000005 0xf8ffbfffbc000000

def z1039 : W := mkw 0x8dffc0407b6ec114 0x48dffc0407b6ec11 0xffffd8c7ffffc33f 0xfffffd8c7ffffc33

def z1040 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3f8037003ff03f0c 0xe3f8037003ff03f0

def z1041 : W := mkw 0x5fdeb6b694401202 0x05fdeb6b69440120 0xcfffffffdc000007 0xfcfffffffdc00000

def z1042 : W := mkw 0x0021404163084154 0x4002140416308415 0x5067d8c7e008c3f7 0xb5067d8c7e008c3f

def z1043 : W := mkw 0x8dfe80003a668000 0x08dfe80003a66800 0xbffc00003fffc00b 0xebffc00003fffc00

def z1044 : W := mkw 0x1b607dc176d07b5e 0x41b607dc176d07b5 0x7fe4ffc7fff0fffd 0xf7fe4ffc7fff0fff

def z1045 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0x8fffffffc0000001 0xd8fffffffc000000

def z1046 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe1c203c3c0ffffa 0x4fe1c203c3c0ffff

def z1047 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0x3fe7c0003fffc009 0x83fe7c0003fffc00

def z1048 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe7ffc03ff03f0f 0xf3fe7ffc03ff03f0

def z1049 : W := mkw 0x4bcab6b680000000 0x04bcab6b68000000 0x41e7ffffc0000007 0xb41e7ffffc000000

def z1050 : W := mkw 0x1b603dc136d03b4e 0x01b603dc136d03b4 0x7fe03fc33ff03fcd 0xf7fe03fc33ff03fc

def z1051 : W := mkw 0x1b403dc014d03b0e 0x01b403dc014d03b0 0x2f803fc01ff03f0d 0x72f803fc01ff03f0

def z1052 : W := mkw 0xe49fc23f892fc4c0 0x8e49fc23f892fc4c 0xc01fc03fc00fc0c2 0x0c01fc03fc00fc0c

def z1053 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xffffc007ffffc00b 0xeffffc007ffffc00

def z1054 : W := mkw 0xcfdeb6b690620000 0x0cfdeb6b69062000 0xcfffffffc0700007 0xfcfffffffc070000

def z1055 : W := mkw 0x1b603dc176d03b5e 0x41b603dc176d03b5 0x3fe03fc3fff03f0d 0xf3fe03fc3fff03f0

def z1056 : W := mkw 0x4dde86b680000000 0x04dde86b68000000 0x81fbcffbc0000001 0x181fbcffbc000000

def z1057 : W := mkw 0x002149416398695c 0x4002149416398695 0x7067d8c7e3f8ffff 0xb7067d8c7e3f8fff

def z1058 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xff9c303c3fffffff 0xeff9c303c3ffffff

def z1059 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xde1c303c3c0ffff6 0x8de1c303c3c0ffff

def z1060 : W := mkw 0x4fdeb6b684001200 0x04fdeb6b68400120 0xdffffffffc000307 0xfdffffffffc00030

def z1061 : W := mkw 0x4dde86b680000000 0x04dde86b68000000 0xc1ffefffc0000007 0x7c1ffefffc000000

def z1062 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbe7fc0003fffc00a 0x8be7fc0003fffc00

def z1063 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe02fc03ff01c09 0xf3fe02fc03ff01c0

def z1064 : W := mkw 0xcdffc236bb6ec000 0x0cdffc236bb6ec00 0xffffd8ffffffc00f 0xfffffd8ffffffc00

def z1065 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xaf9800001ff70000 0x4af9800001ff7000

def z1066 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xc19b2f3b03ff3cc7 0x1c19b2f3b03ff3cc

def z1067 : W := mkw 0x1960094036d03b0e 0x01960094036d03b0 0x3fe02f003ff03f0d 0xf3fe02f003ff03f0

def z1068 : W := mkw 0x4fdeb6b684001221 0x04fdeb6b68400122 0xcfffffffc0000337 0xfcfffffffc000033

def z1069 : W := mkw 0x8ddf8000196e8000 0x08ddf8000196e800 0xbf9f00003fffc00b 0xebf9f00003fffc00

def z1070 : W := mkw 0x2021494163ba695c 0xc2021494163ba695 0x5067d8c7e3f8e3ff 0xb5067d8c7e3f8e3f

def z1071 : W := mkw 0x0d7400003a448000 0x00d7400003a44800 0xbff800003ff70009 0xebff800003ff7000

def z1072 : W := mkw 0x1b403d8014d03a0a 0x01b403d8014d03a0 0x2f8027001ff03c08 0x42f8027001ff03c0

def z1073 : W := mkw 0x3021494977fb7fde 0xc3021494977fb7fd 0x300000003ffffff8 0x0300000003ffffff

def z1074 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x1fe03fc03ff03f05 0x91fe03fc03ff03f0

def z1075 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe1fbeffbc3ff3ccf 0x7e1fbeffbc3ff3cc

def z1076 : W := mkw 0x000148414188615c 0x4000148414188615 0x4067d8c7c008e3f7 0xb4067d8c7c008e3f

def z1077 : W := mkw 0x62003fbf84913ee9 0x862003fbf84913ee 0x40003fffc0003ff4 0x140003fffc0003ff

def z1078 : W := mkw 0x2200392d04913ee9 0x82200392d04913ee 0x4000303c00003ff4 0x04000303c00003ff

def z1079 : W := mkw 0x049f0000092e8000 0x0049f0000092e800 0xaf9b00001fff000b 0x6af9b00001fff000

def z1080 : W := mkw 0x208b0b1a01bb2c88 0x8208b0b1a01bb2c8 0xa19b2f3803ff3c0f 0x7a19b2f3803ff3c0

def z1081 : W := mkw 0x0000090800912c88 0x00000090800912c8 0xa1982f3803f73c0d 0x7a1982f3803f73c0

def z1082 : W := mkw 0x32003fdb44913fde 0xc32003fdb44913fd 0x40003fffc0003ff4 0x140003fffc0003ff

def z1083 : W := mkw 0x0dde821200000000 0x00dde82120000000 0xcfffffffc0000007 0xfcfffffffc000000

def z1084 : W := mkw 0x849fc000092ec000 0x0849fc000092ec00 0xbf9fc0003fffc00b 0xebf9fc0003fffc00

def z1085 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe19b2f3b03ff1cc3 0x5e19b2f3b03ff1cc

def z1086 : W := mkw 0x1b603dc036d03b0e 0x01b603dc036d03b0 0x3fe037c03ff03f08 0xc3fe037c03ff03f0

def z1087 : W := mkw 0x4bcab69280000000 0x04bcab6928000000 0xcffbfffbc0000007 0xfcffbfffbc000000

def z1088 : W := mkw 0x09610000336a0000 0x009610000336a000 0x3fe000003fff0009 0xe3fe000003fff000

def z1089 : W := mkw 0x22003b7f44913ffd 0xc22003b7f44913ff 0x40003fffc0003ff4 0x140003fffc0003ff

def z1090 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbffbc0003ff70009 0xebffbc0003ff7000

def z1091 : W := mkw 0x4fdeb6b684001200 0x04fdeb6b68400120 0xfffffffffc08ffff 0xffffffffffc08fff

def z1092 : W := mkw 0x0dff8000336a0000 0x00dff8000336a000 0xbfffc0003fff000b 0xebfffc0003fff000

def z1093 : W := mkw 0x4fdeb6b688048000 0x04fdeb6b68804800 0xefffffffdc070007 0xfefffffffdc07000

def z1094 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xbe1830383c0ffffc 0xebe1830383c0ffff

def z1095 : W := mkw 0x008b0000012a0000 0x0008b0000012a000 0xbf9b00003fff000b 0xebf9b00003fff000

def z1096 : W := mkw 0x0d7540003b4cc000 0x00d7540003b4cc00 0xbfffc0003fffc00b 0xebfffc0003fffc00

def z1097 : W := mkw 0xcdffc237fb6ec050 0x4cdffc237fb6ec05 0xffffc03fffffc0fb 0xeffffc03fffffc0f

def z1098 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xafffc0001fffc003 0x4afffc0001fffc00

def z1099 : W := mkw 0x72003fff84913fce 0x872003fff84913fc 0x40003fffc0003fc4 0x140003fffc0003fc

def z1100 : W := mkw 0x4614b02c8c0596a1 0x04614b02c8c0596a 0xfe1cf03cfc0ffffe 0xefe1cf03cfc0ffff

def z1101 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xafffc0001ff70003 0xeafffc0001ff7000

def z1102 : W := mkw 0x8dffc0017b6ec050 0x48dffc0017b6ec05 0xbfffc0003fffc0fb 0xebfffc0003fffc0f

def z1103 : W := mkw 0xcfdeb6be9c6796a1 0x0cfdeb6be9c6796a 0xaf9827381c771c00 0x4af9827381c771c0

def z1104 : W := mkw 0x8ddfc000196ec000 0x08ddfc000196ec00 0xaf9fc0001fffc00b 0x6af9fc0001fffc00

def z1105 : W := mkw 0x5b60bdc0b6d03b0e 0x05b60bdc0b6d03b0 0x3fe0ffc0fff03f0d 0xf3fe0ffc0fff03f0

def z1106 : W := mkw 0x208b0b5b41bb2ddc 0xc208b0b5b41bb2dd 0xf19f3fffe3ffffff 0xff19f3fffe3fffff

def z1107 : W := mkw 0x8dffc0403b6ec104 0x08dffc0403b6ec10 0xbfffd0c03fffc30b 0xebfffd0c03fffc30

def z1108 : W := mkw 0x896000003a668000 0x0896000003a66800 0x3fe000003ff70009 0xe3fe000003ff7000

def z1109 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xcfffffffc008c0f7 0xfcfffffffc008c0f

def z1110 : W := mkw 0x1b60358036501a02 0x01b60358036501a0 0x3fe03fc03ff01c0d 0xf3fe03fc03ff01c0

def z1111 : W := mkw 0x49ca869280000000 0x049ca86928000000 0xc1fbcffbc0000003 0x1c1fbcffbc000000

def z1112 : W := mkw 0x008b090801bb2c88 0x0008b090801bb2c8 0xe19b2f3803ff3ccf 0x7e19b2f3803ff3cc

def z1113 : W := mkw 0x002148416388615c 0x4002148416388615 0x1067d8c7e388e3f9 0x91067d8c7e388e3f

def z1114 : W := mkw 0x1b607dc076d07b1e 0x41b607dc076d07b1 0x3fe03fc03ff0ff3d 0xf3fe03fc03ff0ff3

def z1115 : W := mkw 0x1b603de436d03b0e 0x01b603de436d03b0 0x7fe03ffc3ff03f0d 0xf7fe03ffc3ff03f0

def z1116 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe19b2f3b03f73cc5 0x5e19b2f3b03f73cc

def z1117 : W := mkw 0x208b4b1b41bb6cd8 0xc208b4b1b41bb6cd 0xe19bef3bc3ff3ccf 0x7e19bef3bc3ff3cc

def z1118 : W := mkw 0x0200390004903a08 0x00200390004903a0 0x2f802f001ff03c0d 0x72f802f001ff03c0

def z1119 : W := mkw 0xcdffc212bb6ec000 0x0cdffc212bb6ec00 0xbfffc003ffffc00b 0xebfffc003ffffc00

def z1120 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xefffffffc3f0000f 0xfefffffffc3f0000

def z1121 : W := mkw 0x12003dc804913faf 0x012003dc804913fa 0x00003fc000003ff4 0x100003fc000003ff

def z1122 : W := mkw 0xcdffc236bb6ec000 0x0cdffc236bb6ec00 0xffffef3fffffc00f 0xfffffef3fffffc00

def z1123 : W := mkw 0x249f423f492fc4f1 0xc249f423f492fc4f 0xc01fc03fc00fc0f2 0x0c01fc03fc00fc0f

def z1124 : W := mkw 0x208a0b1b00b32cc8 0x8208a0b1b00b32cc 0xe1982f3b03f73ccd 0x7e1982f3b03f73cc

def z1125 : W := mkw 0x4fdeb6b690400000 0x04fdeb6b69040000 0xefffffffdc700007 0xfefffffffdc70000

def z1126 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe18303c3c0ffffc 0x4fe18303c3c0ffff

def z1127 : W := mkw 0x4fdeb6b680000000 0x04fdeb6b68000000 0xdfffffffe008c00f 0xfdfffffffe008c00

def z1128 : W := mkw 0x39eb4fd373fa695e 0xc39eb4fd373fa695 0x01e3cfc3c3f00001 0x101e3cfc3c3f0000

def z1129 : W := mkw 0x208b0b1b01bb2cc8 0x8208b0b1b01bb2cc 0xe19fef3fc3ff3ccf 0x7e19fef3fc3ff3cc

def z1130 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xfe1c103c3c0ffffa 0x8fe1c103c3c0ffff

def z1131 : W := mkw 0x8dffc0003b6ec000 0x08dffc0003b6ec00 0xbfffef003fffc00f 0xfbfffef003fffc00

def z1132 : W := mkw 0xcdffc024bb6ec000 0x0cdffc024bb6ec00 0xbfffc004ffffc00b 0xebfffc004ffffc00

def z1133 : W := mkw 0x8dffc2123b6ec000 0x08dffc2123b6ec00 0xbfffe7383fffc00b 0xebfffe7383fffc00

def z1134 : W := mkw 0x89ebc000336a4000 0x089ebc000336a400 0xbffbc0003fff000b 0xebffbc0003fff000

def z1135 : W := mkw 0x0614302c0c0596a1 0x00614302c0c0596a 0xff9c3f3c3c0fffff 0xfff9c3f3c3c0ffff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z7]),(0,[z0,z1,z8,z3,z4,z5,z9]),(0,[z0,z1,z3,z10,z4,z5,z11])],[(0,[z0,z1,z12,z3,z4,z5,z6])],[(0,[z0,z1,z3,z13,z4,z5,z6]),(0,[z14,z0,z1,z3,z15,z5,z6]),(0,[z0,z1,z3,z4,z16,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z17]),(0,[z0,z1,z3,z4,z18,z5,z6])],[(0,[z0,z1,z3,z19,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z20]),(0,[z0,z1,z3,z4,z5,z21,z6]),(1,[z0,z2,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z23,z3,z4,z24,z5])],[(0,[z25,z0,z1,z3,z4,z5,z6]),(0,[z26,z0,z1,z27,z4,z5,z6])],[(1,[z0,z1,z3,z28,z5,z6]),(0,[z0,z29,z1,z3,z4,z5,z6]),(0,[z30,z0,z1,z3,z4,z5,z6]),(0,[z0,z31,z1,z4,z32,z5,z6]),(0,[z14,z0,z1,z33,z4,z5,z6])],[(0,[z14,z0,z1,z34,z4,z5,z6]),(0,[z0,z1,z3,z4,z35,z5,z6]),(0,[z0,z1,z3,z4,z16,z36,z6]),(0,[z0,z1,z23,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z37]),(0,[z38,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z39,z5,z6])]],
   [[(1,[z22,z1,z3,z4,z5,z36]),(0,[z40,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z41,z6]),(0,[z0,z1,z42,z3,z4,z5,z6])],[(0,[z0,z43,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z10,z4,z5,z44]),(0,[z45,z0,z1,z3,z4,z5,z6]),(0,[z46,z0,z1,z3,z32,z5,z6]),(0,[z47,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z48,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z49])],[(0,[z50,z0,z1,z3,z4,z5,z6]),(1,[z0,z51,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z52,z6])],[(0,[z0,z1,z3,z4,z53,z5,z6]),(0,[z0,z54,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z55,z6])],[(0,[z56,z1,z3,z4,z57,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z58]),(0,[z0,z1,z3,z4,z59,z5,z6]),(0,[z0,z51,z1,z3,z4,z60,z6]),(0,[z0,z1,z61,z3,z4,z62,z6])],[(0,[z0,z63,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z64,z5,z6])]],
   [[(1,[z0,z1,z3,z4,z65,z6])],[(0,[z0,z1,z3,z10,z5,z11,z6]),(0,[z0,z1,z66,z3,z4,z5,z6])],[(0,[z0,z67,z1,z3,z4,z5,z6]),(0,[z68,z1,z3,z4,z5,z6,z44]),(0,[z0,z69,z70,z3,z4,z5,z6]),(0,[z71,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z72,z5,z6])],[(0,[z0,z1,z3,z73,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z65,z6]),(0,[z0,z1,z74,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z75,z5,z6]),(0,[z0,z76,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z77])],[(0,[z0,z1,z78,z3,z4,z5,z6]),(0,[z0,z1,z79,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z80]),(0,[z81,z0,z1,z3,z4,z82,z6]),(0,[z0,z1,z3,z4,z64,z32,z5]),(0,[z0,z1,z33,z3,z24,z5,z6])],[(0,[z83,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z84,z5,z6]),(0,[z0,z85,z1,z3,z4,z5,z6]),(0,[z0,z86,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z87,z4,z5,z6]),(0,[z0,z1,z3,z88,z4,z5,z6]),(0,[z0,z1,z3,z4,z89,z5,z90])],[(0,[z91,z0,z1,z3,z4,z82,z6]),(0,[z0,z1,z3,z4,z5,z6,z92]),(0,[z0,z1,z3,z4,z5,z6,z93]),(0,[z0,z1,z3,z94,z4,z5,z6]),(0,[z95,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z96,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z97,z5,z6]),(0,[z0,z1,z98,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z99,z5,z6]),(0,[z100,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z101,z6]),(0,[z0,z1,z3,z102,z4,z103,z6]),(0,[z0,z1,z3,z4,z5,z6,z104]),(0,[z0,z1,z105,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z106,z6])],[(1,[z0,z1,z3,z4,z5,z107]),(1,[z0,z1,z108,z3,z4,z5]),(0,[z0,z1,z109,z3,z4,z5,z6]),(1,[z110,z0,z3,z4,z111,z6]),(0,[z0,z112,z1,z3,z4,z5,z6]),(0,[z0,z113,z1,z3,z4,z5,z6]),(0,[z0,z1,z114,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z115]),(1,[z0,z1,z3,z116,z5,z6]),(0,[z0,z70,z1,z117,z4,z5,z6])],[(0,[z118,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z119,z5,z6]),(0,[z0,z1,z120,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z121,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z122])],[(0,[z0,z123,z1,z3,z4,z5,z6]),(0,[z124,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z125,z4,z5,z6]),(0,[z0,z1,z3,z4,z126,z5,z6]),(1,[z127,z1,z3,z128,z5,z6]),(0,[z0,z129,z1,z3,z4,z128,z6]),(0,[z0,z3,z4,z5,z130,z6,z17]),(0,[z0,z131,z1,z3,z4,z5,z130]),(0,[z0,z1,z3,z4,z5,z132,z6])],[(0,[z0,z1,z133,z3,z4,z5,z6]),(0,[z0,z1,z3,z134,z4,z5,z6]),(0,[z0,z1,z3,z4,z135,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z136])]],
   [[(0,[z0,z1,z117,z27,z4,z5,z6]),(1,[z0,z137,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z138,z6])],[(1,[z0,z1,z3,z139,z5,z6]),(0,[z0,z1,z27,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z140,z5,z6]),(0,[z14,z0,z69,z1,z4,z5,z6]),(0,[z0,z1,z4,z141,z32,z5,z6]),(0,[z142,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z143,z4,z5,z6]),(0,[z144,z0,z1,z3,z4,z5,z6])],[(0,[z0,z145,z1,z3,z4,z5,z6]),(0,[z0,z1,z146,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z147,z5,z6]),(0,[z0,z1,z3,z148,z4,z5,z6])],[(0,[z149,z0,z1,z3,z4,z5,z6]),(0,[z0,z150,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z10,z4,z5,z36]),(0,[z151,z0,z1,z3,z4,z5,z6])],[(0,[z127,z0,z1,z3,z4,z5,z6]),(0,[z0,z131,z1,z8,z3,z4,z5]),(0,[z0,z1,z152,z3,z4,z5,z6])],[(0,[z153,z0,z1,z3,z4,z5,z6]),(0,[z0,z154,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z155,z24,z5])],[(0,[z0,z1,z3,z156,z4,z5,z6]),(1,[z0,z1,z3,z4,z157,z6]),(0,[z0,z1,z3,z4,z158,z5,z6]),(0,[z159,z0,z1,z3,z4,z5,z6])],[(0,[z160,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z161,z3,z4,z5,z6]),(0,[z0,z131,z1,z3,z4,z5,z6]),(1,[z0,z1,z61,z4,z162,z6]),(0,[z0,z1,z3,z4,z5,z6,z163])]],
   [[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z1,z3,z4,z155,z5,z6])],[(0,[z0,z164,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z165,z4,z5,z6]),(0,[z0,z1,z3,z4,z166,z5,z6])],[(1,[z0,z1,z3,z4,z5,z167]),(0,[z168,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z169,z4,z5,z6]),(0,[z0,z1,z3,z4,z89,z5,z122])],[(0,[z0,z1,z3,z4,z5,z6,z170]),(0,[z0,z1,z3,z4,z5,z171,z122])],[(1,[z0,z1,z156,z4,z5,z6]),(0,[z172,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z173]),(0,[z0,z1,z3,z4,z5,z174,z6]),(0,[z0,z1,z175,z4,z5,z9,z6]),(0,[z0,z1,z3,z4,z5,z176,z6]),(0,[z177,z0,z1,z3,z4,z5,z6])],[(0,[z91,z0,z1,z3,z178,z5,z6]),(0,[z179,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z180,z6]),(0,[z0,z1,z181,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z182])],[(0,[z0,z1,z3,z183,z4,z5,z6]),(0,[z0,z1,z184,z3,z4,z5,z6]),(0,[z110,z0,z1,z3,z4,z103,z6])]],
   [[(0,[z0,z185,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z186,z6]),(0,[z0,z1,z3,z4,z60,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z187]),(0,[z0,z1,z3,z4,z188,z5,z6]),(0,[z0,z1,z3,z102,z188,z5,z6])],[(1,[z0,z189,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z190,z5,z6]),(0,[z0,z1,z3,z4,z5,z44,z122])],[(1,[z0,z1,z191,z4,z5,z6]),(0,[z0,z1,z192,z3,z4,z5,z6]),(0,[z0,z193,z1,z3,z4,z5,z6])],[(0,[z194,z0,z1,z3,z4,z5,z6]),(0,[z81,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z195,z6]),(0,[z0,z1,z3,z4,z89,z103,z6]),(0,[z14,z0,z1,z3,z196,z5,z6]),(0,[z0,z1,z8,z3,z4,z5,z197]),(0,[z198,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z199,z5,z6]),(0,[z91,z200,z1,z3,z4,z5,z6]),(0,[z0,z201,z1,z3,z4,z5,z6]),(0,[z0,z1,z202,z27,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z77,z171])],[(0,[z0,z200,z3,z4,z5,z103,z6]),(0,[z68,z0,z1,z3,z4,z5,z36])],[(0,[z118,z26,z1,z3,z4,z5,z6]),(0,[z0,z131,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z102,z4,z203,z6]),(0,[z0,z204,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z205,z3,z4,z5,z6]),(0,[z0,z1,z3,z206,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z207,z6])],[(1,[z81,z1,z3,z4,z57,z6]),(0,[z0,z208,z1,z3,z4,z5,z6]),(0,[z0,z209,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z210,z6])],[(0,[z14,z0,z1,z4,z24,z5,z6]),(0,[z0,z1,z3,z4,z211,z5,z6])],[(0,[z0,z212,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z213,z6]),(0,[z214,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z215,z5,z6]),(0,[z216,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z178,z5,z6]),(0,[z0,z1,z3,z4,z5,z217,z6]),(0,[z0,z131,z1,z3,z4,z5,z90]),(0,[z0,z1,z3,z4,z5,z6,z218])],[],[(0,[z0,z70,z1,z3,z4,z5,z6]),(0,[z0,z69,z1,z196,z4,z5,z6]),(0,[z0,z1,z3,z4,z219,z5,z6]),(0,[z0,z1,z220,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z221,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z222,z0,z1,z3,z4,z5,z6]),(0,[z118,z1,z27,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z223,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z107])],[(0,[z0,z1,z3,z224,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z225]),(1,[z0,z1,z3,z226,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z227]),(0,[z0,z1,z228,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z229,z5,z6]),(1,[z118,z1,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z230]),(0,[z0,z1,z3,z4,z231,z5,z6]),(0,[z232,z0,z1,z3,z4,z5,z6])],[(0,[z233,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z234]),(0,[z0,z1,z3,z4,z141,z5,z6]),(0,[z0,z1,z3,z4,z5,z235,z6]),(0,[z0,z1,z3,z4,z89,z5,z6]),(0,[z0,z1,z3,z236,z4,z5,z6])],[(0,[z56,z0,z200,z3,z4,z5,z6]),(0,[z26,z0,z1,z34,z4,z5,z6]),(0,[z0,z237,z1,z3,z4,z157,z6]),(0,[z0,z51,z1,z3,z4,z65,z6])],[(0,[z81,z0,z1,z3,z102,z4,z6]),(0,[z0,z1,z238,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z239,z6]),(0,[z0,z1,z8,z3,z4,z5,z6]),(0,[z0,z240,z1,z3,z102,z5,z6])],[(0,[z91,z0,z1,z3,z102,z4,z6]),(0,[z0,z241,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z242,z5,z6]),(0,[z0,z1,z243,z3,z4,z5,z6]),(0,[z0,z1,z3,z244,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z130,z36]),(0,[z0,z1,z3,z4,z62,z5,z245])],[(1,[z56,z96,z3,z4,z5,z6]),(0,[z246,z0,z1,z3,z4,z5,z6]),(0,[z0,z247,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z248,z5,z6]),(0,[z0,z240,z1,z3,z4,z111,z6]),(0,[z0,z249,z1,z3,z4,z5,z6])],[(0,[z56,z0,z1,z3,z4,z5,z167]),(0,[z46,z0,z1,z33,z3,z5,z6]),(0,[z250,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z251,z5,z6])],[(0,[z252,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z253])],[(0,[z254,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z62,z5,z6]),(0,[z0,z1,z3,z4,z255,z5,z6]),(0,[z0,z1,z175,z3,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z256,z6]),(0,[z0,z1,z3,z4,z90,z6,z122])],[(1,[z0,z1,z3,z4,z155,z5]),(0,[z0,z1,z3,z10,z4,z5,z171])],[(0,[z257,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z258,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z259,z6])],[(0,[z0,z1,z260,z3,z4,z5,z6]),(0,[z0,z1,z3,z261,z4,z5,z6]),(0,[z0,z1,z262,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z167]),(0,[z0,z1,z3,z263,z4,z5,z6]),(0,[z0,z1,z3,z4,z111,z82,z6]),(0,[z0,z1,z3,z264,z4,z5,z6]),(0,[z0,z1,z3,z265,z4,z5,z6]),(0,[z0,z1,z3,z266,z4,z5,z6]),(0,[z0,z1,z3,z267,z4,z5,z6]),(0,[z0,z268,z1,z3,z4,z5,z6])],[(0,[z269,z0,z1,z3,z4,z5,z6]),(0,[z0,z131,z1,z3,z4,z5,z122])],[(0,[z0,z270,z1,z3,z4,z5,z6]),(0,[z271,z0,z1,z3,z4,z5,z6]),(0,[z272,z0,z1,z3,z128,z5,z6]),(0,[z0,z1,z3,z4,z273,z5,z6]),(0,[z0,z1,z274,z3,z4,z5,z6]),(0,[z275,z0,z1,z3,z4,z5,z6]),(0,[z0,z240,z1,z3,z4,z188,z6])],[(0,[z56,z0,z1,z191,z4,z5,z6]),(0,[z0,z1,z3,z4,z57,z103,z6]),(0,[z0,z1,z276,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z16,z6]),(0,[z14,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z196,z4,z24,z5,z6]),(0,[z0,z1,z3,z4,z277,z5,z6]),(0,[z0,z1,z3,z278,z4,z5,z6])],[(0,[z0,z279,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z182]),(0,[z0,z1,z280,z3,z4,z5,z6]),(0,[z0,z1,z281,z3,z4,z5,z6]),(0,[z0,z1,z3,z10,z4,z5,z6])],[(0,[z0,z282,z1,z3,z4,z5,z6]),(0,[z118,z0,z1,z3,z126,z5,z6]),(0,[z0,z1,z283,z3,z4,z5,z6]),(0,[z284,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z285,z5,z6])],[(0,[z0,z1,z3,z286,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z287,z6]),(0,[z0,z1,z3,z4,z288,z5,z6])],[(1,[z26,z1,z34,z4,z5,z6]),(0,[z91,z0,z1,z3,z35,z5,z6]),(0,[z0,z131,z51,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z289]),(0,[z0,z1,z3,z290,z4,z5,z6])]],
   [[(0,[z291,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z292]),(0,[z0,z1,z293,z3,z4,z5,z6]),(0,[z0,z240,z1,z3,z5,z203,z6])],[(0,[z0,z1,z33,z3,z128,z5,z6]),(0,[z0,z1,z294,z3,z4,z5,z6]),(0,[z0,z237,z1,z3,z261,z5,z6]),(0,[z0,z1,z61,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z295,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z296]),(0,[z0,z1,z3,z4,z5,z297,z6]),(0,[z298,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z299,z6]),(0,[z0,z1,z3,z4,z5,z6,z300])],[(0,[z0,z1,z301,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z302,z6]),(0,[z303,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z44,z17]),(0,[z0,z304,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z305])],[(0,[z25,z0,z200,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z306,z5,z6]),(0,[z0,z1,z3,z4,z307,z5,z6]),(0,[z0,z1,z3,z4,z308,z5,z6]),(0,[z0,z1,z8,z3,z4,z5,z90]),(1,[z0,z1,z4,z5,z6,z77])],[(0,[z0,z1,z3,z4,z5,z309,z6]),(0,[z0,z1,z34,z310,z4,z5,z6]),(0,[z1,z3,z4,z5,z36,z6,z44]),(0,[z0,z131,z3,z4,z5,z130,z6]),(0,[z0,z1,z8,z3,z10,z4,z5]),(0,[z0,z1,z3,z4,z5,z311,z6])],[],[(0,[z312,z0,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z8,z4,z5,z6]),(0,[z0,z1,z61,z3,z4,z162,z6]),(0,[z0,z240,z1,z3,z4,z5,z6]),(0,[z0,z1,z313,z4,z5,z6,z171]),(0,[z0,z1,z3,z4,z314,z5,z6])]],
   [[(0,[z0,z1,z117,z34,z4,z5,z6]),(0,[z0,z1,z3,z4,z315,z5,z6]),(0,[z1,z3,z4,z57,z5,z82,z6]),(0,[z68,z0,z1,z3,z4,z5,z44]),(0,[z0,z316,z1,z3,z4,z5,z6]),(0,[z317,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z318,z5,z6])],[(0,[z0,z1,z175,z3,z4,z5,z36]),(0,[z319,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z320,z5,z6]),(0,[z0,z1,z3,z4,z5,z321,z6])],[(0,[z56,z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z322,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z57,z5,z6]),(0,[z0,z323,z1,z3,z4,z5,z6]),(0,[z0,z51,z1,z175,z3,z4,z5]),(0,[z0,z240,z1,z3,z4,z5,z324])],[(0,[z325,z0,z1,z3,z4,z5,z6]),(0,[z56,z0,z1,z3,z4,z5,z234]),(1,[z0,z1,z3,z102,z188,z6])],[(0,[z91,z56,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z326,z4,z5,z6])],[(0,[z0,z1,z108,z3,z310,z4,z5]),(0,[z110,z0,z247,z3,z4,z5,z6])],[(0,[z0,z1,z27,z310,z4,z5,z6]),(0,[z0,z1,z327,z3,z4,z5,z6]),(0,[z0,z1,z328,z3,z4,z5,z6]),(1,[z0,z1,z313,z4,z5,z6])],[(0,[z0,z1,z3,z4,z329,z5,z6]),(0,[z0,z1,z3,z4,z5,z90,z11])]],
   [[(0,[z0,z330,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z331]),(0,[z0,z1,z3,z4,z5,z332,z6])],[(0,[z0,z1,z3,z4,z5,z6,z333])],[(0,[z0,z1,z34,z4,z5,z162,z6]),(0,[z0,z1,z3,z4,z103,z82,z6]),(0,[z0,z1,z3,z4,z5,z6,z334]),(0,[z335,z0,z1,z3,z4,z5,z6]),(1,[z0,z247,z3,z4,z103,z6]),(0,[z0,z1,z3,z4,z24,z5,z6])],[(0,[z0,z1,z336,z3,z4,z5,z6]),(0,[z0,z1,z3,z102,z128,z5,z6]),(1,[z0,z1,z260,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z337,z6])],[(0,[z338,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z339,z6]),(0,[z0,z1,z3,z340,z4,z5,z6]),(0,[z0,z341,z1,z3,z4,z5,z6]),(0,[z0,z1,z342,z3,z4,z5,z6])],[(0,[z91,z0,z1,z3,z4,z5,z195]),(0,[z0,z1,z3,z4,z5,z82,z6]),(0,[z0,z1,z343,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z111,z5,z344]),(0,[z0,z1,z33,z196,z4,z5,z6]),(0,[z345,z0,z1,z3,z4,z5,z6]),(0,[z0,z346,z1,z3,z10,z5,z6])],[(0,[z200,z1,z96,z3,z4,z5,z6]),(0,[z0,z1,z347,z3,z4,z5,z6]),(1,[z0,z237,z3,z261,z5,z6]),(0,[z0,z348,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z349,z6])],[(0,[z0,z1,z3,z28,z4,z5,z6]),(0,[z0,z1,z350,z3,z4,z5,z6]),(0,[z0,z1,z351,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z111,z5,z6]),(0,[z0,z1,z3,z352,z4,z5,z6]),(0,[z0,z1,z3,z353,z4,z5,z6]),(0,[z0,z1,z354,z3,z4,z5,z90])]],
   [[(0,[z0,z355,z1,z3,z4,z5,z6]),(0,[z0,z237,z3,z261,z4,z5,z6]),(0,[z0,z1,z8,z3,z4,z5,z122])],[(0,[z0,z1,z3,z4,z5,z6,z356]),(0,[z46,z0,z237,z3,z4,z5,z6]),(0,[z0,z1,z357,z3,z4,z5,z6])],[(0,[z358,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z359,z6]),(0,[z0,z1,z3,z4,z5,z130,z44]),(0,[z0,z1,z3,z4,z5,z6,z360]),(0,[z0,z1,z361,z3,z4,z5,z6]),(0,[z0,z362,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z10,z5,z11]),(0,[z0,z1,z3,z4,z89,z90,z6])],[(0,[z0,z363,z1,z3,z4,z5,z6]),(0,[z0,z1,z27,z4,z5,z162,z6]),(0,[z0,z1,z3,z4,z36,z6,z356]),(0,[z0,z237,z1,z3,z32,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z364])],[(1,[z0,z1,z3,z4,z365,z6]),(0,[z200,z1,z3,z4,z57,z5,z6]),(0,[z0,z1,z3,z4,z366,z5,z6]),(0,[z0,z1,z202,z34,z4,z5,z6]),(0,[z0,z1,z3,z4,z367,z5,z6]),(0,[z0,z189,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z111,z162,z6])],[(0,[z127,z272,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z368,z6])],[(0,[z272,z1,z3,z15,z4,z5,z6]),(0,[z0,z1,z3,z369,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z370,z6]),(0,[z0,z1,z3,z4,z5,z371,z6]),(0,[z0,z1,z202,z3,z4,z62,z6])]],
   [[(0,[z0,z1,z27,z4,z5,z9,z6]),(0,[z0,z1,z3,z4,z372,z5,z6])],[(0,[z373,z0,z1,z3,z4,z5,z6]),(0,[z91,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z374,z3,z4,z5,z6])],[(0,[z0,z1,z3,z263,z4,z128,z6]),(0,[z0,z1,z375,z3,z4,z5,z6]),(0,[z0,z1,z376,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z101,z103,z6]),(0,[z0,z346,z51,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z377,z5,z6])],[(0,[z272,z0,z1,z3,z15,z5,z6]),(0,[z0,z189,z1,z3,z4,z32,z5]),(0,[z0,z1,z3,z4,z5,z378,z6])],[(0,[z0,z1,z3,z4,z379,z5,z6]),(0,[z0,z51,z3,z4,z5,z6,z17]),(0,[z0,z380,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z381,z4,z5,z6]),(0,[z0,z1,z3,z4,z382,z5,z6]),(0,[z0,z247,z1,z3,z4,z103,z6]),(1,[z383,z1,z3,z4,z5,z6]),(0,[z0,z1,z384,z3,z4,z5,z6])],[(0,[z56,z0,z96,z3,z4,z5,z6]),(0,[z0,z1,z3,z385,z4,z5,z6]),(0,[z0,z1,z386,z3,z4,z5,z6])],[(0,[z272,z1,z3,z34,z4,z5,z6])]],
   [[(0,[z387,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z388,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z389,z6]),(0,[z0,z1,z3,z4,z62,z103,z6])],[(0,[z0,z1,z390,z3,z4,z5,z6]),(0,[z0,z69,z1,z117,z4,z5,z6]),(0,[z46,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z61,z202,z4,z5,z6]),(0,[z0,z1,z3,z391,z4,z5,z6])],[(1,[z0,z1,z3,z392,z5,z6]),(0,[z0,z1,z33,z3,z15,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z393]),(0,[z0,z394,z1,z3,z4,z5,z6])],[(0,[z81,z0,z1,z3,z4,z89,z6]),(0,[z0,z247,z3,z4,z5,z103,z6]),(0,[z0,z395,z1,z3,z4,z5,z6]),(0,[z0,z1,z354,z3,z4,z5,z122])],[(0,[z56,z0,z1,z3,z139,z5,z6]),(1,[z91,z1,z3,z4,z82,z6]),(0,[z0,z70,z1,z310,z4,z5,z6]),(0,[z0,z1,z396,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z397]),(0,[z0,z1,z398,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z399,z5,z6]),(0,[z91,z0,z1,z3,z4,z89,z6]),(0,[z0,z1,z3,z310,z4,z5,z6]),(0,[z14,z400,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z401,z5,z6]),(0,[z0,z1,z3,z4,z402,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z91,z0,z1,z403,z4,z5,z6]),(0,[z0,z404,z1,z3,z4,z5,z6]),(1,[z0,z31,z1,z4,z5,z6]),(0,[z405,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z406,z4,z5,z6])],[(0,[z407,z0,z1,z3,z4,z5,z6]),(0,[z26,z1,z3,z34,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z408,z6]),(1,[z409,z0,z1,z3,z5,z6]),(1,[z0,z1,z3,z4,z5,z344]),(0,[z0,z1,z3,z4,z5,z410,z6])]],
   [[(0,[z411,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z91,z0,z1,z412,z4,z5,z6]),(0,[z0,z1,z3,z4,z413,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z414])],[(0,[z0,z1,z415,z3,z4,z5,z6]),(0,[z81,z0,z240,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z416,z5,z6]),(0,[z0,z1,z3,z4,z5,z90,z36]),(0,[z0,z1,z3,z4,z5,z417,z6]),(0,[z418,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z419])],[(0,[z0,z1,z3,z4,z5,z6,z420]),(0,[z0,z1,z175,z3,z4,z5,z44]),(0,[z0,z1,z202,z4,z62,z5,z6])],[(0,[z0,z1,z3,z421,z4,z5,z6]),(0,[z422,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z423,z6]),(0,[z424,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z91,z0,z240,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z425]),(1,[z0,z1,z4,z141,z5,z6]),(0,[z0,z1,z3,z102,z4,z111,z6]),(1,[z0,z1,z3,z4,z5,z324])],[(0,[z110,z0,z96,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z426,z5,z6]),(0,[z0,z1,z427,z3,z4,z5,z6])],[(0,[z428,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z429,z6]),(0,[z0,z3,z261,z4,z32,z5,z6])],[(0,[z118,z0,z1,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z103,z162,z6])]],
   [[(0,[z430,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z36,z6]),(0,[z0,z431,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z432,z6])],[(0,[z0,z1,z3,z4,z5,z433,z6]),(0,[z26,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z434,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z435,z6]),(1,[z0,z1,z3,z4,z5,z436]),(0,[z272,z0,z1,z3,z4,z5,z436]),(0,[z0,z1,z3,z437,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z438])],[(0,[z127,z1,z3,z4,z128,z5,z6]),(0,[z0,z117,z3,z310,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z162,z6]),(0,[z0,z346,z1,z175,z3,z4,z5])],[(0,[z0,z1,z3,z412,z4,z5,z6]),(0,[z0,z240,z1,z3,z4,z103,z6]),(0,[z0,z1,z3,z439,z4,z5,z6]),(0,[z0,z1,z4,z62,z5,z162,z6])],[(0,[z0,z1,z3,z102,z15,z5,z6]),(0,[z440,z0,z1,z3,z4,z5,z6]),(0,[z0,z441,z1,z3,z4,z5,z6]),(0,[z0,z31,z1,z3,z4,z5,z6]),(0,[z442,z0,z1,z3,z4,z5,z6]),(0,[z443,z0,z1,z3,z4,z5,z6])],[(0,[z56,z0,z1,z3,z4,z365,z6]),(0,[z0,z1,z403,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z116,z5,z6]),(1,[z0,z1,z3,z4,z444,z6]),(0,[z14,z0,z1,z3,z24,z5,z6])],[(0,[z25,z0,z96,z3,z4,z5,z6]),(0,[z110,z0,z200,z3,z4,z5,z6]),(0,[z445,z0,z1,z3,z4,z5,z6]),(1,[z0,z129,z1,z3,z4,z6]),(0,[z22,z1,z3,z4,z5,z36,z6])],[(1,[z0,z1,z446,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z234,z6]),(0,[z447,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z448,z5,z6]),(0,[z0,z1,z3,z449,z4,z5,z6])]],
   [[(0,[z0,z1,z450,z3,z4,z5,z6]),(0,[z118,z0,z1,z3,z28,z5,z6]),(0,[z0,z69,z1,z3,z4,z451,z6]),(0,[z0,z1,z3,z4,z5,z444,z6]),(0,[z0,z1,z3,z4,z5,z452,z6]),(0,[z0,z453,z1,z3,z4,z5,z6]),(0,[z0,z1,z454,z3,z4,z5,z6]),(0,[z0,z1,z3,z188,z5,z203,z6]),(0,[z0,z455,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z456,z6]),(0,[z0,z457,z1,z3,z4,z5,z6]),(0,[z1,z27,z3,z34,z4,z5,z6]),(0,[z81,z1,z3,z4,z57,z5,z6]),(1,[z0,z1,z3,z4,z59,z6]),(0,[z409,z0,z1,z3,z310,z5,z6]),(0,[z0,z1,z3,z458,z4,z5,z6]),(0,[z459,z0,z1,z3,z4,z5,z6]),(0,[z0,z346,z1,z3,z4,z5,z11])],[(1,[z25,z200,z3,z4,z5,z6]),(0,[z46,z14,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z460,z5,z6])],[(0,[z461,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z456,z6]),(0,[z0,z1,z3,z4,z5,z6,z462]),(0,[z0,z1,z354,z3,z4,z5,z6])],[(0,[z0,z1,z3,z15,z261,z5,z6]),(0,[z81,z0,z1,z3,z4,z57,z6]),(0,[z0,z463,z1,z3,z4,z5,z6]),(0,[z464,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z465,z6]),(0,[z0,z1,z466,z3,z4,z5,z6]),(1,[z46,z0,z3,z32,z5,z6]),(0,[z0,z240,z1,z3,z4,z5,z467]),(0,[z0,z1,z3,z5,z11,z6,z171])],[(0,[z0,z1,z3,z4,z468,z5,z6]),(0,[z1,z3,z15,z4,z128,z5,z6]),(0,[z91,z0,z1,z3,z4,z57,z6]),(0,[z0,z1,z3,z4,z5,z469,z6]),(0,[z0,z1,z3,z470,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z471,z6])]],
   [[(0,[z0,z1,z3,z472,z4,z5,z6])],[(0,[z0,z1,z3,z473,z4,z5,z6]),(0,[z0,z1,z474,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z475,z6]),(0,[z0,z1,z3,z15,z5,z203,z6]),(0,[z0,z1,z3,z4,z5,z476,z6]),(0,[z477,z0,z1,z3,z4,z5,z6]),(0,[z0,z478,z1,z3,z4,z5,z6]),(0,[z0,z1,z479,z3,z4,z5,z6])],[(0,[z56,z0,z1,z3,z392,z5,z6]),(0,[z0,z1,z480,z3,z4,z5,z6]),(0,[z0,z1,z205,z3,z310,z4,z5]),(0,[z383,z1,z3,z4,z5,z103,z6]),(0,[z110,z0,z1,z3,z4,z111,z6]),(1,[z0,z1,z33,z196,z5,z6]),(0,[z0,z1,z3,z4,z5,z11,z6]),(0,[z0,z1,z3,z4,z481,z5,z6])],[(0,[z482,z0,z1,z3,z4,z5,z6])],[(0,[z0,z483,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z484]),(0,[z0,z1,z3,z485,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z486,z6]),(0,[z0,z1,z487,z3,z4,z5,z6]),(0,[z0,z69,z3,z310,z4,z5,z6]),(0,[z0,z1,z3,z488,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z489,z6]),(0,[z0,z1,z3,z4,z5,z6,z490]),(0,[z0,z491,z1,z3,z4,z5,z6])],[(0,[z492,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z128,z5,z11,z6]),(0,[z0,z69,z1,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z101,z6]),(0,[z0,z493,z1,z3,z4,z5,z6]),(0,[z0,z1,z494,z3,z4,z5,z6])],[(0,[z495,z0,z1,z3,z4,z5,z6]),(0,[z91,z1,z3,z4,z5,z82,z6])],[(0,[z0,z496,z1,z3,z4,z5,z6]),(0,[z0,z69,z1,z310,z4,z5,z6]),(0,[z0,z1,z3,z94,z310,z5,z6]),(0,[z0,z237,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z497,z5,z6])]],
   [[(0,[z0,z1,z3,z15,z5,z11,z6]),(0,[z0,z1,z3,z4,z5,z6,z44]),(0,[z0,z1,z175,z3,z4,z5,z90]),(0,[z0,z1,z3,z4,z5,z6,z498]),(0,[z0,z1,z354,z3,z4,z89,z6]),(0,[z0,z1,z3,z4,z5,z6,z499])],[(0,[z0,z70,z117,z3,z4,z5,z6]),(1,[z0,z1,z202,z4,z62,z6]),(0,[z0,z1,z175,z3,z10,z4,z5])],[(0,[z127,z0,z1,z3,z128,z5,z6]),(0,[z0,z1,z3,z4,z500,z5,z6]),(1,[z0,z1,z3,z35,z5,z6]),(0,[z68,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z501,z3,z4,z5,z6]),(0,[z14,z0,z1,z4,z5,z9,z6])],[(0,[z0,z1,z61,z4,z5,z162,z6]),(0,[z0,z1,z3,z502,z4,z5,z6]),(0,[z0,z503,z1,z3,z4,z5,z6]),(0,[z0,z504,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z89,z90])],[(0,[z0,z505,z1,z3,z4,z5,z6]),(0,[z46,z0,z3,z4,z32,z5,z6]),(0,[z0,z1,z506,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z507]),(0,[z0,z1,z3,z4,z5,z6,z508])],[(0,[z0,z1,z3,z4,z509,z5,z6]),(0,[z0,z1,z3,z4,z5,z510,z6]),(0,[z0,z1,z511,z3,z4,z5,z6])],[(0,[z118,z0,z1,z3,z4,z5,z115]),(0,[z0,z1,z3,z4,z128,z5,z6]),(0,[z512,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z513,z5,z6])],[(0,[z0,z1,z446,z3,z4,z5,z6]),(0,[z0,z514,z1,z3,z4,z5,z6]),(0,[z0,z515,z1,z3,z4,z5,z6]),(0,[z0,z1,z516,z3,z4,z5,z6]),(0,[z0,z1,z517,z3,z4,z5,z6]),(0,[z518,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z519,z5,z6])]],
   [[(0,[z520,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z521,z6]),(0,[z0,z1,z3,z4,z5,z6,z522]),(0,[z0,z346,z1,z3,z5,z6,z171]),(0,[z0,z1,z3,z4,z5,z523,z6])],[(0,[z118,z272,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z524,z6]),(1,[z0,z1,z3,z4,z6,z356]),(0,[z0,z1,z3,z4,z32,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z525]),(0,[z14,z304,z1,z3,z4,z5,z6]),(0,[z0,z240,z1,z3,z4,z203,z6])],[(0,[z0,z1,z526,z3,z4,z5,z6]),(0,[z0,z1,z34,z196,z4,z5,z6]),(0,[z0,z1,z34,z4,z5,z9,z6]),(0,[z0,z1,z3,z4,z527,z5,z6]),(0,[z0,z1,z3,z528,z4,z5,z6]),(0,[z0,z529,z1,z3,z4,z5,z6]),(0,[z530,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z531,z4,z5,z6])],[(1,[z0,z1,z3,z4,z64,z5]),(0,[z0,z237,z1,z3,z4,z444,z6]),(0,[z0,z237,z1,z33,z3,z5,z6]),(0,[z0,z532,z1,z3,z4,z5,z6])],[(0,[z22,z68,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z90,z44]),(0,[z0,z1,z3,z4,z5,z533,z6]),(0,[z0,z51,z1,z3,z4,z5,z130]),(0,[z0,z1,z33,z3,z196,z5,z6]),(0,[z0,z1,z313,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z534,z6]),(0,[z0,z69,z1,z3,z4,z59,z6]),(0,[z0,z1,z535,z3,z4,z5,z6]),(0,[z0,z536,z1,z3,z4,z5,z6])],[(0,[z0,z346,z1,z3,z128,z5,z6]),(1,[z0,z69,z310,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z537,z6]),(0,[z0,z1,z3,z4,z5,z538,z6])],[(0,[z0,z1,z3,z15,z32,z5,z6]),(0,[z539,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z62,z5,z540])]],
   [[(0,[z541,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z9,z6,z197])],[(0,[z56,z0,z1,z3,z4,z456,z6]),(0,[z0,z1,z3,z4,z365,z5,z6]),(0,[z0,z1,z8,z27,z4,z5,z6]),(0,[z0,z1,z542,z3,z4,z5,z6]),(0,[z0,z1,z543,z3,z4,z5,z6])],[(0,[z544,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z116,z5,z6]),(0,[z0,z1,z3,z4,z5,z36,z122]),(0,[z0,z1,z3,z4,z545,z5,z6]),(0,[z0,z51,z1,z8,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z546,z6])],[(0,[z0,z1,z27,z196,z4,z5,z6]),(0,[z22,z0,z1,z3,z226,z5,z6]),(1,[z400,z1,z3,z4,z5,z6]),(1,[z0,z1,z354,z3,z4,z122])],[(0,[z0,z1,z3,z4,z5,z547,z6]),(0,[z0,z346,z1,z3,z4,z5,z36]),(0,[z0,z1,z3,z4,z111,z6,z122]),(0,[z0,z1,z3,z4,z5,z130,z6]),(0,[z0,z1,z175,z3,z4,z5,z122]),(0,[z0,z1,z3,z4,z5,z548,z6])],[(0,[z549,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z178,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z550]),(0,[z0,z51,z1,z3,z4,z5,z6]),(0,[z0,z551,z1,z3,z4,z5,z6])],[(0,[z0,z1,z552,z3,z4,z5,z6])],[(0,[z0,z553,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z451,z6]),(0,[z0,z1,z554,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z139,z5,z6]),(0,[z25,z200,z1,z3,z4,z5,z6]),(0,[z91,z81,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z195]),(0,[z0,z1,z555,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z103,z6]),(0,[z0,z1,z3,z4,z5,z556,z6])],[(0,[z118,z0,z1,z3,z4,z5,z182]),(0,[z0,z1,z557,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z558]),(0,[z0,z559,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z560,z6])],[(1,[z0,z1,z3,z126,z5,z6]),(0,[z0,z1,z3,z4,z5,z451,z6]),(0,[z0,z1,z202,z3,z4,z5,z6]),(0,[z0,z1,z561,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z562])],[(0,[z0,z563,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z564,z6]),(0,[z272,z0,z1,z388,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z565,z6]),(0,[z0,z1,z196,z4,z5,z9,z6]),(0,[z0,z1,z175,z3,z4,z5,z197]),(0,[z0,z1,z566,z3,z4,z5,z6])],[(0,[z56,z1,z96,z3,z4,z5,z6]),(0,[z567,z0,z1,z3,z4,z5,z6]),(0,[z81,z0,z1,z3,z4,z6,z122]),(0,[z0,z568,z1,z3,z4,z5,z6]),(1,[z0,z240,z1,z3,z203,z6]),(0,[z0,z1,z3,z4,z5,z569,z6])],[(0,[z0,z1,z3,z570,z4,z5,z6]),(0,[z0,z1,z571,z3,z4,z5,z6]),(0,[z0,z1,z572,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z573]),(0,[z574,z0,z1,z3,z4,z5,z6])],[(0,[z14,z0,z1,z27,z4,z5,z6]),(1,[z0,z1,z381,z4,z5,z6]),(0,[z272,z0,z1,z381,z4,z5,z6]),(0,[z91,z0,z1,z3,z4,z6,z122]),(0,[z409,z0,z1,z3,z4,z5,z6]),(0,[z14,z0,z237,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z575,z6]),(0,[z0,z1,z3,z4,z5,z576,z6]),(0,[z0,z1,z3,z577,z4,z5,z6]),(0,[z0,z578,z1,z3,z4,z5,z6]),(1,[z0,z1,z8,z4,z5,z197])],[(0,[z91,z0,z1,z3,z4,z5,z107]),(0,[z0,z1,z3,z4,z579,z5,z6]),(0,[z0,z1,z3,z4,z580,z5,z6])]],
   [[(0,[z0,z1,z581,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z582]),(0,[z0,z1,z202,z3,z4,z162,z6]),(1,[z0,z1,z3,z4,z5,z245]),(1,[z0,z1,z3,z4,z5,z467])],[(0,[z0,z1,z3,z4,z5,z583,z6]),(0,[z0,z1,z3,z4,z111,z5,z510])],[(0,[z0,z1,z3,z4,z584,z5,z6]),(0,[z0,z1,z3,z585,z4,z5,z6])],[(0,[z586,z0,z1,z3,z4,z5,z6]),(0,[z587,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z588,z4,z5,z6]),(0,[z0,z589,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z590,z5,z6])],[(0,[z272,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z591,z3,z4,z5,z6]),(0,[z0,z131,z1,z175,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z11,z122])],[(0,[z118,z1,z3,z4,z128,z5,z6]),(1,[z272,z1,z3,z15,z5,z6]),(0,[z91,z0,z137,z3,z4,z5,z6]),(0,[z0,z1,z592,z3,z4,z5,z6]),(0,[z0,z51,z1,z3,z4,z5,z17]),(0,[z593,z0,z1,z3,z4,z5,z6]),(1,[z14,z0,z1,z24,z5,z6]),(0,[z0,z1,z594,z3,z4,z5,z6])],[(0,[z595,z0,z1,z3,z4,z5,z6]),(0,[z596,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z597,z6])],[(0,[z118,z0,z1,z34,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z598])]],
   [[(0,[z0,z599,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z600,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z324,z6]),(0,[z0,z1,z3,z4,z5,z601,z6])],[(0,[z0,z1,z3,z602,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z603,z6]),(0,[z0,z604,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z605,z4,z5,z6]),(0,[z0,z1,z606,z3,z4,z5,z6])],[(0,[z0,z1,z3,z226,z4,z5,z6]),(0,[z22,z0,z1,z3,z4,z5,z36]),(0,[z0,z1,z8,z3,z4,z5,z36]),(1,[z0,z70,z117,z4,z5,z6]),(0,[z0,z1,z3,z4,z607,z5,z6]),(0,[z0,z1,z608,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z609,z6])],[(0,[z127,z0,z1,z3,z15,z5,z6]),(0,[z0,z1,z610,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z611,z6]),(0,[z0,z1,z3,z4,z5,z612,z6]),(0,[z0,z51,z1,z3,z4,z5,z90]),(0,[z0,z1,z33,z3,z4,z5,z6]),(0,[z613,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z614,z6]),(0,[z0,z615,z1,z3,z4,z5,z6]),(0,[z616,z0,z1,z3,z4,z5,z6]),(0,[z0,z51,z1,z3,z10,z4,z5]),(0,[z0,z1,z617,z3,z4,z5,z6]),(0,[z0,z1,z618,z3,z4,z5,z6])],[(0,[z0,z96,z3,z4,z5,z103,z6]),(0,[z0,z1,z3,z261,z128,z5,z6]),(0,[z0,z1,z175,z3,z4,z5,z6])],[(0,[z619,z0,z1,z3,z4,z5,z6]),(0,[z0,z137,z1,z3,z4,z5,z6]),(0,[z0,z1,z620,z3,z4,z5,z6]),(0,[z0,z621,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z103,z6,z122]),(0,[z622,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z623]),(1,[z0,z346,z1,z3,z5,z171])],[(0,[z624,z0,z1,z3,z4,z5,z6]),(0,[z0,z625,z1,z3,z4,z5,z6]),(0,[z626,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z627,z5,z6]),(0,[z0,z1,z3,z4,z111,z57,z6]),(0,[z0,z1,z3,z4,z628,z5,z6]),(0,[z0,z1,z3,z4,z629,z5,z6]),(0,[z0,z3,z4,z111,z5,z103,z6]),(0,[z0,z1,z3,z630,z4,z5,z6]),(0,[z0,z1,z3,z102,z4,z188,z6])],[(0,[z631,z0,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z128,z5,z6]),(0,[z0,z1,z3,z4,z5,z632,z6]),(1,[z0,z1,z403,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z633,z6]),(0,[z0,z70,z1,z196,z4,z5,z6]),(0,[z0,z1,z3,z4,z157,z5,z6])],[(0,[z0,z1,z3,z4,z634,z5,z6]),(1,[z0,z1,z3,z4,z60,z6]),(0,[z0,z1,z3,z196,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z9,z6]),(0,[z0,z635,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z636,z6]),(0,[z0,z1,z3,z4,z637,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z638]),(0,[z0,z639,z1,z3,z4,z5,z6])],[(1,[z0,z1,z412,z4,z5,z6]),(0,[z0,z640,z1,z3,z4,z5,z6])],[(1,[z0,z1,z23,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z641]),(0,[z0,z1,z3,z4,z5,z6,z642])],[(0,[z0,z1,z3,z4,z5,z643,z6]),(0,[z0,z644,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z203,z6])],[(0,[z0,z346,z1,z3,z15,z5,z6]),(1,[z0,z1,z205,z3,z4,z5]),(0,[z383,z0,z1,z3,z4,z5,z6]),(0,[z645,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z646,z6]),(0,[z0,z1,z3,z4,z5,z6,z647]),(0,[z0,z1,z8,z196,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z197])],[(0,[z0,z1,z3,z128,z5,z203,z6])],[(0,[z0,z1,z3,z4,z648,z5,z6]),(0,[z649,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z36,z17]),(1,[z0,z1,z3,z4,z5,z510])],[(0,[z0,z1,z3,z650,z4,z5,z6]),(0,[z110,z0,z3,z4,z111,z5,z6]),(0,[z651,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z652,z5,z6])],[(0,[z22,z0,z1,z260,z4,z5,z6]),(0,[z0,z1,z3,z102,z4,z5,z6])],[(0,[z1,z3,z34,z4,z128,z5,z6]),(0,[z0,z1,z3,z4,z653,z5,z6]),(0,[z0,z346,z1,z3,z4,z5,z44]),(0,[z0,z1,z3,z654,z4,z5,z6]),(0,[z0,z655,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z656,z6]),(0,[z0,z1,z8,z4,z5,z6,z197]),(0,[z0,z346,z1,z3,z4,z5,z171])],[(0,[z0,z51,z1,z3,z4,z5,z122]),(0,[z0,z1,z3,z4,z5,z657,z6]),(1,[z304,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z658])]],
   [[(0,[z659,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z660,z5,z6]),(0,[z661,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z662,z3,z4,z5,z6])],[(0,[z0,z663,z1,z3,z4,z5,z6]),(0,[z22,z0,z1,z156,z4,z5,z6]),(0,[z14,z0,z70,z1,z4,z5,z6]),(0,[z0,z346,z131,z1,z3,z4,z5]),(0,[z0,z664,z1,z3,z4,z5,z6]),(0,[z0,z1,z354,z3,z4,z6,z122])],[(0,[z0,z1,z3,z191,z4,z5,z6]),(0,[z0,z1,z3,z665,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z666,z6]),(0,[z0,z1,z3,z4,z89,z111,z6]),(0,[z0,z346,z1,z8,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z667,z6]),(0,[z0,z1,z3,z15,z4,z5,z6]),(0,[z0,z1,z3,z4,z668,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z171])],[(0,[z56,z0,z1,z3,z4,z5,z6]),(0,[z0,z669,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z670,z4,z5,z6])],[(0,[z0,z1,z3,z4,z671,z5,z6]),(0,[z672,z0,z1,z3,z4,z5,z6]),(0,[z0,z346,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z673]),(0,[z0,z1,z3,z4,z5,z6,z245]),(0,[z0,z1,z3,z4,z5,z6,z467])],[(0,[z0,z674,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z80]),(0,[z272,z0,z1,z3,z4,z5,z80]),(0,[z0,z1,z3,z4,z675,z5,z6])]],
   [[(1,[z68,z1,z3,z4,z5,z44]),(0,[z0,z1,z117,z3,z4,z5,z6]),(0,[z676,z0,z1,z3,z4,z5,z6]),(0,[z46,z0,z1,z3,z261,z5,z6]),(0,[z0,z247,z1,z3,z4,z111,z6]),(0,[z0,z1,z3,z4,z5,z6,z344]),(0,[z0,z1,z3,z677,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z436,z6]),(0,[z0,z1,z3,z4,z5,z678,z6])],[(0,[z0,z1,z388,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6])],[(0,[z0,z1,z3,z34,z4,z5,z6]),(0,[z91,z0,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z62,z111,z6]),(0,[z0,z679,z1,z3,z4,z5,z6]),(0,[z400,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z680,z6]),(0,[z681,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z392,z4,z5,z6]),(0,[z0,z1,z682,z3,z4,z5,z6]),(0,[z0,z129,z1,z3,z4,z5,z6]),(0,[z0,z683,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z540])],[(0,[z684,z0,z1,z3,z4,z5,z6]),(0,[z685,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z686]),(0,[z687,z0,z1,z3,z4,z5,z6])],[(0,[z688,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z689,z5,z6]),(0,[z0,z1,z3,z4,z5,z115,z6])],[(0,[z0,z1,z3,z128,z32,z5,z6]),(1,[z0,z1,z175,z4,z5,z9]),(0,[z0,z1,z3,z4,z5,z90,z171])]],
   [[(0,[z690,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z691,z5,z6]),(0,[z0,z1,z3,z4,z5,z692,z6])],[(0,[z0,z1,z8,z34,z4,z5,z6]),(0,[z0,z1,z3,z693,z4,z5,z6]),(0,[z0,z1,z694,z3,z4,z5,z6]),(0,[z0,z1,z695,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z696,z5,z6])],[(0,[z56,z0,z1,z446,z4,z5,z6]),(0,[z0,z1,z3,z4,z697,z5,z6]),(0,[z0,z1,z8,z175,z4,z5,z6])],[(0,[z698,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z108,z3,z4,z5,z6]),(0,[z110,z0,z1,z3,z4,z5,z6]),(0,[z0,z131,z1,z3,z10,z4,z5]),(0,[z699,z0,z1,z3,z4,z5,z6])],[(0,[z0,z200,z1,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z4,z5,z44]),(0,[z0,z1,z8,z3,z4,z5,z44])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z700,z6]),(0,[z0,z701,z1,z3,z4,z5,z6])],[(0,[z702,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z703,z4,z5,z6]),(1,[z0,z1,z3,z94,z5,z6]),(0,[z0,z1,z3,z4,z704,z5,z6]),(0,[z0,z705,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z90,z6]),(0,[z0,z1,z3,z4,z5,z6,z706])],[(1,[z0,z1,z3,z263,z4,z6]),(0,[z0,z1,z3,z4,z5,z540,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[],[(0,[z0,z1,z3,z4,z60,z6]),(0,[z707,z1,z3,z4,z5,z6])],[(0,[z127,z1,z3,z128,z5,z6])],[(0,[z0,z1,z191,z4,z365,z6]),(0,[z0,z1,z412,z4,z5,z6]),(0,[z0,z1,z61,z4,z708,z6])],[(0,[z0,z137,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z709]),(0,[z0,z1,z4,z5,z710,z6])],[(0,[z711,z1,z3,z4,z5,z6])],[],[(0,[z0,z1,z3,z392,z5,z167]),(0,[z0,z1,z3,z4,z712,z6]),(0,[z71,z1,z3,z15,z5,z6]),(0,[z0,z1,z260,z226,z5,z6]),(0,[z0,z1,z4,z5,z6,z713])]],
   [[(0,[z0,z714,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z6]),(0,[z0,z1,z8,z458,z4,z5])],[(0,[z715,z1,z3,z4,z5,z6])],[(0,[z0,z1,z716,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z717]),(0,[z0,z1,z3,z4,z157,z6]),(0,[z0,z1,z3,z4,z5,z510])],[(0,[z0,z2,z3,z4,z82,z6]),(0,[z0,z1,z156,z226,z5,z6]),(0,[z0,z1,z8,z4,z5,z227])],[(0,[z0,z1,z3,z4,z718,z5]),(0,[z719,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z720,z6]),(0,[z0,z1,z175,z4,z5,z721])],[(0,[z0,z1,z3,z4,z5,z722]),(0,[z0,z1,z388,z4,z5,z80]),(0,[z723,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z167]),(0,[z304,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z724,z6]),(0,[z0,z1,z3,z4,z157,z725])],[(0,[z1,z3,z4,z5,z726,z44]),(0,[z0,z1,z3,z4,z5,z727]),(1,[z0,z1,z3,z4,z728])]],
   [[(0,[z0,z1,z191,z392,z5,z6]),(0,[z0,z1,z381,z4,z5,z80]),(0,[z47,z1,z3,z4,z57,z6])],[(0,[z0,z1,z729,z4,z5,z6]),(0,[z177,z1,z3,z128,z5,z6]),(0,[z22,z1,z260,z4,z5,z36]),(0,[z95,z1,z3,z4,z5,z36]),(0,[z46,z0,z361,z3,z5,z6]),(0,[z0,z1,z730,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z182]),(0,[z400,z1,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z731])],[(0,[z0,z1,z3,z4,z365,z234]),(0,[z732,z96,z3,z4,z5,z6]),(0,[z0,z1,z3,z733,z4,z6]),(0,[z14,z0,z1,z413,z5,z6]),(0,[z0,z1,z3,z5,z6,z734]),(0,[z0,z1,z3,z4,z6,z728])],[],[(0,[z0,z1,z3,z139,z456,z6]),(0,[z56,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z735,z6])],[(0,[z0,z1,z3,z4,z5,z736]),(0,[z0,z1,z3,z4,z89,z510])],[(0,[z0,z1,z191,z4,z5,z6]),(0,[z272,z1,z3,z15,z5,z80]),(0,[z0,z1,z3,z5,z737,z6]),(0,[z0,z1,z3,z4,z60,z90])]],
   [[(0,[z0,z200,z3,z4,z456,z6])],[(0,[z0,z1,z3,z4,z5,z738]),(0,[z56,z96,z3,z4,z365,z6])],[(0,[z0,z1,z3,z4,z739,z6]),(0,[z304,z1,z8,z4,z5,z6]),(0,[z0,z1,z175,z4,z5,z499])],[(0,[z0,z1,z3,z4,z740,z6]),(0,[z0,z1,z3,z4,z5,z540]),(0,[z0,z741,z3,z4,z5,z6])],[(0,[z0,z1,z446,z4,z5,z167]),(0,[z1,z742,z34,z4,z5,z6]),(0,[z91,z1,z3,z178,z82,z6]),(0,[z0,z1,z743,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z744])],[(0,[z1,z3,z4,z745,z82,z6]),(0,[z0,z746,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z456,z167]),(0,[z0,z1,z3,z747,z5,z6]),(0,[z0,z748,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z195]),(0,[z0,z1,z3,z226,z5,z44]),(0,[z0,z1,z260,z4,z5,z36]),(0,[z0,z237,z3,z749,z5,z6])],[(0,[z0,z1,z3,z35,z5,z107]),(0,[z0,z1,z3,z4,z90,z728])]],
   [[(0,[z0,z1,z3,z392,z5,z234]),(0,[z0,z1,z202,z4,z648,z6]),(0,[z0,z346,z1,z3,z5,z58]),(1,[z1,z3,z4,z745,z6]),(0,[z750,z1,z3,z4,z5,z6])],[(0,[z0,z240,z2,z3,z4,z6])],[(0,[z409,z0,z69,z1,z5,z6])],[(0,[z1,z732,z3,z4,z5,z6]),(0,[z200,z3,z4,z5,z217,z6]),(0,[z0,z751,z3,z4,z5,z6]),(0,[z0,z1,z752,z3,z4,z5]),(0,[z0,z1,z3,z4,z753,z6]),(0,[z0,z1,z3,z4,z754,z6]),(0,[z755,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z756]),(0,[z0,z1,z757,z4,z5,z6]),(0,[z0,z1,z758,z4,z5,z6]),(0,[z0,z1,z3,z15,z5,z436]),(0,[z0,z1,z260,z116,z5,z6]),(0,[z0,z69,z205,z310,z4,z5]),(0,[z0,z1,z3,z4,z5,z759]),(0,[z0,z1,z3,z10,z607,z5])],[(0,[z0,z1,z3,z226,z5,z6]),(0,[z0,z137,z3,z35,z5,z6]),(0,[z760,z1,z3,z4,z5,z6]),(0,[z0,z1,z8,z4,z5,z305])],[(0,[z56,z96,z3,z392,z5,z6]),(0,[z118,z1,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z761]),(0,[z0,z1,z3,z762,z5,z6]),(0,[z0,z1,z3,z263,z4,z6]),(0,[z22,z1,z3,z4,z36,z356]),(0,[z763,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z59,z736])],[(0,[z0,z1,z3,z4,z5,z234]),(0,[z0,z1,z191,z4,z456,z6]),(0,[z0,z1,z3,z4,z764,z5]),(0,[z1,z3,z765,z128,z5,z6])]],
   [[(0,[z409,z0,z1,z34,z5,z6]),(0,[z0,z1,z3,z4,z6,z766]),(0,[z0,z1,z3,z767,z5,z6]),(0,[z383,z1,z3,z768,z5,z6]),(0,[z0,z1,z3,z769,z5,z6])],[(0,[z46,z0,z3,z64,z32,z5])],[(0,[z0,z1,z3,z4,z5,z770]),(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z771,z5,z6]),(0,[z0,z1,z3,z4,z772,z6]),(0,[z0,z1,z3,z4,z773,z5]),(0,[z0,z51,z3,z4,z5,z774])],[(0,[z0,z1,z775,z3,z4,z5]),(0,[z776,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z60,z122])],[(0,[z0,z1,z3,z28,z5,z6])],[(0,[z56,z96,z3,z4,z5,z6]),(0,[z0,z1,z388,z128,z5,z6])],[(0,[z0,z1,z3,z4,z5,z777]),(0,[z0,z1,z778,z4,z5,z6]),(0,[z0,z1,z779,z4,z5,z6]),(0,[z0,z1,z4,z5,z721,z197])],[(0,[z22,z1,z3,z4,z5,z36]),(0,[z0,z1,z8,z3,z4,z65])]],
   [[(0,[z0,z1,z780,z4,z5,z6]),(0,[z0,z1,z3,z781,z5,z6]),(0,[z0,z1,z175,z352,z4,z5]),(0,[z0,z1,z3,z4,z590,z122])],[(0,[z0,z1,z3,z782,z5,z6]),(0,[z0,z1,z3,z4,z783,z6]),(0,[z409,z0,z1,z205,z3,z5]),(0,[z0,z1,z3,z4,z784,z6]),(0,[z14,z0,z1,z497,z5,z6])],[(0,[z0,z1,z3,z4,z785,z6]),(0,[z0,z1,z3,z4,z5,z786]),(0,[z91,z1,z3,z4,z519,z6]),(0,[z383,z1,z3,z787,z5,z6]),(0,[z0,z1,z8,z449,z4,z5])],[(0,[z0,z31,z1,z128,z5,z6]),(0,[z0,z1,z3,z4,z5,z788]),(0,[z0,z51,z3,z4,z5,z17])],[(0,[z0,z1,z3,z789,z5,z6]),(0,[z0,z1,z3,z4,z5,z790]),(0,[z0,z791,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z792,z6]),(0,[z95,z1,z3,z15,z5,z6]),(0,[z46,z0,z3,z749,z5,z6]),(0,[z793,z1,z3,z4,z5,z6])],[(0,[z0,z1,z446,z4,z5,z234]),(0,[z0,z794,z3,z4,z5,z6]),(0,[z0,z795,z1,z3,z5,z6]),(0,[z0,z504,z3,z4,z111,z6])],[(0,[z383,z96,z3,z4,z5,z6]),(0,[z0,z1,z796,z4,z5,z6]),(0,[z0,z2,z3,z4,z89,z6]),(0,[z0,z1,z3,z4,z5,z797]),(0,[z0,z1,z3,z798,z5,z6]),(0,[z0,z455,z3,z4,z103,z6]),(0,[z0,z54,z3,z4,z111,z6]),(1,[z0,z1,z4,z5,z721])],[(0,[z0,z1,z3,z4,z456,z234]),(0,[z0,z1,z3,z799,z5,z6]),(0,[z272,z1,z3,z765,z5,z6]),(0,[z0,z2,z403,z4,z5,z6]),(0,[z0,z1,z3,z4,z65,z6])]],
   [[(0,[z0,z1,z3,z4,z800,z6]),(0,[z0,z1,z3,z126,z5,z115]),(0,[z418,z1,z3,z4,z5,z44]),(0,[z0,z247,z3,z4,z801,z6]),(0,[z0,z1,z802,z4,z5,z6]),(0,[z0,z1,z3,z803,z5,z6])],[(0,[z0,z1,z205,z3,z94,z5])],[(0,[z0,z1,z3,z4,z804,z6]),(0,[z0,z1,z805,z3,z4,z5]),(0,[z0,z1,z3,z4,z806,z6]),(0,[z0,z1,z807,z4,z5,z6])],[(0,[z56,z96,z446,z4,z5,z6]),(0,[z0,z137,z3,z4,z5,z195]),(0,[z0,z117,z808,z4,z5,z6]),(0,[z0,z1,z202,z4,z62,z540])],[(0,[z0,z1,z8,z4,z5,z360])],[(0,[z56,z96,z3,z4,z456,z6]),(0,[z0,z1,z3,z809,z4,z6]),(0,[z0,z1,z4,z5,z6,z810]),(0,[z0,z1,z3,z811,z5,z6])],[(0,[z0,z1,z3,z4,z812,z6]),(0,[z0,z1,z3,z4,z813,z6]),(0,[z14,z0,z463,z1,z5,z6]),(0,[z0,z70,z808,z4,z5,z6]),(0,[z46,z0,z31,z32,z5,z6]),(0,[z0,z1,z3,z787,z5,z6]),(0,[z0,z1,z3,z4,z5,z814])],[(1,[z1,z742,z4,z5,z6]),(0,[z0,z1,z3,z4,z195,z122]),(0,[z815,z1,z3,z4,z5,z6]),(0,[z110,z0,z3,z4,z111,z344])]],
   [[(0,[z0,z1,z3,z4,z816,z6]),(0,[z0,z1,z4,z5,z817,z6]),(1,[z0,z3,z4,z801,z6]),(0,[z0,z1,z3,z4,z5,z818]),(0,[z0,z1,z3,z4,z5,z819]),(0,[z0,z1,z175,z4,z481,z5])],[(0,[z0,z1,z108,z3,z4,z5]),(0,[z0,z1,z196,z135,z5,z6]),(0,[z46,z0,z141,z32,z5,z6]),(0,[z110,z0,z3,z4,z111,z6]),(0,[z0,z820,z3,z4,z5,z6])],[(0,[z0,z1,z3,z821,z5,z6]),(0,[z0,z1,z3,z116,z5,z6]),(0,[z383,z1,z3,z4,z82,z6]),(0,[z383,z247,z3,z4,z103,z6]),(0,[z822,z1,z3,z4,z5,z6])],[(0,[z0,z1,z823,z3,z4,z6]),(0,[z409,z0,z70,z1,z5,z6])],[(0,[z0,z824,z3,z4,z5,z6]),(0,[z14,z0,z1,z545,z5,z6]),(0,[z0,z825,z1,z3,z5,z6])],[(0,[z0,z240,z1,z3,z207,z6]),(0,[z0,z1,z826,z4,z5,z6])],[(0,[z0,z1,z3,z4,z827,z6]),(1,[z732,z3,z4,z5,z6]),(0,[z0,z828,z1,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z829]),(0,[z1,z3,z4,z5,z745,z6]),(0,[z1,z830,z3,z4,z5,z6])],[(0,[z0,z1,z831,z4,z5,z6]),(0,[z0,z1,z3,z102,z188,z6])]],
   [[(0,[z0,z1,z3,z139,z5,z6]),(0,[z0,z1,z260,z4,z5,z44]),(0,[z0,z1,z832,z4,z5,z6])],[(0,[z0,z1,z833,z4,z5,z6]),(0,[z0,z1,z3,z4,z834,z6])],[(0,[z0,z1,z3,z4,z5,z835]),(0,[z159,z1,z3,z128,z5,z6]),(0,[z0,z150,z3,z4,z103,z6]),(0,[z0,z1,z3,z4,z5,z836]),(0,[z1,z3,z4,z5,z837,z6]),(0,[z0,z1,z838,z4,z5,z6]),(1,[z0,z1,z3,z5,z731]),(0,[z0,z1,z3,z4,z728,z122])],[(0,[z0,z1,z3,z126,z5,z182]),(0,[z14,z0,z1,z654,z5,z6]),(0,[z0,z1,z3,z4,z5,z839])],[(0,[z0,z1,z840,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z841]),(0,[z0,z1,z3,z4,z5,z842]),(0,[z0,z1,z3,z4,z16,z90]),(0,[z0,z3,z4,z5,z774,z17]),(0,[z0,z1,z3,z4,z277,z122])],[(0,[z0,z1,z3,z4,z5,z843]),(1,[z1,z3,z765,z5,z6]),(0,[z0,z1,z403,z4,z5,z107]),(0,[z0,z31,z189,z1,z4,z5]),(0,[z0,z247,z3,z4,z103,z6]),(0,[z0,z1,z61,z4,z162,z6])],[(0,[z0,z1,z8,z4,z5,z397]),(0,[z0,z1,z3,z4,z844,z6]),(0,[z0,z1,z3,z10,z5,z731])]],
   [[(0,[z0,z1,z845,z4,z5,z6]),(0,[z0,z2,z3,z4,z57,z6]),(0,[z443,z1,z3,z4,z5,z36])],[(0,[z409,z0,z1,z27,z5,z6]),(0,[z0,z1,z3,z4,z5,z846]),(0,[z0,z1,z412,z4,z5,z107])],[(0,[z0,z1,z3,z392,z365,z6]),(0,[z0,z96,z3,z4,z456,z6]),(0,[z400,z1,z34,z4,z5,z6]),(0,[z0,z237,z3,z261,z5,z6])],[(0,[z25,z732,z3,z4,z5,z6]),(0,[z0,z1,z156,z4,z5,z6]),(0,[z0,z1,z3,z102,z248,z6]),(0,[z0,z847,z1,z3,z5,z6])],[(0,[z0,z137,z403,z4,z5,z6]),(0,[z0,z1,z3,z4,z848,z6])],[(0,[z0,z1,z3,z4,z6,z849]),(0,[z110,z0,z3,z4,z229,z6]),(0,[z312,z1,z3,z4,z5,z36]),(0,[z1,z3,z4,z5,z850,z6]),(0,[z0,z1,z3,z4,z851,z6])],[(0,[z0,z1,z446,z139,z5,z6]),(0,[z0,z1,z3,z852,z5,z6]),(0,[z0,z1,z3,z853,z5,z6]),(0,[z40,z1,z34,z4,z5,z6]),(0,[z0,z1,z388,z15,z5,z6]),(0,[z0,z69,z361,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z854]),(0,[z0,z1,z3,z10,z5,z11])],[(0,[z0,z137,z412,z4,z5,z6]),(0,[z0,z1,z4,z64,z141,z5])]],
   [[(0,[z1,z388,z34,z4,z5,z6]),(0,[z0,z189,z1,z3,z128,z5]),(0,[z0,z1,z3,z178,z5,z195]),(0,[z0,z189,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z721]),(0,[z0,z1,z8,z4,z5,z253])],[(0,[z0,z1,z3,z4,z365,z6]),(0,[z0,z1,z3,z855,z5,z6]),(0,[z1,z3,z4,z5,z726,z6]),(0,[z0,z1,z3,z5,z856,z6])],[(0,[z0,z1,z3,z857,z5,z6]),(0,[z0,z129,z1,z3,z4,z842])],[(0,[z1,z3,z4,z5,z858,z6]),(0,[z0,z1,z3,z4,z60,z510])],[(0,[z0,z31,z1,z15,z5,z6])],[(0,[z0,z1,z3,z4,z5,z859])],[(0,[z0,z1,z3,z860,z5,z6]),(0,[z0,z1,z3,z4,z5,z861]),(0,[z400,z1,z3,z28,z5,z6]),(0,[z0,z237,z3,z261,z444,z6]),(0,[z0,z1,z3,z4,z5,z862])],[(0,[z0,z1,z3,z4,z5,z863]),(0,[z0,z1,z3,z4,z5,z864]),(0,[z0,z1,z3,z865,z5,z6]),(0,[z0,z1,z3,z866,z5,z6]),(0,[z118,z1,z27,z126,z5,z6]),(0,[z0,z1,z3,z867,z5,z6]),(0,[z0,z69,z108,z310,z4,z5]),(0,[z0,z1,z3,z4,z868,z6])]],
   [[(0,[z549,z1,z3,z128,z5,z6]),(0,[z81,z1,z3,z4,z57,z6]),(0,[z869,z1,z3,z4,z5,z6]),(0,[z0,z1,z313,z4,z5,z90])],[(0,[z383,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z870,z5]),(0,[z0,z1,z3,z871,z5,z6]),(0,[z0,z1,z313,z10,z4,z5]),(0,[z0,z1,z3,z4,z872,z6]),(0,[z0,z1,z3,z873,z5,z6])],[(0,[z0,z1,z3,z4,z874,z6])],[(0,[z0,z1,z4,z5,z6,z875]),(0,[z0,z1,z876,z4,z5,z6]),(0,[z0,z1,z877,z4,z5,z6]),(0,[z0,z237,z3,z677,z5,z6]),(0,[z0,z878,z1,z3,z4,z5])],[(0,[z0,z1,z879,z3,z4,z5]),(0,[z14,z0,z1,z634,z5,z6]),(0,[z0,z1,z3,z178,z5,z6]),(0,[z880,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z881]),(0,[z0,z1,z3,z4,z5,z882]),(0,[z0,z1,z8,z4,z5,z721]),(0,[z0,z1,z883,z4,z5,z6])],[(0,[z304,z1,z4,z5,z9,z6]),(0,[z0,z664,z1,z8,z4,z5]),(0,[z0,z346,z1,z5,z77,z171])],[(0,[z0,z1,z3,z392,z5,z6]),(0,[z0,z1,z3,z4,z884,z6]),(0,[z0,z1,z3,z4,z5,z885]),(0,[z0,z1,z886,z3,z4,z5]),(0,[z0,z346,z1,z3,z5,z731])],[(0,[z0,z1,z446,z4,z365,z6]),(0,[z0,z1,z175,z3,z4,z356])]],
   [[(0,[z0,z1,z3,z4,z887,z6]),(0,[z0,z1,z3,z888,z5,z6]),(0,[z400,z1,z3,z128,z5,z6]),(0,[z0,z1,z3,z4,z6,z889]),(0,[z0,z1,z890,z3,z4,z5]),(0,[z91,z1,z3,z4,z82,z6]),(0,[z0,z644,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z891]),(0,[z892,z1,z3,z4,z5,z6])],[(0,[z1,z742,z3,z4,z5,z6]),(0,[z893,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z894,z5])],[(0,[z0,z346,z1,z3,z5,z292]),(0,[z0,z1,z3,z4,z5,z895])],[(0,[z0,z1,z896,z4,z5,z6]),(0,[z0,z1,z3,z4,z897,z6]),(0,[z409,z0,z1,z3,z5,z6]),(0,[z0,z1,z4,z5,z6,z898]),(0,[z0,z1,z3,z4,z708,z6])],[(0,[z0,z1,z899,z4,z5,z6]),(0,[z0,z1,z388,z4,z5,z436]),(0,[z649,z1,z3,z4,z5,z44]),(0,[z900,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z901]),(0,[z383,z1,z3,z4,z89,z6]),(0,[z0,z1,z196,z902,z5,z6])],[(0,[z0,z1,z3,z4,z5,z903]),(0,[z0,z553,z310,z4,z5,z6]),(0,[z0,z1,z3,z4,z16,z195])],[(0,[z0,z1,z381,z4,z5,z436]),(0,[z0,z1,z396,z3,z4,z122]),(0,[z0,z1,z904,z4,z5,z6])]],
   [[(0,[z14,z0,z1,z653,z5,z6]),(0,[z0,z1,z4,z141,z5,z6]),(0,[z0,z1,z3,z4,z5,z324])],[(0,[z383,z1,z3,z4,z456,z6]),(0,[z447,z200,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z905])],[(0,[z0,z1,z27,z4,z5,z115]),(0,[z0,z1,z906,z4,z5,z6]),(0,[z383,z1,z3,z102,z4,z6]),(0,[z400,z1,z3,z4,z5,z818]),(0,[z907,z1,z3,z4,z5,z6])],[(0,[z0,z1,z535,z4,z162,z6])],[(0,[z0,z1,z446,z392,z5,z6]),(0,[z0,z1,z3,z908,z5,z6]),(0,[z0,z1,z3,z4,z5,z909]),(0,[z0,z1,z108,z3,z94,z5]),(0,[z383,z240,z1,z3,z4,z6]),(0,[z0,z3,z4,z111,z801,z6]),(0,[z0,z1,z3,z4,z155,z5]),(0,[z0,z1,z313,z4,z5,z122])],[(0,[z0,z1,z191,z4,z5,z167]),(0,[z0,z1,z3,z4,z5,z436]),(0,[z0,z1,z3,z4,z5,z910]),(0,[z0,z1,z3,z4,z5,z911]),(0,[z110,z0,z3,z4,z801,z6]),(0,[z0,z912,z1,z3,z4,z5]),(0,[z0,z1,z3,z5,z731,z171])],[(0,[z0,z1,z3,z392,z456,z6]),(0,[z14,z1,z34,z128,z5,z6]),(0,[z0,z69,z808,z4,z5,z6])],[(0,[z0,z2,z3,z4,z6,z122]),(0,[z0,z808,z310,z4,z5,z6]),(0,[z0,z1,z3,z768,z5,z6]),(0,[z0,z1,z4,z62,z708,z6])]],
   [[(0,[z0,z1,z913,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z107])],[(0,[z626,z1,z3,z128,z5,z6]),(0,[z0,z1,z3,z102,z426,z6]),(0,[z0,z1,z3,z4,z444,z6]),(0,[z46,z0,z189,z3,z32,z5]),(0,[z0,z1,z914,z4,z5,z6])],[(0,[z0,z1,z3,z4,z915,z6]),(0,[z0,z1,z3,z4,z16,z6]),(0,[z0,z1,z3,z4,z5,z916]),(0,[z0,z1,z917,z3,z4,z5]),(0,[z0,z1,z918,z4,z5,z6])],[(0,[z0,z1,z919,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z920]),(0,[z0,z1,z3,z28,z5,z115])],[(0,[z200,z3,z4,z57,z103,z6]),(0,[z91,z0,z1,z3,z4,z467]),(0,[z0,z1,z374,z3,z4,z122])],[(0,[z0,z1,z3,z4,z456,z6]),(0,[z0,z1,z3,z4,z5,z921]),(0,[z0,z2,z412,z4,z5,z6]),(0,[z922,z0,z1,z3,z4,z6])],[(0,[z26,z1,z34,z4,z5,z6]),(0,[z272,z1,z3,z28,z5,z6]),(0,[z0,z129,z1,z3,z4,z905]),(0,[z0,z1,z3,z4,z923,z6]),(0,[z0,z70,z4,z652,z5,z6]),(0,[z0,z51,z479,z3,z4,z5]),(0,[z0,z1,z902,z24,z5,z6])],[(0,[z924,z0,z1,z3,z5,z6]),(0,[z0,z346,z1,z3,z5,z522]),(0,[z0,z1,z3,z5,z6,z925]),(0,[z383,z1,z926,z4,z5,z6])]],
   [[(0,[z0,z1,z205,z34,z4,z5]),(0,[z0,z1,z183,z196,z5,z6]),(0,[z0,z1,z175,z4,z5,z524]),(0,[z0,z1,z3,z4,z927,z6]),(0,[z0,z1,z3,z4,z5,z928])],[(0,[z0,z1,z3,z4,z5,z929])],[(0,[z0,z1,z930,z4,z5,z6]),(0,[z0,z1,z3,z931,z5,z6]),(0,[z0,z189,z1,z4,z141,z5]),(0,[z0,z1,z3,z4,z5,z932])],[(0,[z622,z1,z34,z4,z5,z6]),(0,[z0,z1,z3,z102,z35,z6]),(0,[z0,z1,z4,z5,z6,z77]),(0,[z0,z933,z1,z3,z4,z5])],[(0,[z0,z1,z934,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z935]),(0,[z0,z51,z3,z4,z60,z17]),(0,[z14,z0,z1,z23,z4,z5])],[(0,[z1,z3,z4,z5,z36,z726]),(0,[z383,z1,z936,z4,z5,z6])],[(1,[z0,z808,z4,z5,z6]),(0,[z0,z1,z4,z937,z5,z6]),(0,[z0,z1,z33,z196,z5,z6])],[]],
   [[(0,[z0,z1,z3,z938,z5,z6]),(0,[z0,z1,z939,z4,z5,z6]),(0,[z0,z1,z940,z4,z5,z6])],[(0,[z1,z3,z4,z5,z101,z6]),(0,[z0,z1,z3,z941,z5,z6]),(0,[z0,z1,z3,z4,z5,z942]),(0,[z91,z1,z3,z35,z82,z6]),(0,[z943,z1,z3,z4,z5,z6]),(0,[z944,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z945,z5,z6]),(0,[z0,z1,z3,z4,z5,z946]),(0,[z0,z514,z117,z4,z5,z6]),(0,[z0,z1,z3,z4,z947,z6])],[(0,[z0,z1,z446,z4,z456,z6]),(0,[z0,z1,z3,z4,z948,z6]),(0,[z0,z1,z3,z4,z801,z6]),(0,[z0,z1,z926,z4,z5,z6]),(0,[z0,z1,z3,z4,z949,z6])],[(0,[z0,z1,z3,z950,z5,z6]),(0,[z0,z1,z951,z4,z5,z6]),(0,[z0,z1,z694,z4,z62,z6]),(1,[z0,z1,z4,z708,z6])],[(0,[z0,z1,z3,z4,z5,z952]),(0,[z0,z1,z953,z3,z4,z6]),(0,[z0,z1,z3,z5,z954,z6]),(0,[z0,z3,z4,z749,z5,z6]),(0,[z0,z51,z3,z4,z5,z560]),(0,[z0,z1,z313,z4,z5,z6]),(0,[z0,z1,z202,z4,z62,z6])],[(0,[z0,z1,z3,z28,z5,z182]),(0,[z0,z1,z3,z35,z5,z6])],[(0,[z0,z1,z3,z4,z89,z90])]],
   [[(0,[z0,z1,z3,z4,z5,z955]),(0,[z0,z1,z3,z956,z5,z6]),(0,[z14,z304,z1,z24,z5,z6])],[(0,[z400,z1,z3,z15,z5,z6]),(0,[z0,z1,z957,z4,z5,z6])],[(0,[z0,z1,z260,z4,z5,z6]),(0,[z0,z3,z749,z32,z5,z6]),(0,[z0,z1,z958,z4,z5,z6]),(0,[z0,z1,z3,z4,z959,z6])],[(0,[z0,z1,z742,z4,z5,z6]),(0,[z0,z1,z3,z960,z5,z6])],[(0,[z56,z96,z191,z4,z5,z6]),(0,[z0,z31,z1,z4,z64,z5])],[(0,[z0,z137,z3,z4,z5,z107]),(0,[z0,z1,z3,z4,z6,z356]),(0,[z0,z1,z3,z4,z5,z961])],[(0,[z411,z1,z27,z4,z5,z6]),(0,[z0,z962,z3,z4,z5,z6]),(0,[z0,z3,z4,z801,z5,z6]),(0,[z0,z1,z3,z4,z111,z245]),(0,[z0,z1,z3,z4,z111,z467])],[(0,[z91,z1,z3,z4,z456,z6]),(0,[z0,z1,z963,z4,z5,z6]),(0,[z232,z1,z3,z128,z5,z6]),(0,[z0,z1,z964,z4,z5,z6]),(0,[z81,z1,z3,z278,z4,z6]),(0,[z0,z1,z3,z4,z64,z5])]],
   [[(0,[z0,z1,z965,z4,z5,z6]),(0,[z319,z1,z34,z4,z5,z6]),(0,[z409,z0,z1,z108,z3,z5]),(0,[z0,z1,z3,z4,z5,z966])],[(0,[z200,z732,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z967]),(0,[z0,z1,z3,z4,z5,z968]),(0,[z0,z1,z8,z4,z5,z598]),(0,[z0,z1,z3,z102,z856,z6])],[(0,[z0,z1,z3,z969,z5,z6]),(0,[z0,z69,z310,z4,z5,z6])],[(0,[z0,z1,z3,z4,z970,z6]),(0,[z110,z0,z3,z4,z111,z510])],[(0,[z0,z1,z3,z4,z259,z122]),(0,[z0,z1,z971,z3,z4,z5]),(0,[z0,z1,z3,z5,z6,z972]),(0,[z0,z1,z3,z4,z973,z6])],[(0,[z284,z1,z27,z4,z5,z6]),(0,[z0,z189,z1,z3,z15,z5]),(0,[z0,z3,z4,z974,z5,z6])],[(0,[z0,z1,z3,z4,z975,z6]),(1,[z1,z3,z4,z5,z726]),(0,[z976,z1,z3,z4,z5,z6])],[(0,[z400,z1,z3,z4,z5,z6]),(0,[z0,z1,z27,z28,z5,z6]),(0,[z91,z1,z3,z4,z82,z195])]],
   [[(1,[z0,z3,z749,z5,z6]),(0,[z0,z1,z4,z708,z162,z6])],[(0,[z0,z1,z3,z4,z977,z6]),(0,[z0,z1,z434,z4,z162,z6])],[(0,[z0,z457,z3,z4,z103,z6]),(0,[z118,z1,z27,z28,z5,z6]),(0,[z0,z113,z3,z4,z103,z6])],[(0,[z0,z1,z3,z4,z5,z978]),(0,[z68,z1,z3,z4,z5,z726]),(0,[z0,z1,z3,z4,z451,z6])],[(0,[z0,z1,z3,z4,z5,z195]),(0,[z0,z1,z979,z4,z5,z6]),(0,[z22,z1,z3,z226,z5,z36]),(0,[z0,z1,z3,z4,z16,z122]),(0,[z0,z31,z237,z1,z5,z6]),(0,[z0,z1,z196,z5,z6,z393])],[(0,[z0,z1,z3,z4,z5,z980]),(0,[z0,z1,z3,z4,z5,z981]),(0,[z0,z1,z3,z4,z5,z982])],[(0,[z0,z1,z3,z139,z5,z167]),(0,[z0,z1,z983,z3,z4,z6]),(0,[z0,z1,z3,z126,z5,z6]),(0,[z0,z984,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z985])],[(0,[z0,z1,z986,z4,z5,z6]),(0,[z0,z1,z388,z4,z5,z6])]],
   [[(0,[z1,z3,z28,z128,z5,z6]),(0,[z272,z1,z388,z15,z5,z6]),(0,[z91,z635,z1,z3,z4,z6]),(0,[z987,z1,z3,z4,z5,z6])],[(0,[z0,z1,z988,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z989]),(0,[z0,z1,z205,z27,z4,z5]),(0,[z0,z1,z3,z990,z5,z6]),(0,[z991,z1,z3,z4,z5,z6])],[(0,[z0,z1,z381,z4,z5,z6]),(0,[z0,z1,z3,z4,z992,z5]),(0,[z0,z69,z310,z4,z59,z6]),(0,[z0,z639,z3,z4,z103,z6]),(0,[z0,z1,z8,z4,z5,z197])],[(0,[z0,z1,z3,z993,z5,z6]),(0,[z0,z1,z3,z994,z5,z6]),(0,[z0,z995,z3,z4,z5,z6]),(0,[z0,z240,z1,z3,z203,z324]),(0,[z0,z1,z3,z4,z5,z996]),(0,[z0,z1,z3,z531,z5,z11])],[(0,[z0,z1,z3,z997,z5,z6]),(0,[z0,z998,z3,z4,z5,z6]),(0,[z144,z1,z3,z4,z5,z44]),(0,[z0,z1,z999,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z245]),(0,[z0,z1,z3,z4,z5,z467]),(0,[z0,z1000,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z6,z1001]),(0,[z0,z1,z3,z1002,z5,z6]),(0,[z0,z31,z1,z4,z5,z6]),(0,[z1003,z1,z3,z4,z5,z6]),(0,[z0,z346,z1,z3,z251,z5]),(0,[z0,z1,z3,z4,z5,z728])],[(0,[z0,z1,z3,z1004,z5,z6]),(0,[z0,z1,z3,z4,z5,z344])],[(0,[z0,z1,z191,z139,z5,z6]),(0,[z14,z0,z1,z155,z24,z5]),(0,[z0,z1,z8,z577,z4,z5]),(0,[z0,z1,z4,z5,z9,z721])]],
   [[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z129,z1,z3,z102,z6]),(0,[z0,z1,z3,z4,z89,z195]),(0,[z0,z1,z1005,z4,z5,z6]),(0,[z383,z1,z3,z4,z5,z1006]),(0,[z0,z1,z3,z1007,z5,z6])],[(0,[z272,z1,z3,z15,z5,z6]),(0,[z0,z1,z3,z4,z5,z1008]),(0,[z0,z701,z3,z261,z5,z6]),(0,[z0,z1,z4,z5,z9,z462]),(0,[z0,z1,z1009,z4,z5,z6]),(0,[z0,z1,z3,z4,z285,z90])],[(0,[z0,z1,z34,z4,z5,z115]),(0,[z0,z1,z3,z178,z5,z107])],[(0,[z0,z1,z3,z4,z1010,z6]),(0,[z0,z1,z33,z148,z5,z6]),(0,[z0,z1,z1011,z4,z5,z6]),(0,[z0,z1,z3,z1012,z5,z6])],[(0,[z0,z1,z403,z178,z5,z6]),(0,[z0,z1,z3,z4,z5,z725]),(0,[z0,z3,z261,z749,z5,z6])],[(0,[z0,z1,z1013,z4,z5,z6]),(0,[z0,z1,z3,z4,z59,z982]),(0,[z0,z1,z354,z3,z4,z728])],[(0,[z0,z1,z1014,z4,z5,z6]),(0,[z91,z1,z3,z4,z82,z107]),(0,[z0,z1,z3,z4,z5,z1015])],[(0,[z0,z1,z3,z1016,z5,z6]),(0,[z0,z1017,z3,z4,z5,z6]),(0,[z1,z27,z742,z4,z5,z6]),(0,[z0,z1,z412,z178,z5,z6]),(0,[z0,z1,z3,z4,z745,z6]),(0,[z0,z1,z1018,z4,z5,z6]),(0,[z0,z1,z1019,z4,z5,z6]),(0,[z0,z1,z4,z5,z708,z6])]],
   [[(0,[z118,z1,z27,z4,z5,z115]),(0,[z0,z137,z3,z178,z5,z6]),(0,[z91,z1,z403,z4,z82,z6]),(0,[z0,z1,z3,z4,z1020,z6]),(0,[z0,z1,z3,z4,z510,z122])],[(0,[z0,z1,z1021,z3,z4,z6]),(0,[z0,z1022,z1,z3,z4,z6]),(0,[z272,z1,z3,z15,z5,z436]),(0,[z0,z1023,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1024,z6]),(0,[z0,z431,z3,z4,z5,z130]),(0,[z0,z1,z3,z4,z89,z728])],[(0,[z0,z1,z1025,z4,z5,z6]),(0,[z0,z51,z3,z4,z65,z17]),(0,[z0,z346,z1,z3,z5,z171]),(0,[z0,z1,z3,z1026,z4,z6])],[(0,[z91,z1,z412,z4,z82,z6]),(0,[z0,z1,z4,z5,z6,z1027]),(0,[z0,z1,z4,z902,z5,z6])],[(0,[z91,z137,z3,z4,z82,z6]),(0,[z0,z1,z3,z10,z5,z476]),(0,[z0,z69,z94,z310,z5,z6]),(0,[z0,z1,z3,z4,z5,z1028])],[(0,[z0,z1,z3,z4,z5,z1029]),(0,[z0,z1,z403,z4,z5,z6]),(0,[z0,z129,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z1030])],[(0,[z0,z1,z446,z4,z5,z6]),(0,[z0,z1031,z1,z3,z4,z5]),(0,[z0,z1,z4,z5,z6,z1032]),(0,[z0,z1,z3,z10,z668,z5])],[(0,[z0,z1,z3,z139,z5,z234]),(0,[z0,z1,z33,z231,z5,z6]),(0,[z0,z1,z8,z3,z4,z356])]],
   [[(0,[z142,z1,z34,z4,z5,z6]),(0,[z0,z1,z3,z4,z59,z6]),(0,[z0,z1,z1033,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1034])],[(0,[z25,z200,z3,z4,z5,z6]),(0,[z0,z1,z1035,z3,z4,z5]),(0,[z0,z1,z301,z4,z5,z9]),(0,[z22,z1,z3,z116,z5,z36]),(0,[z0,z1,z3,z4,z157,z759]),(0,[z0,z1,z23,z3,z4,z5])],[(0,[z0,z1,z4,z1036,z5,z6]),(0,[z0,z129,z1,z3,z35,z6]),(0,[z0,z1,z3,z1037,z5,z6])],[(0,[z0,z1,z3,z4,z1038,z6]),(0,[z0,z1,z205,z3,z4,z5]),(0,[z0,z51,z571,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1039])],[],[(0,[z56,z96,z3,z139,z5,z6]),(0,[z0,z1,z3,z35,z5,z195]),(0,[z81,z1,z3,z4,z6,z300]),(0,[z46,z0,z3,z32,z5,z6]),(0,[z0,z1,z3,z4,z401,z90])],[(0,[z0,z1,z1040,z4,z5,z6]),(0,[z0,z1,z3,z4,z1041,z6]),(0,[z1042,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1043]),(0,[z0,z346,z1,z3,z497,z5]),(0,[z0,z1,z4,z5,z6,z721]),(0,[z0,z1,z1044,z4,z5,z6]),(0,[z0,z1,z606,z3,z4,z122])]],
   [[(0,[z56,z732,z3,z4,z5,z6]),(0,[z0,z270,z3,z4,z103,z6]),(0,[z0,z240,z1,z3,z35,z6]),(0,[z46,z0,z31,z1,z5,z6]),(0,[z0,z1,z33,z902,z5,z6])],[(0,[z0,z1,z3,z4,z1045,z6]),(0,[z0,z1046,z3,z4,z5,z6])],[(0,[z383,z1,z3,z4,z57,z6]),(0,[z0,z1,z3,z4,z5,z1047]),(0,[z0,z3,z4,z801,z103,z6]),(0,[z400,z1,z3,z4,z5,z966])],[(0,[z118,z1,z27,z4,z5,z182])],[(0,[z127,z129,z1,z3,z128,z6]),(0,[z0,z1,z1048,z4,z5,z6]),(0,[z0,z76,z3,z4,z111,z6]),(0,[z0,z1,z202,z4,z62,z245])],[(0,[z0,z1,z3,z4,z1049,z6]),(0,[z0,z1,z1050,z4,z5,z6]),(0,[z1,z3,z4,z765,z5,z6])],[(0,[z56,z96,z3,z4,z5,z167]),(0,[z0,z3,z808,z4,z5,z6]),(0,[z0,z1,z23,z196,z4,z5])],[(0,[z0,z1,z1051,z4,z5,z6]),(0,[z0,z1,z3,z5,z11,z731])]],
   [[(0,[z0,z69,z310,z4,z451,z6])],[(0,[z0,z1,z191,z4,z5,z234]),(0,[z91,z1,z3,z4,z745,z6]),(0,[z0,z1,z808,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1052])],[(0,[z0,z1,z3,z4,z5,z1053]),(0,[z22,z1,z156,z4,z5,z36])],[(0,[z0,z1,z3,z4,z6,z1054]),(0,[z0,z1,z1055,z4,z5,z6]),(0,[z0,z1,z3,z4,z1056,z6]),(0,[z0,z1,z3,z4,z5,z80]),(0,[z1,z3,z15,z765,z5,z6]),(0,[z1057,z1,z3,z4,z5,z6]),(0,[z0,z1058,z3,z4,z5,z6]),(0,[z0,z1,z3,z902,z5,z6])],[(0,[z68,z1,z3,z4,z5,z44]),(0,[z0,z1,z936,z4,z5,z6]),(0,[z0,z1059,z3,z4,z5,z6])],[(0,[z198,z1,z3,z15,z5,z6]),(0,[z0,z1,z3,z4,z1060,z6]),(0,[z0,z1,z3,z4,z1061,z6]),(0,[z0,z1,z3,z4,z5,z1062]),(0,[z14,z0,z1,z902,z5,z6])],[(0,[z0,z1,z1063,z4,z5,z6]),(0,[z0,z1,z202,z4,z708,z6])],[(0,[z0,z1,z175,z3,z4,z65])]],
   [[(0,[z0,z1,z3,z4,z5,z1064]),(0,[z383,z1,z3,z4,z5,z1065]),(0,[z0,z346,z1,z313,z4,z5])],[(0,[z118,z1,z742,z4,z5,z6]),(0,[z400,z1,z388,z4,z5,z6]),(0,[z0,z1,z3,z102,z379,z6]),(0,[z1,z3,z4,z57,z745,z6]),(0,[z0,z1,z3,z1066,z5,z6]),(0,[z0,z1,z1067,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1068,z6])],[(0,[z0,z1,z3,z4,z5,z1069]),(0,[z383,z2,z3,z4,z5,z6]),(0,[z1,z3,z1070,z4,z5,z6]),(0,[z0,z1,z175,z4,z5,z9])],[(0,[z0,z1,z1071,z3,z4,z5]),(0,[z168,z1,z34,z4,z5,z6]),(0,[z0,z386,z3,z4,z103,z6]),(0,[z0,z1,z1072,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z731])],[(0,[z0,z732,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1073,z6]),(0,[z0,z2,z3,z178,z5,z6]),(0,[z0,z1,z403,z35,z5,z6]),(0,[z0,z1,z1074,z4,z5,z6]),(0,[z0,z240,z1,z3,z856,z6])],[(0,[z0,z1,z3,z1075,z5,z6]),(0,[z0,z1,z34,z28,z5,z6]),(0,[z1076,z1,z3,z4,z5,z6])]],
   [[(0,[z214,z1,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1077]),(0,[z0,z1,z3,z4,z103,z245]),(0,[z0,z1,z3,z4,z103,z467]),(0,[z14,z400,z1,z24,z5,z6]),(0,[z0,z1,z3,z4,z1078,z5])],[(0,[z0,z1079,z1,z3,z4,z5]),(0,[z0,z1,z3,z1080,z5,z6]),(0,[z0,z1,z412,z35,z5,z6])],[(0,[z1,z3,z4,z57,z456,z6]),(0,[z1081,z0,z1,z3,z5,z6]),(0,[z91,z2,z3,z4,z82,z6]),(0,[z409,z0,z69,z310,z5,z6]),(0,[z0,z1,z3,z94,z5,z6]),(0,[z0,z1,z354,z3,z4,z122])],[(0,[z0,z1,z3,z4,z1082,z5]),(0,[z0,z1,z1083,z3,z4,z6]),(0,[z530,z1,z3,z4,z5,z44]),(0,[z14,z0,z241,z1,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1084]),(0,[z0,z1,z3,z4,z5,z1065])],[(0,[z0,z1,z3,z1085,z5,z6]),(0,[z0,z1,z1086,z4,z5,z6]),(0,[z0,z1,z3,z765,z5,z6]),(0,[z0,z129,z1,z3,z203,z6]),(0,[z0,z1,z156,z116,z5,z6]),(0,[z22,z1,z3,z4,z5,z726]),(0,[z0,z1,z3,z4,z1087,z6]),(0,[z0,z1,z1088,z3,z4,z5])],[(0,[z0,z1,z3,z4,z1089,z5]),(0,[z200,z2,z3,z4,z5,z6])],[(0,[z56,z96,z3,z4,z5,z234]),(0,[z0,z240,z1,z3,z203,z467])]],
   [[(0,[z0,z1,z3,z4,z5,z1090]),(0,[z0,z1,z3,z4,z1091,z6]),(0,[z0,z1,z3,z13,z5,z11]),(0,[z0,z1,z1092,z3,z4,z5])],[],[(0,[z14,z0,z1,z315,z5,z6]),(0,[z14,z0,z1,z23,z24,z5]),(1,[z0,z1,z3,z856,z6])],[(0,[z0,z1,z3,z4,z1093,z6]),(0,[z0,z1094,z3,z4,z5,z6]),(0,[z0,z1095,z1,z3,z4,z5]),(0,[z0,z1,z3,z749,z5,z6]),(0,[z0,z240,z1,z3,z203,z6])],[(0,[z0,z1,z1096,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1097]),(0,[z81,z0,z1,z3,z4,z467])],[(0,[z118,z1,z388,z4,z5,z6])],[(0,[z272,z1,z381,z15,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1098]),(0,[z0,z237,z3,z261,z157,z6]),(0,[z0,z1,z3,z4,z5,z1099]),(0,[z0,z3,z4,z1100,z5,z6]),(0,[z0,z532,z1,z3,z5,z171])]],
   [[(0,[z0,z1,z3,z4,z5,z1101]),(0,[z0,z1,z3,z4,z5,z1102]),(0,[z1,z3,z4,z5,z6,z1103])],[(0,[z0,z1,z3,z139,z365,z6]),(0,[z0,z1,z3,z4,z5,z1104]),(0,[z26,z1,z742,z4,z5,z6]),(0,[z428,z0,z3,z4,z111,z6]),(0,[z0,z1,z4,z5,z1105,z6]),(0,[z383,z1,z3,z4,z6,z122]),(0,[z0,z1,z3,z1106,z5,z6])],[(0,[z127,z1,z3,z263,z128,z6]),(0,[z0,z1,z3,z4,z5,z726])],[(0,[z0,z1,z3,z4,z5,z1107])],[(0,[z127,z1,z3,z765,z5,z6]),(0,[z0,z1,z403,z4,z5,z195]),(0,[z0,z1,z3,z4,z5,z1108]),(0,[z0,z1,z3,z226,z5,z36]),(0,[z14,z0,z1,z24,z5,z6]),(1,[z0,z1,z902,z5,z6])],[(0,[z0,z1,z3,z4,z1109,z6]),(0,[z0,z1,z1110,z4,z5,z6]),(0,[z0,z1,z3,z4,z1111,z6]),(0,[z0,z1,z3,z4,z856,z6])],[(0,[z1,z3,z4,z57,z521,z6]),(0,[z0,z1112,z1,z3,z5,z6]),(0,[z1113,z1,z3,z4,z5,z6]),(0,[z0,z346,z1,z3,z5,z163])],[(0,[z0,z1,z1114,z4,z5,z6]),(0,[z0,z1,z412,z4,z5,z195]),(0,[z0,z1,z1115,z4,z5,z6]),(0,[z0,z346,z1,z313,z5,z171])]],
   [[(0,[z0,z1,z3,z1116,z5,z6]),(0,[z0,z1,z3,z1117,z5,z6]),(0,[z0,z1118,z1,z4,z5,z6]),(0,[z0,z2,z3,z102,z4,z6]),(0,[z0,z1,z3,z4,z5,z1119]),(0,[z0,z1,z3,z4,z1120,z6]),(0,[z0,z1,z3,z856,z203,z6])],[(0,[z194,z0,z3,z32,z5,z6]),(0,[z22,z1,z3,z4,z16,z36]),(0,[z214,z1,z3,z4,z5,z36]),(0,[z0,z70,z117,z4,z5,z6])],[(0,[z0,z1,z3,z4,z365,z167]),(0,[z247,z3,z4,z101,z103,z6]),(0,[z0,z1,z1121,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z774]),(0,[z0,z3,z4,z5,z774,z6]),(0,[z0,z1,z3,z4,z5,z1122])],[(0,[z0,z1,z4,z1123,z5,z6]),(0,[z0,z1,z3,z1124,z5,z6]),(0,[z0,z1,z3,z4,z1125,z6]),(0,[z0,z1,z3,z128,z5,z436]),(0,[z0,z1126,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1127,z6]),(0,[z383,z200,z3,z4,z5,z6]),(0,[z0,z3,z4,z1128,z5,z6]),(0,[z0,z1,z3,z1129,z5,z6])],[(0,[z0,z1,z3,z188,z856,z6])],[(0,[z0,z1,z3,z4,z5,z107]),(0,[z81,z1,z3,z4,z745,z6]),(0,[z0,z1130,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1131]),(0,[z0,z1,z3,z4,z5,z1132])],[(0,[z0,z1,z3,z4,z5,z115]),(0,[z0,z1,z3,z4,z5,z1133]),(0,[z0,z1,z3,z4,z5,z1134]),(0,[z0,z1,z3,z4,z5,z1006]),(0,[z0,z1135,z3,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 549) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 549).take 545) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1094).take 3) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1097)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [549, 545, 3] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 156).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 156).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [156, 100] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_40503

theorem PEqualNP.Outside.L_meta_40503 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242596000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4242596000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40503.solve
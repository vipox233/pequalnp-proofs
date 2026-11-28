import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38905

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
  Nat.testBit (4276809440 * 2 ^ 32 + 4209682944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0000a21c3010aaad#64 ++ 0x2000144386021555#64 ++ 0xa813e63c7071ffff#64 ++ 0xd5027cc78e0e3fff#64 : BitVec 256),
   (0x10658acd8c566666#64 ++ 0x420cb159b18acccc#64 ++ 0xf0ed9bcf8c5e6667#64 ++ 0xbe1db379f18bcccc#64 : BitVec 256),
   (0x0b0a1c06d59b8787#64 ++ 0x81614380dab370f0#64 ++ 0xdf0e1c0fff9f8787#64 ++ 0x7be1c381fff3f0f0#64 : BitVec 256),
   (0x05b01d600ee00550#64 ++ 0x00b603ac01dc00aa#64 ++ 0xfff01ff00fe007fe#64 ++ 0xfffe03fe01fc00ff#64 : BitVec 256),
   (0x06ff40000b6d5000#64 ++ 0x00dfe800016daa00#64 ++ 0x9fffe0000ffff805#64 ++ 0xf3fffc0001ffff00#64 : BitVec 256),
   (0x27dff7bb60000000#64 ++ 0x04fbfef76c000000#64 ++ 0xe7fffffff0000003#64 ++ 0xfcfffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [10, 3]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0xa813e63c7071ffff 0xd5027cc78e0e3fff

def z1 : W := mkw 0x002000000b6d5000 0x00040000016daa00 0x180000000ffff804 0x0300000001ffff00

def z2 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xfff01ff00fe007fe 0xfffe03fe01fc00ff

def z3 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x9fffe0000ffff805 0xf3fffc0001ffff00

def z4 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf0e1c0fff9f8787 0x7be1c381fff3f0f0

def z5 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z6 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xe7fffffff0000003 0xfcfffffffe000000

def z7 : W := mkw 0x0590152002a00110 0x00b202a400540022 0xaf10063003e007fe 0xd5e200c6007c00ff

def z8 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0x50ec19c38c0e0000 0x2a1d83387181c000

def z9 : W := mkw 0x030a140650108285 0x00614280ca021050 0xcf0e1c0ff0118787 0x79e1c381fe0230f0

def z10 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0ed9bcf8c5e6667 0xbe1db379f18bcccc

def z11 : W := mkw 0x020a400001091000 0x0041480000212200 0x0002600000019800 0x00004c0000003300

def z12 : W := mkw 0x05b0bf7c3ef0affd 0x20b617ef87de15ff 0xfff3fffc7ff1ffff 0xfffe7fff8ffe3fff

def z13 : W := mkw 0x002008441ef0affd 0x2004010883de15ff 0x180000000ff1fffc 0x0300000001fe3fff

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0x8813e0000071f805 0xd1027c00000e3f00

def z15 : W := mkw 0x06ffe21c3b7dfaad 0x20dffc43876fbf55 0xbfffe63c7fffffff 0xf7fffcc78fffffff

def z16 : W := mkw 0x27ff5de34ee00550 0x04ffebbc69dc00aa 0xfffc1ff38fe007fe 0xffff83fe71fc00ff

def z17 : W := mkw 0x0590152000000000 0x00b202a400000000 0xe7f01ff000000002 0xfcfe03fe00000000

def z18 : W := mkw 0x27fffffb6ee00550 0x04ffffff6ddc00aa 0xffffffffffe007ff 0xfffffffffffc00ff

def z19 : W := mkw 0x0065000008444000 0x000ca00001088800 0x90ed80000c5e6005 0xb21db000018bcc00

def z20 : W := mkw 0x10008acd84122666 0x42001159b08244cc 0x60001bcf80000662 0x0c000379f00000cc

def z21 : W := mkw 0x25b0bffb6ee00550 0x04b617ff6ddc00aa 0xfff01fffffe007fe 0xfffe03fffffc00ff

def z22 : W := mkw 0x0000080484120606 0x00000100908240c0 0xd00c180f8c1e0607 0x3a018301f183c0c0

def z23 : W := mkw 0x0045a29920000000 0x0008b45324000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z24 : W := mkw 0x106508c58c566666 0x420ca118b18acccc 0x50ec19c38c5e6664 0x2a1d8338718bcccc

def z25 : W := mkw 0x10458a8d84166626 0x4208b151b082ccc4 0xd00d980f8c1e6607 0x3a01b301f183ccc0

def z26 : W := mkw 0x030a140240000000 0x0061428048000000 0xc70e1c0ff0000003 0x78e1c381fe000000

def z27 : W := mkw 0x102008448c566666 0x42040108918acccc 0x100000000c5e6664 0x02000000018bcccc

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8100630006007fe 0xd50200c6000c00ff

def z29 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x57e019c00f800000 0x2afc033801f00000

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000020000400666 0x94000040000800cc

def z31 : W := mkw 0x04b0a3782a602878 0x2096146f054c050f 0x20f1e3f000607878 0x841e3c7e000c0f0f

def z32 : W := mkw 0x07ff5d600fed5550 0x00ffebac01fdaaaa 0xfffffff00fffffff 0xfffffffe01ffffff

def z33 : W := mkw 0x08000804959b8787 0x8100010092b370f0 0x180000000f9f8784 0x0300000001f3f0f0

def z34 : W := mkw 0x09001c06d4928787 0x81200380da9250f0 0x40001c0ff0000782 0x08000381fe0000f0

def z35 : W := mkw 0x000020143010aaad 0x2000040286021555 0x081264307071fffc 0x41024c860e0e3fff

def z36 : W := mkw 0x3100bfffe4122666 0x462017fffc8244cc 0x60001ffff0000662 0x0c0003fffe0000cc

def z37 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x0003e00c7011f801 0x00007c018e023f00

def z38 : W := mkw 0x0b0a1c06d59bafaf 0xa1614380dab375f5 0xdf0e1c0fffffffff 0x7be1c381ffffffff

def z39 : W := mkw 0x06ff48400f6d5440 0x00dfe90801edaa88 0xfffffbc00ffffe67 0xffffff7801ffffcc

def z40 : W := mkw 0x0490400002201000 0x0092080000440200 0x0010600000201800 0x00020c0000040300

def z41 : W := mkw 0x106582c908446060 0x420cb05921088c0c 0x20e183c000406060 0x841c307800080c0c

def z42 : W := mkw 0x002008400c400440 0x0004010801880088 0xf0e01bc00c400666 0xbe1c0378018800cc

def z43 : W := mkw 0x15f59fed8ef66776 0x42beb3fdb1deccee 0xfffd9fff8ffe67ff 0xffffb3fff1ffccff

def z44 : W := mkw 0x100082c900002060 0x420010592000040c 0x200003c000000060 0x040000780000000c

def z45 : W := mkw 0x069a400003291000 0x00d3480000652200 0x0f12600003a19800 0x41e24c0000743300

def z46 : W := mkw 0x0000000003291000 0x0000000000652200 0x0800000003a19800 0x0100000000743300

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z48 : W := mkw 0x04b0a37c3a70aafd 0x2096146f874e155f 0xa8f3e7fc7071ffff 0xd51e7cff8e0e3fff

def z49 : W := mkw 0x04b000000a600000 0x00960000014c0000 0xbff006300fe007fe 0xf7fe00c601fc00ff

def z50 : W := mkw 0x0b6f1c06dddfc787 0x816de380dbbbf8f0 0xdfef9c0fffdfe787 0xfbfdf381fffbfcf0

def z51 : W := mkw 0x1b6f9ecfdddfe7e7 0xc36df3d9fbbbfcfc 0xffef9fcfffdfe7e7 0xfffdf3f9fffbfcfc

def z52 : W := mkw 0x27df55a340000000 0x04fbeab468000000 0xe7fc1ff380000002 0xfcff83fe70000000

def z53 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x17ec00000f8e0000 0x22fd800001f1c000

def z54 : W := mkw 0x0590152002a00110 0x00b202a400540022 0x0f10043003a00198 0x41e2008600740033

def z55 : W := mkw 0x19659ecfdcd6e7e7 0xc32cb3d9fb9adcfc 0xf0ed9fcffc5e67e7 0xbe1db3f9ff8bccfc

def z56 : W := mkw 0x27fff7bb6b6d5000 0x04fffef76d6daa00 0xfffffffffffff807 0xffffffffffffff00

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0x8013e00000000001 0xd0027c0000000000

def z58 : W := mkw 0x27dff7bf70108285 0x04fbfef7ee021050 0xeffffffff0118787 0xfdfffffffe0230f0

def z59 : W := mkw 0x0b0abe1ef59b8787 0x816157c3deb370f0 0xff1ffe3fff9f8787 0xffe3ffc7fff3f0f0

def z60 : W := mkw 0x024fe21c311dfaad 0x2049fc438623bf55 0xa81fe63c707fffff 0xd503fcc78e0fffff

def z61 : W := mkw 0x069a400003291000 0x00d3480000652200 0x8f13e00003f1f805 0xd1e27c00007e3f00

def z62 : W := mkw 0x020a000001090000 0x0041400000212000 0x000e0000001f8001 0x0001c0000003f000

def z63 : W := mkw 0x0000000410108285 0x0000000082021050 0xa812063c707187ff 0xd50240c78e0e30ff

def z64 : W := mkw 0x07ffff7c3ffdfffd 0x20ffffef87ffbfff 0xfffffffc7fffffff 0xffffffff8fffffff

def z65 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0xf0ec1bc38c4e0666 0xbe1d83787189c0cc

def z66 : W := mkw 0x24d541a100000000 0x049aa83420000000 0x00e001c000000000 0x001c003800000000

def z67 : W := mkw 0x0eff48049fffd787 0x81dfe90093fffaf0 0x9fffe0000fffff85 0xf3fffc0001fffff0

def z68 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x47eff9cff0000001 0x28fdff39fe000000

def z69 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000000071f804 0x01000000000e3f00

def z70 : W := mkw 0x0000820c00102224 0x0000104180020444 0xa001820c00506667 0x94003041800a0ccc

def z71 : W := mkw 0x0590b73c32b0abbd 0x20b216e786561577 0xaf13e63c73f1ffff 0xd5e27cc78e7e3fff

def z72 : W := mkw 0x0b0abe1ef59bafaf 0xa16157c3deb375f5 0xff1ffe3fffffffff 0xffe3ffc7ffffffff

def z73 : W := mkw 0x002008400ee00550 0x0004010801dc00aa 0x180000000fe007fc 0x0300000001fc00ff

def z74 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xeffffffff06007ff 0xfdfffffffe0c00ff

def z75 : W := mkw 0x24d5e3b920000000 0x049abc7724000000 0x20f1e3f000000000 0x841e3c7e00000000

def z76 : W := mkw 0x01001d6004800550 0x002003ac009000aa 0x60001ff0000007fa 0x0c0003fe000000ff

def z77 : W := mkw 0x0a0a0002c10b0002 0x8141400058216000 0x000c0003800e0000 0x000180007001c000

def z78 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xfff3fff00ff1ffff 0xfffe7ffe01fe3fff

def z79 : W := mkw 0x0000000410108285 0x0000000082021050 0x8802040c70118787 0x510040818e0230f0

def z80 : W := mkw 0x0000a21820000000 0x0000144304000000 0xa013e63c70000003 0xd4027cc78e000000

def z81 : W := mkw 0x020a000001090000 0x0041400000212000 0x9f0e00000f9f8005 0x73e1c00001f3f000

def z82 : W := mkw 0x030a140241090000 0x0061428048212000 0xdf0e1c0fff9f8007 0x7be1c381fff3f000

def z83 : W := mkw 0x002000000b6d5000 0x00040000016daa00 0x9813e0000ffff805 0xd3027c0001ffff00

def z84 : W := mkw 0x27dfffbfe4120606 0x04fbfff7fc8240c0 0xf7fffffffc1e0607 0xfeffffffff83c0c0

def z85 : W := mkw 0x0000a21820002828 0x2000144304000505 0x2011e23000607878 0x84023c46000c0f0f

def z86 : W := mkw 0x106508c58c564646 0x420ca118b18ac8c8 0xd0ec19cf8c1e0607 0x3a1d8339f183c0c0

def z87 : W := mkw 0x0b0a1c06c59b0706 0x81614380d8b360e0 0xd70c180f8f9e0607 0x3ae18301f1f3c0c0

def z88 : W := mkw 0x000000041010aaad 0x2000000082021555 0x080000000071fffc 0x01000000000e3fff

def z89 : W := mkw 0x0045828900000000 0x0008b05120000000 0xe0ed9bcf80000003 0xbc1db379f0000000

def z90 : W := mkw 0x1fff9fefdfffe7f7 0xc3fff3fdfbfffcfe 0xffff9fffffffe7ff 0xfffff3fffffffcff

def z91 : W := mkw 0x0b0a1406d11b8287 0x81614280da237050 0xc70e1c0ff01f8003 0x78e1c381fe03f000

def z92 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xdff019c00fe00004 0xfbfe033801fc0000

def z93 : W := mkw 0x10658ac98c464442 0x420cb1593188c888 0xf0ed9bcf8c0e0003 0xbe1db379f181c000

def z94 : W := mkw 0x0fff5c06dfffd787 0x81ffeb80dbfffaf0 0xdffffc0fffffff87 0xfbffff81fffffff0

def z95 : W := mkw 0x0b0a140251898181 0x816142804a313030 0x0f02040073818180 0x41e040800e703030

def z96 : W := mkw 0x106582cd08546264 0x420cb059a10a8c4c 0xa0e183cc00506667 0x941c3079800a0ccc

def z97 : W := mkw 0x1000828d80122226 0x42001051b0024444 0x0000000f80000000 0x00000001f0000000

def z98 : W := mkw 0x0fba1d66dffb87d7 0x81f743acdbff70fa 0xfffe1fffffff87ff 0xffffc3fffffff0ff

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800040000000786 0x51000080000000f0

def z100 : W := mkw 0x0b0a1c02c58b0502 0x8161438058b160a0 0x570c18038f8e0000 0x2ae1830071f1c000

def z101 : W := mkw 0x16ff48c18f6f5442 0x42dfe91831edea88 0xdffff9c38ffff805 0xfbffff3871ffff00

def z102 : W := mkw 0x01001d6004800550 0x002003ac009000aa 0xff001ff00f8007fe 0x7fe003fe01f000ff

def z103 : W := mkw 0x0db01d649ffb87d7 0x81b603ac93ff70fa 0xfff01ff00fff87fe 0xfffe03fe01fff0ff

def z104 : W := mkw 0x0020000008444000 0x0004000001088800 0x100000000c5e6004 0x02000000018bcc00

def z105 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0xa001863c705067ff 0x940030c78e0a0cff

def z106 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf0effbcffc5ffe67 0xbe1dff79ff8bffcc

def z107 : W := mkw 0x0a0a0006d11b8287 0x81414000da237050 0x9f0e000fff9f8005 0x73e1c001fff3f000

def z108 : W := mkw 0x082008049fffd787 0x8104010093fffaf0 0x180000000fffff84 0x0300000001fffff0

def z109 : W := mkw 0x0000080484120606 0x00000100908240c0 0x100000000c1e0604 0x020000000183c0c0

def z110 : W := mkw 0x2fdfffbff59b8787 0x85fbfff7feb370f0 0xffffffffff9f8787 0xfffffffffff3f0f0

def z111 : W := mkw 0x0000000000000000 0x0000000000000000 0x0011e00000607800 0x80023c00000c0f00

def z112 : W := mkw 0x15f5bffdbef6efff 0x62beb7ffb7deddff 0xffffffffffffffff 0xffffffffffffffff

def z113 : W := mkw 0x0000201030008889 0x2000040206001111 0x0812643070219998 0x41024c860e043333

def z114 : W := mkw 0x06ba00000b690000 0x00d74000016d2000 0x9ffe00000fff8005 0xf3ffc00001fff000

def z115 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0xa013e63c7011f803 0xd4027cc78e023f00

def z116 : W := mkw 0x0f9a540253a99181 0x81f34a804a753230 0x0f12640073a19980 0x41e24c800e743330

def z117 : W := mkw 0x0000a21830008889 0x2000144306001111 0xa813e63c7021999b 0xd5027cc78e043333

def z118 : W := mkw 0x37fffffffc56eeef 0x66ffffffff8adddd 0xfffffffffc7fffff 0xffffffffff8fffff

def z119 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x8813e00c7071f805 0xd1027c018e0e3f00

def z120 : W := mkw 0x0b0a1c02c58b0502 0x8161438058b160a0 0xdf0c1c038f8e0786 0x7be1838071f1c0f0

def z121 : W := mkw 0x0000080494128687 0x00000100928250d0 0xd80e1c0ffc1f8787 0x7b01c381ff83f0f0

def z122 : W := mkw 0x002008400c400440 0x0004010801880088 0xf8f01ff00c6007fe 0xff1e03fe018c00ff

def z123 : W := mkw 0x230ab7bb60000000 0x046156f76c000000 0xe70e1ffff0000003 0x7ce1c3fffe000000

def z124 : W := mkw 0x1b6f1cc3cdcf4542 0xc36de39879b9e8a8 0x57ec19c38f8e0000 0x2afd833871f1c000

def z125 : W := mkw 0x106582c908446060 0x420cb05921088c0c 0xe0ed9bcf80406063 0xbc1db379f0080c0c

def z126 : W := mkw 0x1045a29db016eaaf 0x6208b453b602dd55 0x000fe00ff01ff801 0x0001fc01fe03ff00

def z127 : W := mkw 0x102008448f7f7666 0x4204010891efeecc 0x180000000ffffe64 0x0300000001ffffcc

def z128 : W := mkw 0x3165bfffec566666 0x462cb7fffd8acccc 0xf0ed9ffffc5e6667 0xbe1db3ffff8bcccc

def z129 : W := mkw 0x11009fed84922776 0x422013fdb09244ee 0x60001fff800007fa 0x0c0003fff00000ff

def z130 : W := mkw 0x06ff48400fed5550 0x00dfe90801fdaaaa 0x9fffe0000ffffffd 0xf3fffc0001ffffff

def z131 : W := mkw 0x2100b7bb60000000 0x042016f76c000000 0x60001ffff0000002 0x0c0003fffe000000

def z132 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x2812663c70219ffa 0x45024cc78e0433ff

def z133 : W := mkw 0x279af7bb60000000 0x04f35ef76c000000 0x67127ffff0000002 0x4ce24ffffe000000

def z134 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf0ed9ffffc5e67ff 0xbe1db3ffff8bccff

def z135 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x2000063c700007fa 0x040000c78e0000ff

def z136 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0xd0ed99c38c5e6005 0xba1db338718bcc00

def z137 : W := mkw 0x079a552003a91110 0x00f34aa400752222 0x0f12643003a19998 0x41e24c8600743333

def z138 : W := mkw 0x06ff41600b6d5050 0x00dfe82c016daa0a 0xbfffe3f00ffff87d 0xf7fffc7e01ffff0f

def z139 : W := mkw 0x27dff7bb62a00110 0x04fbfef76c540022 0xeffffffff3a0019b 0xfdfffffffe740033

def z140 : W := mkw 0x27dff7bf7010aaad 0x24fbfef7ee021555 0xeffffffff071ffff 0xfdfffffffe0e3fff

def z141 : W := mkw 0x002008400c400440 0x0004010801880088 0x100000000c400664 0x02000000018800cc

def z142 : W := mkw 0x0b0a1c06d4928787 0x81614380da9250f0 0xc70e1c0ff0000783 0x78e1c381fe0000f0

def z143 : W := mkw 0x06ff40000a645000 0x00dfe800014c8a00 0x87ffe00000607801 0xf0fffc00000c0f00

def z144 : W := mkw 0x0100bf7c3490affd 0x202017ef869215ff 0xe813fffc7071ffff 0xdd027fff8e0e3fff

def z145 : W := mkw 0x05d597a900000000 0x00bab2f520000000 0xe7fd9fff80000003 0xfcffb3fff0000000

def z146 : W := mkw 0x01001c0004800500 0x00200380009000a0 0xff101e300fe007fe 0xffe203c601fc00ff

def z147 : W := mkw 0x224fe29b60000000 0x0449fc536c000000 0x000fe00ff0000001 0x0001fc01fe000000

def z148 : W := mkw 0x04f540000a645000 0x009ea800014c8a00 0x00f1e00000607800 0x801e3c00000c0f00

def z149 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xf7e01bc00fc00666 0xbefc037801f800cc

def z150 : W := mkw 0x10658acd8f7f7666 0x420cb159b1efeecc 0xf8ed9bcf8ffffe67 0xbf1db379f1ffffcc

def z151 : W := mkw 0x06ff400008444000 0x00dfe80001088800 0x97ffe0000c5e6005 0xf2fffc00018bcc00

def z152 : W := mkw 0x27ff5de34ee00550 0x04ffebbc69dc00aa 0x57ec19c38f800000 0x2afd833871f00000

def z153 : W := mkw 0x0b0ab61e7199abad 0xa16156c3ce333575 0xaf13e63c73f1ffff 0xd5e27cc78e7e3fff

def z154 : W := mkw 0x05901d2004800500 0x00b203a4009000a0 0xfff01ff00f800786 0xfffe03fe01f000f0

def z155 : W := mkw 0x06df4000032d5000 0x00dbe8000065aa00 0x0f1fe00003bff801 0x41e3fc000077ff00

def z156 : W := mkw 0x0000000000000000 0x0000000000000000 0xa010063000000002 0xd40200c600000000

def z157 : W := mkw 0x0000a21820002828 0x2000144304000505 0xa013e63c7060787b 0xd4027cc78e0c0f0f

def z158 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xff1e1e3fffff87ff 0xffe3c3c7fffff0ff

def z159 : W := mkw 0x0b0a3c16f59b8f8f 0xa1614782deb371f1 0xdf1e7c3fffbf9f9f 0x7be3cf87fff7f3f3

def z160 : W := mkw 0x05b0bf782ee00550 0x00b617ef05dc00aa 0xfff3fffc7fe007ff 0xfffe7fff8ffc00ff

def z161 : W := mkw 0x16ff48c18f6f5442 0x42dfe91831edea88 0x57ec19c38f8e0000 0x2afd833871f1c000

def z162 : W := mkw 0x279a753260000000 0x04f34ea64c000000 0x0712643070000000 0x40e24c860e000000

def z163 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x70ec1bcf8c0e0662 0x2e1d8379f181c0cc

def z164 : W := mkw 0x024f4000010d5000 0x0049e8000021aa00 0x9f0fe0000f9ff805 0x73e1fc0001f3ff00

def z165 : W := mkw 0x0eff4006db7fd287 0x81dfe800db6ffa50 0x9fffe00ffffff805 0xf3fffc01ffffff00

def z166 : W := mkw 0x15f51de18ee64552 0x42bea3bc31dcc8aa 0x57ec19c38f8e0000 0x2afd833871f1c000

def z167 : W := mkw 0x06ff40000a600000 0x00dfe800014c0000 0x9fffe0000fe00005 0xf3fffc0001fc0000

def z168 : W := mkw 0x09001c06d4928787 0x81200380da9250f0 0xc8021c0ff0118787 0x59004381fe0230f0

def z169 : W := mkw 0x27dff7bb70008889 0x24fbfef76e001111 0xeffffffff021999b 0xfdfffffffe043333

def z170 : W := mkw 0x106582cd88566266 0x420cb059b10acc4c 0x20ed83cf805e6061 0x841db079f00bcc0c

def z171 : W := mkw 0x0065a21c3854eaad 0x200cb443870a9d55 0xb8ffe63c7c7fffff 0xf71ffcc78f8fffff

def z172 : W := mkw 0x2590b7bb60000000 0x04b216f76c000000 0xe7f01ffff0000002 0xfcfe03fffe000000

def z173 : W := mkw 0x0000a21820002828 0x2000144304000505 0xa813e2300071f87d 0xd5027c46000e3f0f

def z174 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x0ff3e00003e1f800 0xc1fe7c00007c3f00

def z175 : W := mkw 0x27fffffb6ee00550 0x04ffffff6ddc00aa 0xf7ffffffff800003 0xfefffffffff00000

def z176 : W := mkw 0x0000080004800500 0x00000100009000a0 0x180000000f800784 0x0300000001f000f0

def z177 : W := mkw 0x279a753260000000 0x04f34ea64c000000 0xe7f27ff070000002 0xfcfe4ffe0e000000

def z178 : W := mkw 0x0b0a140651998385 0x81614280ca333070 0x8f02040c73918787 0x51e040818e7230f0

def z179 : W := mkw 0x27df55a340000000 0x04fbeab468000000 0x47ec19c380000000 0x28fd833870000000

def z180 : W := mkw 0x0a4f4006d11fd287 0x8149e800da23fa50 0x000fe00ff01ff801 0x0001fc01fe03ff00

def z181 : W := mkw 0x0fba1d625fe985d1 0x81f743ac4bfd30ba 0xfff21ff07fe187fe 0xfffe43fe0ffc30ff

def z182 : W := mkw 0x0000a21c30108285 0x0000144386021050 0xa813e63c70118787 0xd5027cc78e0230f0

def z183 : W := mkw 0x1045828d80166226 0x4208b051b002cc44 0x000d800f801e6001 0x0001b001f003cc00

def z184 : W := mkw 0x26dfe3b920000000 0x04dbfc7724000000 0xa7ffe3f000000001 0xf4fffc7e00000000

def z185 : W := mkw 0x37ffffffec566666 0x46fffffffd8acccc 0xf7fffffffc5e6667 0xfeffffffff8bcccc

def z186 : W := mkw 0x01001c0004800500 0x00200380009000a0 0x40001c0000000782 0x08000380000000f0

def z187 : W := mkw 0x0590b73c3010aaad 0x20b216e786021555 0xeff3fffc7071ffff 0xfdfe7fff8e0e3fff

def z188 : W := mkw 0x000000041010aaad 0x2000000082021555 0x00000000000007f8 0x00000000000000ff

def z189 : W := mkw 0x2f9a753271898181 0x85f34ea64e313030 0x0f12643073818180 0x41e24c860e703030

def z190 : W := mkw 0x04b000000a600000 0x00960000014c0000 0x9ff3e0000ff1f805 0xf3fe7c0001fe3f00

def z191 : W := mkw 0x08000800858b0502 0x8100010010b160a0 0x100000000f8e0000 0x0200000001f1c000

def z192 : W := mkw 0x279af73e7010aaad 0x24f35ee7ce021555 0xaf13e63c7071ffff 0xd5e27cc78e0e3fff

def z193 : W := mkw 0x0b4f5c06d59fd787 0x8169eb80dab3faf0 0xdf0ffc0fff9fff87 0x7be1ff81fff3fff0

def z194 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf1ffc0fffffff87 0xfbe3ff81fffffff0

def z195 : W := mkw 0x0000080484120606 0x00000100908240c0 0x4000180f80000602 0x08000301f00000c0

def z196 : W := mkw 0x0b2a1c06dfffd787 0x81654380dbfffaf0 0xdf0e1c0fffffff87 0x7be1c381fffffff0

def z197 : W := mkw 0x0ffffe1effffffaf 0xa1ffffc3dffffff5 0xfffffe3fffffffff 0xffffffc7ffffffff

def z198 : W := mkw 0x002000041b7dfaad 0x20040000836fbf55 0x180000000ffffffc 0x0300000001ffffff

def z199 : W := mkw 0x00008a0c84122626 0x00001141908244c4 0xf00d9a0f8c5e6667 0xbe01b341f18bcccc

def z200 : W := mkw 0x10658acd9c56eeef 0x620cb159b38adddd 0xf8ed9bcf8c7fffff 0xbf1db379f18fffff

def z201 : W := mkw 0x10658ac98c466462 0x420cb1593188cc8c 0x70ed9bc38c4e6060 0xae1db3787189cc0c

def z202 : W := mkw 0x04b001600a600050 0x0096002c014c000a 0x20f003f000600078 0x841e007e000c000f

def z203 : W := mkw 0x0a0a0006d11b8287 0x81414000da237050 0x000e000ff01f8001 0x0001c001fe03f000

def z204 : W := mkw 0x0a0a000251098081 0x814140004a213010 0x0002000070018000 0x000040000e003000

def z205 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0xbfffe6300fffffff 0xf7fffcc601ffffff

def z206 : W := mkw 0x024f4000010d5000 0x0049e8000021aa00 0x000fe000001ff801 0x0001fc000003ff00

def z207 : W := mkw 0x0000000002a00110 0x0000000000540022 0x0800000003a00198 0x0100000000740033

def z208 : W := mkw 0x2b4ffe9ff59b8787 0x8569ffd3feb370f0 0xdf0ffc0fff9f8787 0x7be1ff81fff3f0f0

def z209 : W := mkw 0x05b015600a600050 0x00b602ac014c000a 0xe7f01ff00060007a 0xfcfe03fe000c000f

def z210 : W := mkw 0x2f9a7d36f59b8787 0x85f34fa6deb370f0 0xdf1e7c3fff9f8787 0x7be3cf87fff3f0f0

def z211 : W := mkw 0x0000201030008889 0x2000040206001111 0xa812663070619ffe 0xd5024cc60e0c33ff

def z212 : W := mkw 0x14f5c2c90a647060 0x429eb859214c8e0c 0x20f1e3c000607860 0x841e3c78000c0f0c

def z213 : W := mkw 0x2100353260000000 0x042006a64c000000 0x0000043070000000 0x000000860e000000

def z214 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x1f1004300fe007fc 0x43e2008601fc00ff

def z215 : W := mkw 0x06df400000000000 0x00dbe80000000000 0x87ffe00000000001 0xf0fffc0000000000

def z216 : W := mkw 0x0a0a0806d59b8787 0x81414100dab370f0 0x180e000fff9f8785 0x0301c001fff3f0f0

def z217 : W := mkw 0x069a400003291000 0x00d3480000652200 0x9f1e60000fbf9805 0x73e3cc0001f7f300

def z218 : W := mkw 0x00458a8d84120606 0x0008b151b08240c0 0xf0ed9bcf8c1e0607 0xbe1db379f183c0c0

def z219 : W := mkw 0x0000820800002020 0x0000104100000404 0x2001820000406060 0x8400304000080c0c

def z220 : W := mkw 0x10658ac90c446460 0x420cb15921888c8c 0xf0e19bc00c406666 0xbe1c337801880ccc

def z221 : W := mkw 0x1000000480166226 0x420000009002cc44 0x00000000001e6000 0x000000000003cc00

def z222 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x570c1c0fff8e0782 0x2ae18381fff1c0f0

def z223 : W := mkw 0x0000a21c20102224 0x0000144384020444 0xa013e63c70506667 0xd4027cc78e0a0ccc

def z224 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x50ed99cf8c1e6001 0x2a1db339f183cc00

def z225 : W := mkw 0x0000000400100204 0x0000000080020040 0x8000000c00100607 0x10000001800200c0

def z226 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x1ffe60000faf9800 0x63ffcc0001f5f300

def z227 : W := mkw 0x000000041010aaad 0x2000000082021555 0x8813e0000071fffd 0xd1027c00000e3fff

def z228 : W := mkw 0x1065aaddac566666 0x420cb55bb58acccc 0xf0fffffffc5e6667 0xfe1fffffff8bcccc

def z229 : W := mkw 0x17ffdfed8fff7776 0x42fffbfdb1ffeeee 0xffffffff8fffffff 0xfffffffff1ffffff

def z230 : W := mkw 0x0590152000000000 0x00b202a400000000 0x0710043000000000 0x40e2008600000000

def z231 : W := mkw 0x1020aa5cbc56eeef 0x6204154b978adddd 0xb813e63c7c7fffff 0xd7027cc78f8fffff

def z232 : W := mkw 0x37ffdfefcc566666 0x46fffbfdf98acccc 0xf7ed9bcf8c5e6667 0xbefdb379f18bcccc

def z233 : W := mkw 0x06ba40000b691000 0x00d74800016d2200 0x9ff260000fe19804 0xf3fe4c0001fc3300

def z234 : W := mkw 0x1065a2d928446868 0x620cb45b25088d0d 0x20f1e3f000607878 0x841e3c7e000c0f0f

def z235 : W := mkw 0x0065000008444000 0x000ca00001088800 0x10ec00000c0e0000 0x221d80000181c000

def z236 : W := mkw 0x0b0a1c0255898581 0x816143804ab130b0 0xdf021c007f818786 0x7be043800ff030f0

def z237 : W := mkw 0x0490012000000000 0x0092002400000000 0x20f003f000000000 0x841e007e00000000

def z238 : W := mkw 0x01001c0484920706 0x00200380909240e0 0xdf0c1c0f8f9e0787 0x7be18381f1f3c0f0

def z239 : W := mkw 0x27dff7bb63291000 0x04fbfef76c652200 0xeffffffff3a19803 0xfdfffffffe743300

def z240 : W := mkw 0x030a140240000000 0x0061428048000000 0x0702040070000000 0x40e040800e000000

def z241 : W := mkw 0x0045a29d3010aaad 0x2008b453a6021555 0xe8fffffff071ffff 0xfd1ffffffe0e3fff

def z242 : W := mkw 0x0065000008444000 0x000ca00001088800 0x98ffe0000c7ff805 0xf31ffc00018fff00

def z243 : W := mkw 0x01001c0004800500 0x00200380009000a0 0xdf001c000f800786 0x7be0038001f000f0

def z244 : W := mkw 0x0000a21820002828 0x2000144304000505 0xa811e63000607ffe 0xd5023cc6000c0fff

def z245 : W := mkw 0x1000084484122666 0x42000108908244cc 0x0000000000000660 0x00000000000000cc

def z246 : W := mkw 0x05b01d648ef20756 0x00b603ac91de40ea 0xfffc1fff8ffe07ff 0xffff83fff1ffc0ff

def z247 : W := mkw 0x1b2a1c46dddfe7e7 0xc3654388dbbbfcfc 0xdf0e1c0fffdfe7e7 0x7be1c381fffbfcfc

def z248 : W := mkw 0x15f51de18ee64552 0x42bea3bc31dcc8aa 0xfffc1ff38fee07fe 0xffff83fe71fdc0ff

def z249 : W := mkw 0x0000201020000808 0x2000040204000101 0x0010603000201818 0x00020c0600040303

def z250 : W := mkw 0x00208a4c0c502664 0x00041149818a04cc 0xf0e19bcc0c506667 0xbe1c3379818a0ccc

def z251 : W := mkw 0x01001c0004800500 0x00200380009000a0 0x570018000f800000 0x2ae0030001f00000

def z252 : W := mkw 0x210015a340000000 0x042002b468000000 0x400019c380000000 0x0800033870000000

def z253 : W := mkw 0x0b2a1c46dffb87d7 0x81654388dbff70fa 0xdf0e1c0fffff87ff 0x7be1c381fffff0ff

def z254 : W := mkw 0x04f540000a645000 0x009ea800014c8a00 0x90fde0000c7e7805 0xb21fbc00018fcf00

def z255 : W := mkw 0x24f5e3b92a645000 0x049ebc77254c8a00 0x20f1e3f000607800 0x841e3c7e000c0f00

def z256 : W := mkw 0x05b015600ae00150 0x00b602ac015c002a 0x2ff007f003e001f8 0xc5fe00fe007c003f

def z257 : W := mkw 0x27dff7bb60002828 0x24fbfef76c000505 0xe7fffffff060787b 0xfcfffffffe0c0f0f

def z258 : W := mkw 0x10208a4c8c566666 0x42041149918acccc 0xb001820c0c5e6667 0x96003041818bcccc

def z259 : W := mkw 0x27fffffb6fed5550 0x04ffffff6dfdaaaa 0xffffffffffffffff 0xffffffffffffffff

def z260 : W := mkw 0x0045828900000000 0x0008b05120000000 0x000d800f80000001 0x0001b001f0000000

def z261 : W := mkw 0x030ab61e7010aaad 0x206156c3ce021555 0xef1ffe3ff071ffff 0xfde3ffc7fe0e3fff

def z262 : W := mkw 0x05b09f6c0ef02774 0x00b613ed81de04ee 0xfff19ffc0ff067ff 0xfffe33ff81fe0cff

def z263 : W := mkw 0x27ff55a34b6d5000 0x04ffeab4696daa00 0xdffff9c38ffff805 0xfbffff3871ffff00

def z264 : W := mkw 0x0fba1c06dffb8787 0x81f74380dbff70f0 0xdffe1c0fffff8787 0xfbffc381fffff0f0

def z265 : W := mkw 0x27dff7bb61090000 0x04fbfef76c212000 0xffffffffff9f8007 0xfffffffffff3f000

def z266 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x30e183c00c5e6664 0x861c3078018bcccc

def z267 : W := mkw 0x04b000000a600000 0x00960000014c0000 0x9ff000000fe00004 0xf3fe000001fc0000

def z268 : W := mkw 0x07df540240000000 0x00fbea8048000000 0xc7fffc0ff0000003 0xf8ffff81fe000000

def z269 : W := mkw 0x0590353032a08999 0x20b206a606541133 0x0f12643073a19998 0x41e24c860e743333

def z270 : W := mkw 0x06ffe21c3b7dfaad 0x20dffc43876fbf55 0x9fffe00c7ffff805 0xf3fffc018fffff00

def z271 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x97ed80000fde6005 0xb2fdb00001fbcc00

def z272 : W := mkw 0x0065828908444000 0x000cb05121088800 0xf0ed9bcf8c5e6007 0xbe1db379f18bcc00

def z273 : W := mkw 0x06dfc28900000000 0x00dbf85120000000 0xe7fffbcf80000003 0xfcffff79f0000000

def z274 : W := mkw 0x0800aa1cb59bafaf 0xa100154396b375f5 0xb813e63c7fffffff 0xd7027cc78fffffff

def z275 : W := mkw 0x24d5e3bd3010aaad 0x249abc77a6021555 0xa8f3e7fc7071ffff 0xd51e7cff8e0e3fff

def z276 : W := mkw 0x0b0a1c02c58b0502 0x8161438058b160a0 0xd70e1c0fff8e0003 0x7ae1c381fff1c000

def z277 : W := mkw 0x04f540000a645000 0x009ea800014c8a00 0x88f3e0000071f805 0xd11e7c00000e3f00

def z278 : W := mkw 0x0000201030008889 0x2000040206001111 0x0002600070019800 0x00004c000e003300

def z279 : W := mkw 0x002000000b6d5000 0x00040000016daa00 0x100000000f8e0000 0x0200000001f1c000

def z280 : W := mkw 0x1b6fbedffddfefef 0xe36df7dbffbbfdfd 0xffffffffffffffff 0xffffffffffffffff

def z281 : W := mkw 0x020a000000000000 0x0041400000000000 0x870e000000000001 0x70e1c00000000000

def z282 : W := mkw 0x05b015200ae00110 0x00b602a4015c0022 0x9ff004300fe0019c 0xf3fe008601fc0033

def z283 : W := mkw 0x27dff7bf7010aaad 0x24fbfef7ee021555 0xe7fffffff011f803 0xfcfffffffe023f00

def z284 : W := mkw 0x102008408c464442 0x420401081188c888 0x100000000c0e0000 0x020000000181c000

def z285 : W := mkw 0x2fdfffbff59bafaf 0xa5fbfff7feb375f5 0xffffffffffffffff 0xffffffffffffffff

def z286 : W := mkw 0x0100140240000000 0x0020028048000000 0x40001c0ff0000002 0x08000381fe000000

def z287 : W := mkw 0x182008449ddfe7e7 0xc304010893bbfcfc 0x180000000fdfe7e4 0x0300000001fbfcfc

def z288 : W := mkw 0x0000a21820000000 0x0000144304000000 0x0003e00c70000001 0x00007c018e000000

def z289 : W := mkw 0x1fffdecfdffff7e7 0xc3fffbd9fbfffefc 0xffffffcfffffffe7 0xfffffff9fffffffc

def z290 : W := mkw 0x102008448c566666 0x42040108918acccc 0xd00c180f8c5e6667 0x3a018301f18bcccc

def z291 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x570e180fff9f8001 0x2ae1c301fff3f000

def z292 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x0000000c70000000 0x000000018e000000

def z293 : W := mkw 0x27fff7bf7b7dfaad 0x24fffef7ef6fbf55 0xffffffffffffffff 0xffffffffffffffff

def z294 : W := mkw 0x082008449ffb87d7 0x8104010893ff70fa 0x180000000fff87fc 0x0300000001fff0ff

def z295 : W := mkw 0x00000000010d5000 0x000000000021aa00 0x00000000001ff800 0x000000000003ff00

def z296 : W := mkw 0x0800000011898181 0x8100000002313030 0x0800000003818180 0x0100000000703030

def z297 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x5ff01df00fa00198 0x6bfe03be01f40033

def z298 : W := mkw 0x04d5400000000000 0x009aa80000000000 0x00f1e00000000000 0x801e3c0000000000

def z299 : W := mkw 0x0900be1ef492afaf 0xa12017c3de9255f5 0x60001e3ff00007fa 0x0c0003c7fe0000ff

def z300 : W := mkw 0x1000aaddb412aeef 0x6200155bb68255dd 0x60001ffff00007fa 0x0c0003fffe0000ff

def z301 : W := mkw 0x0045008100000000 0x0008a01020000000 0x40ec19c380000000 0x281d833870000000

def z302 : W := mkw 0x1045a29db016eaaf 0x6208b453b602dd55 0xa81fe63ff07fffff 0xd503fcc7fe0fffff

def z303 : W := mkw 0x01201c400cc00540 0x00240388019800a8 0xffe01fc00fc007e6 0xfffc03f801f800fc

def z304 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x77e01ff00f8007fa 0x2efc03fe01f000ff

def z305 : W := mkw 0x0b0a1d66d59b87d7 0x816143acdab370fa 0xff0e1fffff9f87ff 0x7fe1c3fffff3f0ff

def z306 : W := mkw 0x000000041010aaad 0x2000000082021555 0xa81006300071fffe 0xd50200c6000e3fff

def z307 : W := mkw 0x06ff40041b7dfaad 0x20dfe800836fbf55 0x9fffe0000ffffffd 0xf3fffc0001ffffff

def z308 : W := mkw 0x2fdf5da7d59b8787 0x85fbebb4fab370f0 0xdfee1dcfff9f8787 0x7bfdc3b9fff3f0f0

def z309 : W := mkw 0x25d5f7bb60000000 0x04babef76c000000 0x60f1fffff0000002 0x8c1e3ffffe000000

def z310 : W := mkw 0x0fba1d66dffb87d7 0x81f743acdbff70fa 0xdfee1dcfff9f8787 0x7bfdc3b9fff3f0f0

def z311 : W := mkw 0x04b001600a600050 0x0096002c014c000a 0xa8f007f0006007fe 0xd51e00fe000c00ff

def z312 : W := mkw 0x279af73a60000000 0x04f35ee74c000000 0xa713e63c70000003 0xd4e27cc78e000000

def z313 : W := mkw 0x0000820c00102224 0x0000104180020444 0xa811863c007067ff 0xd50230c7800e0cff

def z314 : W := mkw 0x0b4f9e8fd59b8787 0x8169f3d1fab370f0 0xffef9fcfff9f8787 0xfffdf3f9fff3f0f0

def z315 : W := mkw 0x05b01d641ef087d5 0x00b603ac83de10fa 0xfff21ffc7ff187ff 0xfffe43ff8ffe30ff

def z316 : W := mkw 0x11659ecd8cd66766 0x422cb3d9b19accec 0xffed9fcf8fde67e7 0xfffdb3f9f1fbccfc

def z317 : W := mkw 0x16ffc28d8b7f7226 0x42dff851b16fee44 0x9fffe00f8ffff805 0xf3fffc01f1ffff00

def z318 : W := mkw 0x0f9a1d26d59b8787 0x81f343a4dab370f0 0xfffe1fffff9f8787 0xffffc3fffff3f0f0

def z319 : W := mkw 0x16ffeaddbf7ffeef 0x62dffd5bb7efffdd 0xffffffffffffffff 0xffffffffffffffff

def z320 : W := mkw 0x0000080004000400 0x0000010000800080 0xd00018000c000606 0x3a000300018000c0

def z321 : W := mkw 0x10658acd8ef66776 0x420cb159b1deccee 0xf8ed9bcf8ffe67ff 0xbf1db379f1ffccff

def z322 : W := mkw 0x1045828d80166226 0x4208b051b002cc44 0xe0ed9bcf801e6003 0xbc1db379f003cc00

def z323 : W := mkw 0x022a00000b6d5000 0x00454000016daa00 0x9f0e00000ffff805 0x73e1c00001ffff00

def z324 : W := mkw 0x0100bf7c3490affd 0x202017ef869215ff 0x60001ffc700007fa 0x0c0003ff8e0000ff

def z325 : W := mkw 0x16ffcacd8f7f7666 0x42dff959b1efeecc 0xfffffbcf8ffffe67 0xffffff79f1ffffcc

def z326 : W := mkw 0x01201c400ee00550 0x0024038801dc00aa 0xdf001c000fe007fe 0x7be0038001fc00ff

def z327 : W := mkw 0x002008400ee00550 0x0004010801dc00aa 0x100000000f800000 0x0200000001f00000

def z328 : W := mkw 0x10658acd9c56e6e7 0x420cb159b38adcdc 0xf8ef9fcffc5fe7e7 0xff1df3f9ff8bfcfc

def z329 : W := mkw 0x020a000001090000 0x0041400000212000 0x9f1fe0000ffff805 0xf3e3fc0001ffff00

def z330 : W := mkw 0x15b01d648ef66776 0x42b603ac91deccee 0xfff01ff00ffe67fe 0xfffe03fe01ffccff

def z331 : W := mkw 0x1045828d80166226 0x4208b051b002cc44 0xa00d820f805e6667 0x9401b041f00bcccc

def z332 : W := mkw 0x0590152002a00110 0x00b202a400540022 0x0700000003800000 0x00e0000000700000

def z333 : W := mkw 0x002008400ee00550 0x0004010801dc00aa 0xf8e01bc00fe007fe 0xbf1c037801fc00ff

def z334 : W := mkw 0x0065820c08546224 0x000cb041810a8c44 0xb0ed820c0c5e6667 0xb61db041818bcccc

def z335 : W := mkw 0x05b0bf7c3ef0affd 0x20b617ef87de15ff 0xfff01ffc7fe007fe 0xfffe03ff8ffc00ff

def z336 : W := mkw 0x27df75b360000000 0x04fbeeb66c000000 0x47fe7df3f0000000 0x68ffcfbe7e000000

def z337 : W := mkw 0x04f540000b6d5000 0x009ea800016daa00 0x18f1e0000ffff804 0x831e3c0001ffff00

def z338 : W := mkw 0x0000a21820002828 0x2000144304000505 0x2000023000000078 0x040000460000000f

def z339 : W := mkw 0x09001c06d4928787 0x81200380da9250f0 0xd00c1c0ffc1e0787 0x3a018381ff83c0f0

def z340 : W := mkw 0x3ffffffffddfe7e7 0xc7ffffffffbbfcfc 0xffffffffffdfe7e7 0xfffffffffffbfcfc

def z341 : W := mkw 0x102008448ef66776 0x4204010891deccee 0x180000000ffe67fc 0x0300000001ffccff

def z342 : W := mkw 0x0000000410108285 0x0000000082021050 0x0002000c70118001 0x000040018e023000

def z343 : W := mkw 0x079a152240000000 0x00f342a448000000 0xe7fe1ffff0000003 0xfcffc3fffe000000

def z344 : W := mkw 0x05901d6006a00550 0x00b203ac00d400aa 0x6f101ff003a007fa 0x4de203fe007400ff

def z345 : W := mkw 0x16ffcacd8c566666 0x42dff959b18acccc 0xf7fffbcf8c5e6667 0xfeffff79f18bcccc

def z346 : W := mkw 0x0b0a1c02c58b0502 0x8161438058b160a0 0xdf0e18038f9f8005 0x7be1c30071f3f000

def z347 : W := mkw 0x102008449c56eeef 0x62040108938adddd 0x180000000c7ffffc 0x03000000018fffff

def z348 : W := mkw 0x37fff7fb68446060 0x46fffeff6d088c0c 0xe7fffffff0406063 0xfcfffffffe080c0c

def z349 : W := mkw 0x07ff54024b6d5000 0x00ffea80496daa00 0xdffffc0ffffff807 0xfbffff81ffffff00

def z350 : W := mkw 0x2fdf5da3c58b0502 0x85fbebb478b160a0 0x57ec19c38f8e0000 0x2afd833871f1c000

def z351 : W := mkw 0x1045008180064002 0x4208a0103000c800 0x000c0003800e0000 0x000180007001c000

def z352 : W := mkw 0x224fe29f7010aaad 0x2449fc53ee021555 0x000fe00ff011f801 0x0001fc01fe023f00

def z353 : W := mkw 0x0045400000045000 0x0008a80000008a00 0x0001e00000007800 0x00003c0000000f00

def z354 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0e01bc000000002 0xbc1c037800000000

def z355 : W := mkw 0x2fdff7bb71898181 0x85fbfef76e313030 0xeffffffff3818183 0xfdfffffffe703030

def z356 : W := mkw 0x27ff55a34b6d5000 0x04ffeab4696daa00 0x57ec19c38f8e0000 0x2afd833871f1c000

def z357 : W := mkw 0x0000000000000000 0x0000000000000000 0x8810000000600004 0xd1020000000c0000

def z358 : W := mkw 0x224fe29b60000000 0x0449fc536c000000 0xe0effbcff0000003 0xbc1dff79fe000000

def z359 : W := mkw 0x05b01c000ee00500 0x00b6038001dc00a0 0xdff01c000fe00786 0xfbfe038001fc00f0

def z360 : W := mkw 0x136f9ecfcc566666 0x426df3d9f98acccc 0xf7ef9fcffc5e6667 0xfefdf3f9ff8bcccc

def z361 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x1f0204007f9f8784 0x43e040800ff3f0f0

def z362 : W := mkw 0x020a000001090000 0x0041400000212000 0x0f02000003818000 0x41e0400000703000

def z363 : W := mkw 0x0000a2183000a8a9 0x2000144306001515 0x2813e6307061f9f8 0xc5027cc60e0c3f3f

def z364 : W := mkw 0x04b000000a600000 0x00960000014c0000 0x17e000000f800000 0x22fc000001f00000

def z365 : W := mkw 0x0000000010008889 0x2000000002001111 0x0800000000219998 0x0100000000043333

def z366 : W := mkw 0x26dfe29b60000000 0x04dbfc536c000000 0x87ffe00ff0000001 0xf0fffc01fe000000

def z367 : W := mkw 0x27dff7bb610d5000 0x04fbfef76c21aa00 0xe7fffffff01ff803 0xfcfffffffe03ff00

def z368 : W := mkw 0x2fffffbfffffd787 0x85fffff7fffffaf0 0xffffffffffffff87 0xfffffffffffffff0

def z369 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x4f021c0ff3818782 0x49e04381fe7030f0

def z370 : W := mkw 0x09001c06d59b8787 0x81200380dab370f0 0x58001c0fff9f8786 0x0b000381fff3f0f0

def z371 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x67ec1ffff0000002 0x2cfd83fffe000000

def z372 : W := mkw 0x06ffe2182b6d7828 0x20dffc43056daf05 0xbfffe2300ffff87d 0xf7fffc4601ffff0f

def z373 : W := mkw 0x26dfe3bb60000000 0x04dbfc776c000000 0x20ffe3fff0000001 0x841ffc7ffe000000

def z374 : W := mkw 0x0a0aa21ef11baaaf 0xa1415443de237555 0xa81fe63ff07fffff 0xd503fcc7fe0fffff

def z375 : W := mkw 0x0000201430108a8d 0x2000040286021151 0x8812643c70319f9f 0x51024c878e0633f3

def z376 : W := mkw 0x18658acd9ddfe7e7 0xc30cb159b3bbfcfc 0xf8ed9bcf8fdfe7e7 0xbf1db379f1fbfcfc

def z377 : W := mkw 0x2fdfffbbe58b0502 0x85fbfff77cb160a0 0xf7ffffffff8e0003 0xfefffffffff1c000

def z378 : W := mkw 0x0000080084020402 0x0000010010804080 0x500c18038c0e0000 0x2a0183007181c000

def z379 : W := mkw 0x1065828d88566226 0x420cb051b10acc44 0x90ed800f8c5e6005 0xb21db001f18bcc00

def z380 : W := mkw 0x06ff48048f7f5606 0x00dfe90091efeac0 0xdffff80f8ffffe07 0xfbffff01f1ffffc0

def z381 : W := mkw 0x05901d2006a00510 0x00b203a400d400a2 0xdf101c300fa0079e 0x7be2038601f400f3

def z382 : W := mkw 0x0000820c00102224 0x0000104180020444 0x0001800c00106001 0x0000300180020c00

def z383 : W := mkw 0x024fe21c311dfaad 0x2049fc438623bf55 0x000fe00c701ff801 0x0001fc018e03ff00

def z384 : W := mkw 0x0490000002200000 0x0092000000440000 0x0f10000003a00000 0x41e2000000740000

def z385 : W := mkw 0x0db01d66def287d7 0x81b603acdbde50fa 0xfff01fffffe007fe 0xfffe03fffffc00ff

def z386 : W := mkw 0x01201d600cc00550 0x002403ac019800aa 0xf0e01ff00c4007fe 0xbe1c03fe018800ff

def z387 : W := mkw 0x27fff7bb6b6d5000 0x04fffef76d6daa00 0xf7ffffffff8e0003 0xfefffffffff1c000

def z388 : W := mkw 0x0fba1d62cfeb0552 0x81f743ac59fd60aa 0x57ec19c38f8e0000 0x2afd833871f1c000

def z389 : W := mkw 0x0020004008400040 0x0004000801080008 0x20e003c000400060 0x841c00780008000c

def z390 : W := mkw 0x27fff7bb6a645000 0x04fffef76d4c8a00 0xe7fffffff0607803 0xfcfffffffe0c0f00

def z391 : W := mkw 0x01001d6004800550 0x002003ac009000aa 0xe8101ff0006007fe 0xdd0203fe000c00ff

def z392 : W := mkw 0x24d5e3b920000000 0x049abc7724000000 0xa0f3e7fc70000003 0xd41e7cff8e000000

def z393 : W := mkw 0x002008400fed5550 0x0004010801fdaaaa 0x180000000ffffffc 0x0300000001ffffff

def z394 : W := mkw 0x0045000000044000 0x0008a00000008800 0x000d8000001e6001 0x0001b0000003cc00

def z395 : W := mkw 0x069ae21c3339baad 0x20d35c4386673755 0xaf13e63c73f1ffff 0xd5e27cc78e7e3fff

def z396 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x67fdfbf380000000 0xacffbf7e70000000

def z397 : W := mkw 0x06df400000000000 0x00dbe80000000000 0x07ec000000000000 0x20fd800000000000

def z398 : W := mkw 0x006508048c564606 0x000ca100918ac8c0 0xd0ed980f8c5e6607 0xba1db301f18bccc0

def z399 : W := mkw 0x19009ecfd492a7e7 0xc32013d9fa9254fc 0x60001fcff00007e2 0x0c0003f9fe0000fc

def z400 : W := mkw 0x14f5cacd8e767666 0x429eb959b1cececc 0xf0fdfbcf8c7e7e67 0xbe1fbf79f18fcfcc

def z401 : W := mkw 0x0000a21820000000 0x0000144304000000 0xa813e63c7071f807 0xd5027cc78e0e3f00

def z402 : W := mkw 0x08000804959b8787 0x8100010092b370f0 0x9802040c7f9f8787 0x530040818ff3f0f0

def z403 : W := mkw 0x2ffffffffffb87d7 0x85ffffffffff70fa 0xffffffffffff87ff 0xfffffffffffff0ff

def z404 : W := mkw 0x002000400a600050 0x00040008014c000a 0x0000000000600078 0x00000000000c000f

def z405 : W := mkw 0x37ffffffeef66776 0x46fffffffddeccee 0xfffffffffffe67ff 0xffffffffffffccff

def z406 : W := mkw 0x0b0a140251898181 0x816142804a313030 0xcf0e1c0ff3818183 0x79e1c381fe703030

def z407 : W := mkw 0x0000000000002828 0x2000000000000505 0x0000000000607878 0x00000000000c0f0f

def z408 : W := mkw 0x1b6f9ecfcddf6766 0xc36df3d9f9bbecec 0xf7ed9bcf8fde6667 0xbefdb379f1fbcccc

def z409 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x1fec00000ffff804 0x23fd800001ffff00

def z410 : W := mkw 0x0020000008400000 0x0004000001080000 0x90e000000c400004 0xb21c000001880000

def z411 : W := mkw 0x25d5f7b920000000 0x04babef724000000 0xe7f1fff000000002 0xfcfe3ffe00000000

def z412 : W := mkw 0x15b09fed8ef22776 0x42b613fdb1de44ee 0xfff01fff8fe007fe 0xfffe03fff1fc00ff

def z413 : W := mkw 0x0fff5d66dfffd7d7 0x81ffebacdbfffafa 0xffffffffffffffff 0xffffffffffffffff

def z414 : W := mkw 0x05b015200a600000 0x00b602a4014c0000 0xfff01ff00fe00006 0xfffe03fe01fc0000

def z415 : W := mkw 0x0000000410108285 0x0000000082021050 0x0000040c70000782 0x000000818e0000f0

def z416 : W := mkw 0x106500c108444040 0x420ca01821088808 0x00e001c000000000 0x001c003800000000

def z417 : W := mkw 0x1b4f9e8fd59fe7a7 0xc369f3d1fab3fcf4 0xdf0f9c0fff9fe787 0x7be1f381fff3fcf0

def z418 : W := mkw 0x27fff7fb6a600050 0x04fffeff6d4c000a 0xe7fffffff060007b 0xfcfffffffe0c000f

def z419 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x60f01ff0006007fa 0x8c1e03fe000c00ff

def z420 : W := mkw 0x0590152002a00110 0x00b202a400540022 0xeff01ff003a0019a 0xfdfe03fe00740033

def z421 : W := mkw 0x279a753263291000 0x04f34ea64c652200 0x0f12643073a19800 0x41e24c860e743300

def z422 : W := mkw 0x0a0aa21ef11baaaf 0xa1415443de237555 0x000fe00ff01ff801 0x0001fc01fe03ff00

def z423 : W := mkw 0x1065aaddac566e6e 0x620cb55bb58acdcd 0xf0fdfbff8c7e7e7f 0xbe1fbf7ff18fcfcf

def z424 : W := mkw 0x1a6f8acfdd5fe6e7 0xc34df159fbabfcdc 0xf0ef9bcffc5fe667 0xbe1df379ff8bfccc

def z425 : W := mkw 0x37ff5de3cc464442 0x46ffebbc7988c888 0x57ec19c38c0e0000 0x2afd83387181c000

def z426 : W := mkw 0x002008400c400440 0x0004010801880088 0x50e019c00c000000 0x2a1c033801800000

def z427 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x2003e63c7011fffb 0x04007cc78e023fff

def z428 : W := mkw 0x1000aaddb412aeef 0x6200155bb68255dd 0xe813fffff071ffff 0xdd027ffffe0e3fff

def z429 : W := mkw 0x27ff75326b6d5000 0x04ffeea64d6daa00 0x9fffe4307ffff805 0xf3fffc860fffff00

def z430 : W := mkw 0x0000000410108285 0x0000000082021050 0x0800000000118784 0x01000000000230f0

def z431 : W := mkw 0x0590152000000000 0x00b202a400000000 0xeff01ff0006007fe 0xfdfe03fe000c00ff

def z432 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x0803e00c7071fffd 0x01007c018e0e3fff

def z433 : W := mkw 0x2100b7bf7010aaad 0x242016f7ee021555 0xe813fffff071ffff 0xdd027ffffe0e3fff

def z434 : W := mkw 0x026f4000094d5000 0x004de8000129aa00 0x90efe0000c5ff805 0xb21dfc00018bff00

def z435 : W := mkw 0x07df552000000000 0x00fbeaa400000000 0xe7fffff000000003 0xfcfffffe00000000

def z436 : W := mkw 0x27fff7bb68444000 0x04fffef76d088800 0xf7fffffffc5e6007 0xfeffffffff8bcc00

def z437 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xeffffffff071f807 0xfdfffffffe0e3f00

def z438 : W := mkw 0x2000a3b920000000 0x0400147724000000 0x200003f000000000 0x0400007e00000000

def z439 : W := mkw 0x224f408340000000 0x0449e81068000000 0x000c000380000000 0x0001800070000000

def z440 : W := mkw 0x024f4000010d5000 0x0049e8000021aa00 0x881fe000007ff805 0xd103fc00000fff00

def z441 : W := mkw 0x224fe29b610d5000 0x0449fc536c21aa00 0x000fe00ff01ff801 0x0001fc01fe03ff00

def z442 : W := mkw 0x37fffffbec464442 0x46ffffff7d88c888 0xf7fffffffc0e0003 0xfeffffffff81c000

def z443 : W := mkw 0x04b000000a600000 0x00960000014c0000 0x00f0000000600000 0x801e0000000c0000

def z444 : W := mkw 0x0000000410108285 0x0000000082021050 0x8813e40c7071ff87 0xd1027c818e0e3ff0

def z445 : W := mkw 0x15f59fed8ef66776 0x42beb3fdb1deccee 0xf7ed9bcf8fde6667 0xbefdb379f1fbcccc

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001800000506005 0x90003000000a0c00

def z447 : W := mkw 0x04f540000a645000 0x009ea800014c8a00 0x00e0000000000000 0x001c000000000000

def z448 : W := mkw 0x0fba1d62cfeb0552 0x81f743ac59fd60aa 0xfffc1ff38fee07fe 0xffff83fe71fdc0ff

def z449 : W := mkw 0x069a400000000000 0x00d3480000000000 0x0712600000000000 0x40e24c0000000000

def z450 : W := mkw 0x030a1c06c4120606 0x00614380d88240c0 0xd70e1c0ffc1e0607 0x7ae1c381ff83c0c0

def z451 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x17efe0000f9ff801 0x22fdfc0001f3ff00

def z452 : W := mkw 0x01001c0414908785 0x00200380829210f0 0xdf021c0c7f918787 0x7be043818ff230f0

def z453 : W := mkw 0x0fdf5c06d59b8787 0x81fbeb80dab370f0 0xdffffc0fff9f8787 0xfbffff81fff3f0f0

def z454 : W := mkw 0x10008acd84122666 0x42001159b08244cc 0xe0019bcf80506667 0x9c003379f00a0ccc

def z455 : W := mkw 0x0b0a341271898989 0xa16146824e313131 0x0f12643073a19998 0x41e24c860e743333

def z456 : W := mkw 0x0490012002200010 0x0092002400440002 0x0010003000200018 0x0002000600040003

def z457 : W := mkw 0x0590b73820000000 0x00b216e704000000 0xe7f3fffc70000003 0xfcfe7fff8e000000

def z458 : W := mkw 0x06ffc20c0b7d7224 0x00dff841816fae44 0xbfffe20c0ffffe67 0xf7fffc4181ffffcc

def z459 : W := mkw 0x234ff69b60000000 0x0469fed36c000000 0xc70ffc0ff0000003 0x78e1ff81fe000000

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000630000007fa 0x040000c6000000ff

def z461 : W := mkw 0x234ff7bb60000000 0x0469fef76c000000 0x600ffffff0000003 0x0c01fffffe000000

def z462 : W := mkw 0x24f5e3f92a600050 0x049ebc7f254c000a 0x20f1e3f000600078 0x841e3c7e000c000f

def z463 : W := mkw 0x06ba40000b6d5000 0x00d74800016daa00 0x1f1260000ffff804 0x43e24c0001ffff00

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000000006007fc 0x01000000000c00ff

def z465 : W := mkw 0x0000000400102224 0x0000000080020444 0x0000000000506664 0x00000000000a0ccc

def z466 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0xa802063c701187ff 0x550040c78e0230ff

def z467 : W := mkw 0x34f5e3f928446060 0x469ebc7f25088c0c 0x20f1e3f000406060 0x841e3c7e00080c0c

def z468 : W := mkw 0x069a400003291000 0x00d3480000652200 0x0700000003800000 0x00e0000000700000

def z469 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x071fe43ff0000001 0x40e3fc87fe000000

def z470 : W := mkw 0x0000000000000000 0x0000000000000000 0x0812600000219800 0x41024c0000043300

def z471 : W := mkw 0x05b0bf782ee02d78 0x20b617ef05dc05af 0xfff1fff00fe07ffe 0xfffe3ffe01fc0fff

def z472 : W := mkw 0x2a4fe29ff11b8287 0x8549fc53fe237050 0x000fe00ff01f8001 0x0001fc01fe03f000

def z473 : W := mkw 0x27df55a340000000 0x04fbeab468000000 0xc7ee1dcff0000003 0x78fdc3b9fe000000

def z474 : W := mkw 0x0f9a152253a98191 0x81f342a44a753032 0x0f12043073a18198 0x41e240860e743033

def z475 : W := mkw 0x0045828900000000 0x0008b05120000000 0x20e183c000000000 0x841c307800000000

def z476 : W := mkw 0x100008c184020442 0x4200011830804088 0x400019c380000000 0x0800033870000000

def z477 : W := mkw 0x0045000000000000 0x0008a00000000000 0x80ed800000000001 0xb01db00000000000

def z478 : W := mkw 0x34f5ebfdac566666 0x469ebd7fb58acccc 0xf0fdfbff8c5e6667 0xbe1fbf7ff18bcccc

def z479 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf8fd9fff8c7e67ff 0xff1fb3fff18fccff

def z480 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x17fde0000fee7800 0xa2ffbc0001fdcf00

def z481 : W := mkw 0x0000000000000000 0x0000000000000000 0xa813e6300071ffff 0xd5027cc6000e3fff

def z482 : W := mkw 0x1b6f1cc7dddfc7c7 0xc36de398fbbbf8f8 0xdfee1dcfff9f8787 0x7bfdc3b9fff3f0f0

def z483 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0xa013e63c700007fb 0xd4027cc78e0000ff

def z484 : W := mkw 0x27fff7bb6a600000 0x04fffef76d4c0000 0xffffffffffe00007 0xfffffffffffc0000

def z485 : W := mkw 0x37ffffffef7f7666 0x46fffffffdefeecc 0xfffffffffffffe67 0xffffffffffffffcc

def z486 : W := mkw 0x0000a21820002828 0x2000144304000505 0x0001e00000007800 0x00003c0000000f00

def z487 : W := mkw 0x06dfe21820000000 0x00dbfc4304000000 0xa7ffe63c70000003 0xf4fffcc78e000000

def z488 : W := mkw 0x08000804959bafaf 0xa100010092b375f5 0x180000000ffffffc 0x0300000001ffffff

def z489 : W := mkw 0x002000000a645000 0x00040000014c8a00 0x0000000000607800 0x00000000000c0f00

def z490 : W := mkw 0x0a0a0006d11b8287 0x81414000da237050 0x880e040ff01f8787 0x5101c081fe03f0f0

def z491 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x2800063c7071fffe 0x050000c78e0e3fff

def z492 : W := mkw 0x27df753260000000 0x04fbeea64c000000 0x87ffe43070000001 0xf0fffc860e000000

def z493 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x5fe019c00fe007fc 0x2bfc033801fc00ff

def z494 : W := mkw 0x14f58acd8e766666 0x429eb159b1cecccc 0xfffd9bcf8ffe6667 0xffffb379f1ffcccc

def z495 : W := mkw 0x09001c02c4820502 0x81200380589040a0 0x4000180380000000 0x0800030070000000

def z496 : W := mkw 0x07ff5d600fed5550 0x00ffebac01fdaaaa 0xfffc1ff00fee07fe 0xffff83fe01fdc0ff

def z497 : W := mkw 0x15f59fe90ee46570 0x42beb3fd21dc8cae 0xfff19ff00fe067fe 0xfffe33fe01fc0cff

def z498 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x9ffc00000fee0004 0xf3ff800001fdc000

def z499 : W := mkw 0x07ff5c000fed5500 0x00ffeb8001fdaaa0 0xdffffc000fffff87 0xfbffff8001fffff0

def z500 : W := mkw 0x04b008400ee00550 0x0096010801dc00aa 0x9ff000000fe007fc 0xf3fe000001fc00ff

def z501 : W := mkw 0x006500000b6d5000 0x000ca000016daa00 0x98ed80000ffff805 0xb31db00001ffff00

def z502 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xdfe01dc00f800786 0x7bfc03b801f000f0

def z503 : W := mkw 0x05b03d703ee08dd9 0x20b607ae07dc11bb 0xfff27ff07fe19ffe 0xfffe4ffe0ffc33ff

def z504 : W := mkw 0x27dffffb64800550 0x04fbffff6c9000aa 0xe7fffffff00007fb 0xfcfffffffe0000ff

def z505 : W := mkw 0x07ff55200b6d5000 0x00ffeaa4016daa00 0xfffffff00ffff807 0xfffffffe01ffff00

def z506 : W := mkw 0x10008acd84122666 0x42001159b08244cc 0xf00c1bcf8c1e0667 0x3e018379f183c0cc

def z507 : W := mkw 0x0590152000000000 0x00b202a400000000 0x47e019c000000000 0x28fc033800000000

def z508 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x0813e43c7031f999 0x41027c878e063f33

def z509 : W := mkw 0x106582c908446060 0x420cb05921088c0c 0xb0ed83c00c5e6065 0xb61db078018bcc0c

def z510 : W := mkw 0x26ffe3b92b6d5000 0x04dffc77256daa00 0xbfffe3f00ffff805 0xf7fffc7e01ffff00

def z511 : W := mkw 0x030ab61a60000000 0x006156c34c000000 0xe71ffe3ff0000003 0xfce3ffc7fe000000

def z512 : W := mkw 0x06ff60103b6dd889 0x20dfec02076dbb11 0x9fffe4307ffff99d 0xf3fffc860fffff33

def z513 : W := mkw 0x10208acd8c522666 0x42041159b18a44cc 0xf0e01bcf8c400666 0xbe1c0379f18800cc

def z514 : W := mkw 0x279a552240000000 0x04f34aa448000000 0x0700000000000000 0x00e0000000000000

def z515 : W := mkw 0x0100140000000000 0x0020028000000000 0xc7001c0000000002 0x78e0038000000000

def z516 : W := mkw 0x020a000001090000 0x0041400000212000 0x170c00000f8e0000 0x22e1800001f1c000

def z517 : W := mkw 0x0000084004800550 0x00000108009000aa 0x00000000000007f8 0x00000000000000ff

def z518 : W := mkw 0x0a0a0806d51b8687 0x81414100daa370d0 0xd00e180ffc1f8607 0x3a01c301ff83f0c0

def z519 : W := mkw 0x2100bffb64800550 0x042017ff6c9000aa 0x60001ffff00007fa 0x0c0003fffe0000ff

def z520 : W := mkw 0x0fff5c02cfef5502 0x81ffeb8059fdeaa0 0x57ec18038f8e0000 0x2afd830071f1c000

def z521 : W := mkw 0x2145b7bb60000000 0x0428b6f76c000000 0xe0ed9ffff0000003 0xbc1db3fffe000000

def z522 : W := mkw 0x0b2a1c46dddb87c7 0x81654388dbbb70f8 0xffee1fcfffdf87e7 0xfffdc3f9fffbf0fc

def z523 : W := mkw 0x10458acd84122666 0x4208b159b08244cc 0xe0ed9bcf80000663 0xbc1db379f00000cc

def z524 : W := mkw 0x0000820c1010a2a5 0x0000104182021454 0xa803860c7051e7e7 0xd50070c18e0a3cfc

def z525 : W := mkw 0x220a601260000000 0x04414c024c000000 0x0002600070000000 0x00004c000e000000

def z526 : W := mkw 0x0020aa5c3ef0affd 0x2004154b87de15ff 0xb813e63c7ff1ffff 0xd7027cc78ffe3fff

def z527 : W := mkw 0x05f51d600ee44550 0x00bea3ac01dc88aa 0xfffd9ff00ffe67ff 0xffffb3fe01ffccff

def z528 : W := mkw 0x020a000411198285 0x0041400082233050 0x9f0e040c7f9f8787 0x73e1c0818ff3f0f0

def z529 : W := mkw 0x0000016000000050 0x0000002c0000000a 0x200003f000000078 0x0400007e0000000f

def z530 : W := mkw 0x0000a21c20102a2c 0x2000144384020545 0xa011e23c00707e7f 0x94023c47800e0fcf

def z531 : W := mkw 0x27df55a340000000 0x04fbeab468000000 0xc7fff9c380000001 0xf8ffff3870000000

def z532 : W := mkw 0x2100b7bb60000000 0x042016f76c000000 0xe013fffff0000003 0xdc027ffffe000000

def z533 : W := mkw 0x1045828900046020 0x4208b05120008c04 0x0001800000006000 0x0000300000000c00

def z534 : W := mkw 0x026f0000094d4000 0x004de0000129a800 0x9fef80000fdfe005 0xf3fdf00001fbfc00

def z535 : W := mkw 0x27dff7bf7010aaad 0x24fbfef7ee021555 0xe7fffffff00007fb 0xfcfffffffe0000ff

def z536 : W := mkw 0x0000000480120206 0x0000000090024040 0x000c000f801e0001 0x00018001f003c000

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x0003e0000011f801 0x00007c0000023f00

def z538 : W := mkw 0x0000a21820000000 0x0000144304000000 0x2000063c70000002 0x040000c78e000000

def z539 : W := mkw 0x04f500000a644000 0x009ea000014c8800 0x9ffd80000ffe6005 0xf3ffb00001ffcc00

def z540 : W := mkw 0x000000041010aaad 0x2000000082021555 0x000000000011f800 0x0000000000023f00

def z541 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf8fffbcf8c7ffe67 0xff1fff79f18fffcc

def z542 : W := mkw 0x0fff5c02cfef5502 0x81ffeb8059fdeaa0 0xdffff8038ffff805 0xfbffff0071ffff00

def z543 : W := mkw 0x0000201030008889 0x2000040206001111 0x0000043070000198 0x000000860e000033

def z544 : W := mkw 0x04b001600a600050 0x0096002c014c000a 0xbff003f00fe0007c 0xf7fe007e01fc000f

def z545 : W := mkw 0x11659fed8cd66776 0x422cb3fdb19accee 0xf0ed9fff8c5e67ff 0xbe1db3fff18bccff

def z546 : W := mkw 0x002008448c520646 0x00040108918a40c8 0xf0ec1bcf8c5e0667 0xbe1d8379f18bc0cc

def z547 : W := mkw 0x0100140000800100 0x0020028000100020 0x0f00040003800180 0x41e0008000700030

def z548 : W := mkw 0x01201d600ee00550 0x002403ac01dc00aa 0x78001ff00fe007fe 0x0f0003fe01fc00ff

def z549 : W := mkw 0x0f9a5c06d7bb9787 0x81f34b80daf772f0 0xdf1e7c0fffbf9f87 0x7be3cf81fff7f3f0

def z550 : W := mkw 0x1020004008446060 0x4204000801088c0c 0x0000000000406060 0x0000000000080c0c

def z551 : W := mkw 0x0b0abe1ef59bafaf 0xa16157c3deb375f5 0xdf0ffc0fff9fff87 0x7be1ff81fff3fff0

def z552 : W := mkw 0x27dfd7ab40000000 0x04fbfaf568000000 0xe7ed9bcf80000003 0xbcfdb379f0000000

def z553 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x5f0c18038f9f8784 0x2be1830071f3f0f0

def z554 : W := mkw 0x04b0a21c3a70aaad 0x20961443874e1555 0xbff3e63c7ff1ffff 0xf7fe7cc78ffe3fff

def z555 : W := mkw 0x0fff54025bedd181 0x81ffea804b7dba30 0x9fffe4007ffff985 0xf3fffc800fffff30

def z556 : W := mkw 0x0b0a1c02d58b8583 0x816143805ab170b0 0x5f0e1c03ff8f8180 0x6be1c3807ff1f030

def z557 : W := mkw 0x0000000000000000 0x0000000000000000 0x8002040c70000003 0x500040818e000000

def z558 : W := mkw 0x024f400000000000 0x0049e80000000000 0x000fe00000000001 0x0001fc0000000000

def z559 : W := mkw 0x0b0a140251898181 0x816142804a313030 0x9f0e04007f9f8185 0x73e1c0800ff3f030

def z560 : W := mkw 0x0045828d00102224 0x0008b051a0020444 0xe0ed9bcf80506667 0xbc1db379f00a0ccc

def z561 : W := mkw 0x10208acd8c566666 0x42041159b18acccc 0x70001bcf8c5e6666 0x0e000379f18bcccc

def z562 : W := mkw 0x0000201030008889 0x2000040206001111 0x8813e4307071f99d 0xd1027c860e0e3f33

def z563 : W := mkw 0x05b01d600fed5550 0x00b603ac01fdaaaa 0xfff01ff00ffffffe 0xfffe03fe01ffffff

def z564 : W := mkw 0x1065a2dd3854eaed 0x620cb45ba70a9d5d 0xa8f3e7fc7071ffff 0xd51e7cff8e0e3fff

def z565 : W := mkw 0x04b001600a600050 0x0096002c014c000a 0x00e001c000000000 0x001c003800000000

def z566 : W := mkw 0x10458acd84166666 0x4208b159b082cccc 0x600d9bcf801e6663 0x0c01b379f003cccc

def z567 : W := mkw 0x002000000a600000 0x00040000014c0000 0x180000000fe00004 0x0300000001fc0000

def z568 : W := mkw 0x27fffffb6c400440 0x04ffffff6d880088 0xf7fffffffc400667 0xfeffffffff8800cc

def z569 : W := mkw 0x0000a21820000000 0x0000144304000000 0x2011e23000000000 0x84023c4600000000

def z570 : W := mkw 0x27dfffbb64800500 0x04fbfff76c9000a0 0xffffffffff800787 0xfffffffffff000f0

def z571 : W := mkw 0x08000006d0128287 0x81000000da025050 0x0000000ff0000000 0x00000001fe000000

def z572 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x60e19bcf80406662 0x8c1c3379f0080ccc

def z573 : W := mkw 0x024f4000010d5000 0x0049e8000021aa00 0x000c0000000e0000 0x000180000001c000

def z574 : W := mkw 0x06ff40041b7dd285 0x00dfe800836fba50 0x9fffe40c7fffff87 0xf3fffc818ffffff0

def z575 : W := mkw 0x05b01d641ef0affd 0x20b603ac83de15ff 0xfff01ff00ff1fffe 0xfffe03fe01fe3fff

def z576 : W := mkw 0x0a0a0804959b8787 0x8141410092b370f0 0x9f0e00000f9f8785 0x73e1c00001f3f0f0

def z577 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x400e1c0ff01f8783 0x0801c381fe03f0f0

def z578 : W := mkw 0x0b0a140241890100 0x8161428048312020 0x0700000003800000 0x00e0000000700000

def z579 : W := mkw 0x2000a29b60000000 0x040014536c000000 0x0000000ff0000000 0x00000001fe000000

def z580 : W := mkw 0x224fe29f7010aaad 0x2449fc53ee021555 0xa81fe63ff071ffff 0xd503fcc7fe0e3fff

def z581 : W := mkw 0x08000804959b8787 0x8100010092b370f0 0xd80c180f8f9f8787 0x3b018301f1f3f0f0

def z582 : W := mkw 0x034f968b40000000 0x0069f2d168000000 0xe7ef9fcff0000003 0xfcfdf3f9fe000000

def z583 : W := mkw 0x09001d66d49287d7 0x812003acda9250fa 0x60001ffff00007fa 0x0c0003fffe0000ff

def z584 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x8803e40c7011ff87 0x51007c818e023ff0

def z585 : W := mkw 0x0000828900000000 0x0000105120000000 0x60001bcf80000002 0x0c000379f0000000

def z586 : W := mkw 0x16ff48448f7f7666 0x42dfe90891efeecc 0x9fffe0000ffffe65 0xf3fffc0001ffffcc

def z587 : W := mkw 0x026f40000b6d5000 0x004de800016daa00 0x180fe0000ffff805 0x0301fc0001ffff00

def z588 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x97ffe0000f8e0001 0xf2fffc0001f1c000

def z589 : W := mkw 0x102008448c566666 0x42040108918acccc 0xf0e01bc00c5e6666 0xbe1c0378018bcccc

def z590 : W := mkw 0x2fdfffbff4928787 0x85fbfff7fe9250f0 0xe7fffffff0000783 0xfcfffffffe0000f0

def z591 : W := mkw 0x2b0abfbff59b8787 0x856157f7feb370f0 0xff0e1fffff9f8787 0x7fe1c3fffff3f0f0

def z592 : W := mkw 0x279a753260000000 0x04f34ea64c000000 0xc71e7c3ff0000003 0x78e3cf87fe000000

def z593 : W := mkw 0x0020aa5c3c50aeed 0x2004154b878a15dd 0xf8f3fffc7c71ffff 0xff1e7fff8f8e3fff

def z594 : W := mkw 0x27ffffff7ef0affd 0x24ffffffefde15ff 0xfffffffffff1ffff 0xfffffffffffe3fff

def z595 : W := mkw 0x16ffcacd8f7f7666 0x42dff959b1efeecc 0xf7ed9bcf8fde6667 0xbefdb379f1fbcccc

def z596 : W := mkw 0x0000084004000440 0x0000010800800088 0x60001bc000000662 0x0c000378000000cc

def z597 : W := mkw 0x09001c06d4928787 0x81200380da9250f0 0xdf001c0fff800786 0x7be00381fff000f0

def z598 : W := mkw 0x07ba1d624ee00550 0x00f743ac49dc00aa 0xfffe1fffffe007ff 0xffffc3fffffc00ff

def z599 : W := mkw 0x0b0abe1ef59bafaf 0xa16157c3deb375f5 0xff0e1e3fff9f87ff 0x7fe1c3c7fff3f0ff

def z600 : W := mkw 0x24d5e3b920002828 0x249abc7724000505 0x20f1e3f000607878 0x841e3c7e000c0f0f

def z601 : W := mkw 0x05f55d600ee45550 0x00beabac01dc8aaa 0xfff1fff00fe07ffe 0xfffe3ffe01fc0fff

def z602 : W := mkw 0x04b008400e600440 0x0096010801cc0088 0xfff01bc00fe00666 0xfffe037801fc00cc

def z603 : W := mkw 0x04f5e2182a647828 0x209ebc43054c8f05 0x20f1e23000607878 0x841e3c46000c0f0f

def z604 : W := mkw 0x0100152000800110 0x002002a400100022 0x0000043000000198 0x0000008600000033

def z605 : W := mkw 0x126f8acd8d5f6666 0x424df159b1abeccc 0xffef9bcf8fdfe667 0xfffdf379f1fbfccc

def z606 : W := mkw 0x0fff5c06dfffd787 0x81ffeb80dbfffaf0 0xdfee1c0fff9f8787 0x7bfdc381fff3f0f0

def z607 : W := mkw 0x0100be1c3490afad 0x202017c3869215f5 0xff13fe3c7ff1ffff 0xffe27fc78ffe3fff

def z608 : W := mkw 0x06df4000010d5000 0x00dbe8000021aa00 0x87ffe000001ff801 0xf0fffc000003ff00

def z609 : W := mkw 0x069a601033299889 0x20d34c0206653311 0x0f12643073a19998 0x41e24c860e743333

def z610 : W := mkw 0x006508400c444440 0x000ca10801888888 0xf0ed9bc00c5e6667 0xbe1db378018bcccc

def z611 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x00ffe000007ff801 0x801ffc00000fff00

def z612 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x100d800f8c5e6665 0x0201b001f18bcccc

def z613 : W := mkw 0x279a753270008889 0x24f34ea64e001111 0x0f12643070219998 0x41e24c860e043333

def z614 : W := mkw 0x04f5e21c3a74faad 0x209ebc43874e9f55 0xa8f3e63c7071ffff 0xd51e7cc78e0e3fff

def z615 : W := mkw 0x324fe29fe0166226 0x4649fc53fc02cc44 0x000fe00ff01e6001 0x0001fc01fe03cc00

def z616 : W := mkw 0x0000820c1010aaad 0x2000104182021555 0xa801820c0071ffff 0x95003041800e3fff

def z617 : W := mkw 0x0000201020000000 0x0000040204000000 0x0012643070000000 0x40024c860e000000

def z618 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x2013e23c7071f879 0x84027c478e0e3f0f

def z619 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x77f01bf00fe00078 0xaefe037e01fc000f

def z620 : W := mkw 0x0b0a9e0ed59ba7a7 0x816153c1dab374f4 0xff0f9e0fffdfe7e7 0xffe1f3c1fffbfcfc

def z621 : W := mkw 0x1a4f828fd11fe2a7 0xc349f051fa23fc54 0x000f800ff01fe001 0x0001f001fe03fc00

def z622 : W := mkw 0x0000000000000000 0x0000000000000000 0x900c00000c1e0005 0x320180000183c000

def z623 : W := mkw 0x06df400003291000 0x00dbe80000652200 0x8fffe00003a19801 0xf1fffc0000743300

def z624 : W := mkw 0x07ba5d600fe91550 0x00f74bac01fd22aa 0xfff27ff00fe19ffe 0xfffe4ffe01fc33ff

def z625 : W := mkw 0x2900bfbff4928787 0x852017f7fe9250f0 0x60001ffff0000782 0x0c0003fffe0000f0

def z626 : W := mkw 0x01001d6004800550 0x002003ac009000aa 0x400019c000000000 0x0800033800000000

def z627 : W := mkw 0x06ffe2182b6d5000 0x00dffc43056daa00 0xbfffe63c7ffff807 0xf7fffcc78fffff00

def z628 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xf7f01ff00f800002 0xfefe03fe01f00000

def z629 : W := mkw 0x06df400001090000 0x00dbe80000212000 0x9fffe0000f9f8005 0xf3fffc0001f3f000

def z630 : W := mkw 0x07ff5d600fed5550 0x00ffebac01fdaaaa 0xdffff9c00ffff805 0xfbffff3801ffff00

def z631 : W := mkw 0x0020a21c3b7dfaad 0x20041443876fbf55 0xb813e63c7fffffff 0xd7027cc78fffffff

def z632 : W := mkw 0x0000000000000000 0x0000000000000000 0x9f0000000f800004 0x73e0000001f00000

def z633 : W := mkw 0x030a1c0244800500 0x00614380489000a0 0xdf0e1c0fff800787 0x7be1c381fff000f0

def z634 : W := mkw 0x05b01d600c400440 0x00b603ac01880088 0xf7f01ff00c400666 0xfefe03fe018800cc

def z635 : W := mkw 0x106508448c566666 0x420ca108918acccc 0x90ed80000c5e6665 0xb21db000018bcccc

def z636 : W := mkw 0x05901d6004800550 0x00b203ac009000aa 0xe7f01ff0000007fa 0xfcfe03fe000000ff

def z637 : W := mkw 0x0000aa1cb412aeaf 0x20001543968255d5 0xf81ffe3ffc7fffff 0xff03ffc7ff8fffff

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0x2010023000600078 0x84020046000c000f

def z639 : W := mkw 0x26ffe29b6b6d5000 0x04dffc536d6daa00 0x9fffe00ffffff805 0xf3fffc01ffffff00

def z640 : W := mkw 0x0000820800000000 0x0000104100000000 0xa001820c00000003 0x9400304180000000

def z641 : W := mkw 0x27ba7d726ee00550 0x04f74fae4ddc00aa 0xfff27ff07fe007fe 0xfffe4ffe0ffc00ff

def z642 : W := mkw 0x04f540000a645000 0x009ea800014c8a00 0x9ff1e0000fe07804 0xf3fe3c0001fc0f00

def z643 : W := mkw 0x0b0a1406d19b8387 0x81614280da337070 0x0f0e040ff39f8181 0x41e1c081fe73f030

def z644 : W := mkw 0x00658ac90c400440 0x000cb15921880088 0xf0ed9bcf8c400667 0xbe1db379f18800cc

def z645 : W := mkw 0x1b0a9ecfd59ba7e7 0xc36153d9fab374fc 0xff0e1fcfff9f87e7 0x7fe1c3f9fff3f0fc

def z646 : W := mkw 0x000000041010aaad 0x2000000082021555 0x8802040c7071ffff 0x510040818e0e3fff

def z647 : W := mkw 0x0490000000000000 0x0092000000000000 0x87f0000000000000 0xf0fe000000000000

def z648 : W := mkw 0x326feadfec566666 0x464dfd5bfd8acccc 0xf0effbcffc5e6667 0xbe1dff79ff8bcccc

def z649 : W := mkw 0x07ff5d600ee00550 0x00ffebac01dc00aa 0xfffffff00fe007ff 0xfffffffe01fc00ff

def z650 : W := mkw 0x04b009600e600450 0x0096012c01cc008a 0xf0f01bf00c60067e 0xbe1e037e018c00cf

def z651 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x2011e63c70607ffa 0x84023cc78e0c0fff

def z652 : W := mkw 0x0065000008444000 0x000ca00001088800 0x00e1800000406000 0x801c300000080c00

def z653 : W := mkw 0x0000820c00102224 0x0000104180020444 0x2000020c00000662 0x04000041800000cc

def z654 : W := mkw 0x126fcacd8d5f7666 0x424df959b1abeecc 0xf0effbcf8c5ffe67 0xbe1dff79f18bffcc

def z655 : W := mkw 0x224fe29b60000000 0x0449fc536c000000 0xa01fe63ff0000003 0xd403fcc7fe000000

def z656 : W := mkw 0x16ffc2c90b6d7060 0x42dff859216dae0c 0xbfffe3c00ffff865 0xf7fffc7801ffff0c

def z657 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x9fee00000f9f8005 0x73fdc00001f3f000

def z658 : W := mkw 0x08000004911b8287 0x8100000092237050 0x00000000001f8000 0x000000000003f000

def z659 : W := mkw 0x06df400000000000 0x00dbe80000000000 0x8fffe0000071f805 0xf1fffc00000e3f00

def z660 : W := mkw 0x020aa21c3119aaad 0x2041544386233555 0xbf1fe63c7fffffff 0xf7e3fcc78fffffff

def z661 : W := mkw 0x2490613020000000 0x04920c2604000000 0x0010603000000000 0x00020c0600000000

def z662 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x2811e2300071fffc 0x85023c46000e3fff

def z663 : W := mkw 0x030a1c0005890500 0x0061438000b120a0 0xdf0e1c000f9f8787 0x7be1c38001f3f0f0

def z664 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00c180f80000003 0x38018301f0000000

def z665 : W := mkw 0x25f5fff92ee00550 0x04bebfff25dc00aa 0xfff1fff00fe007fe 0xfffe3ffe01fc00ff

def z666 : W := mkw 0x27dff7bf60102224 0x04fbfef7ec020444 0xe7fffffff0506667 0xfcfffffffe0a0ccc

def z667 : W := mkw 0x0000000001090000 0x0000000000212000 0x180000000f9f8004 0x0300000001f3f000

def z668 : W := mkw 0x0900140250808181 0x812002804a101030 0x0000040070000180 0x000000800e000030

def z669 : W := mkw 0x0000000000000000 0x0000000000000000 0x0810043000200198 0x4102008600040033

def z670 : W := mkw 0x07ff5d600fed5550 0x00ffebac01fdaaaa 0x57ec19c00f8e0000 0x2afd833801f1c000

def z671 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x27f3e7f070000000 0xc4fe7cfe0e000000

def z672 : W := mkw 0x15f59fed8c566666 0x42beb3fdb18acccc 0xf7fd9fff8c5e6667 0xfeffb3fff18bcccc

def z673 : W := mkw 0x37dfffffe4122666 0x46fbfffffc8244cc 0xe7fffffff0000663 0xfcfffffffe0000cc

def z674 : W := mkw 0x24d5e3b920000000 0x049abc7724000000 0xe0fdfbff80000003 0xbc1fbf7ff0000000

def z675 : W := mkw 0x05f59fe90ee00550 0x00beb3fd21dc00aa 0xfffd9fff8fe007ff 0xffffb3fff1fc00ff

def z676 : W := mkw 0x2045e29920000000 0x0408bc5324000000 0x0001e00000000000 0x00003c0000000000

def z677 : W := mkw 0x14f58bed8e766676 0x429eb17db1ceccce 0xf0fd9bff8c7e667f 0xbe1fb37ff18fcccf

def z678 : W := mkw 0x0000820c00102224 0x0000104180020444 0xa813e20c0071fe67 0xd5027c41800e3fcc

def z679 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0xa003e20c7051fe67 0x94007c418e0a3fcc

def z680 : W := mkw 0x0f9a1d26d7bb8797 0x81f343a4daf770f2 0xdf1e1c3fffbf879f 0x7be3c387fff7f0f3

def z681 : W := mkw 0x0000a21820000000 0x0000144304000000 0xa813e63c706007ff 0xd5027cc78e0c00ff

def z682 : W := mkw 0x04b000000b6d5000 0x00960000016daa00 0x9ff000000ffff804 0xf3fe000001ffff00

def z683 : W := mkw 0x09001c04959b8787 0x8120038092b370f0 0xdf001c000f9f8786 0x7be0038001f3f0f0

def z684 : W := mkw 0x06dfe21c3010aaad 0x20dbfc4386021555 0xafffe63c7071ffff 0xf5fffcc78e0e3fff

def z685 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0xa810063c706007fe 0xd50200c78e0c00ff

def z686 : W := mkw 0x07ba1d600fe90550 0x00f743ac01fd20aa 0xfffe1ff00fff87ff 0xffffc3fe01fff0ff

def z687 : W := mkw 0x020a0804851b0606 0x0041410090a360c0 0xdf0e180f8f9f8607 0x7be1c301f1f3f0c0

def z688 : W := mkw 0x04b009600ee00550 0x0096012c01dc00aa 0x38f003f00fe007fc 0x871e007e01fc00ff

def z689 : W := mkw 0x04f541600a645050 0x009ea82c014c8a0a 0x20f1e3f000607878 0x841e3c7e000c0f0f

def z690 : W := mkw 0x020a000240000000 0x0041400048000000 0x000e000ff0000001 0x0001c001fe000000

def z691 : W := mkw 0x14f583e90a646070 0x429eb07d214c8c0e 0x20f183f000606078 0x841e307e000c0c0f

def z692 : W := mkw 0x279a753262a00110 0x04f34ea64c540022 0x0f12643073a00198 0x41e24c860e740033

def z693 : W := mkw 0x002008400ee00550 0x0004010801dc00aa 0xb81006300fe007fe 0xd70200c601fc00ff

def z694 : W := mkw 0x0800080494928787 0x81000100929250f0 0x0000000000000780 0x00000000000000f0

def z695 : W := mkw 0x2100b7bf7010aaad 0x242016f7ee021555 0x60001ffff00007fa 0x0c0003fffe0000ff

def z696 : W := mkw 0x06ffc2890b6d5000 0x00dff851216daa00 0xfffffbcf8ffff807 0xffffff79f1ffff00

def z697 : W := mkw 0x0100152000000000 0x002002a400000000 0x60001ff000000002 0x0c0003fe00000000

def z698 : W := mkw 0x0900be1ef492afaf 0xa12017c3de9255f5 0xe813fe3ff071ffff 0xdd027fc7fe0e3fff

def z699 : W := mkw 0x0000000010008081 0x0000000002001010 0x0802040070018180 0x410040800e003030

def z700 : W := mkw 0x030a140240000000 0x0061428048000000 0x470c180380000000 0x28e1830070000000

def z701 : W := mkw 0x2fdff7bff11b8287 0x85fbfef7fe237050 0xe7fffffff01f8003 0xfcfffffffe03f000

def z702 : W := mkw 0x07ff55200bed5110 0x00ffeaa4017daa22 0x9fffe4300ffff99d 0xf3fffc8601ffff33

def z703 : W := mkw 0x37dff7bfe0166226 0x46fbfef7fc02cc44 0xe7fffffff01e6003 0xfcfffffffe03cc00

def z704 : W := mkw 0x124fc28d811f7226 0x4249f851b023ee44 0x000fe00f801ff801 0x0001fc01f003ff00

def z705 : W := mkw 0x0fbabf7efffbafff 0xa1f757efdfff75ff 0xffffffffffffffff 0xffffffffffffffff

def z706 : W := mkw 0x0000000000000000 0x0000000000000000 0x8802000000118005 0x5100400000023000

def z707 : W := mkw 0x102008449ef6efff 0x6204010893deddff 0x180000000ffffffc 0x0300000001ffffff

def z708 : W := mkw 0x27df55a340000000 0x04fbeab468000000 0xc7fffdcff0000003 0xf8ffffb9fe000000

def z709 : W := mkw 0x10658acd8e766676 0x420cb159b1ceccce 0xf0ed9bcf8c7e667f 0xbe1db379f18fcccf

def z710 : W := mkw 0x0045828900000000 0x0008b05120000000 0xf0ed9bcf8c1e0007 0xbe1db379f183c000

def z711 : W := mkw 0x106528d1bc46cccb 0x620ca51a3788d999 0x58fe7df3fc2f9998 0x6b1fcfbe7f85f333

def z712 : W := mkw 0x15d597ad82b66336 0x42bab2f5b056cc66 0x0f1d843f83be6199 0x41e3b087f077cc33

def z713 : W := mkw 0x1065aaddac566e6e 0x620cb55bb58acdcd 0xf0fffffffc7e7e7f 0xfe1fffffff8fcfcf

def z714 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0xf8fc1ff38c6e07fe 0xff1f83fe718dc0ff

def z715 : W := mkw 0x024f4000010d5000 0x0049e8000021aa00 0x9f1fe0000ffff805 0xf3e3fc0001ffff00

def z716 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x570c180fff8e0000 0x2ae18301fff1c000

def z717 : W := mkw 0x27dff7bb63a91110 0x04fbfef76c752222 0xeffffffff3a1999b 0xfdfffffffe743333

def z718 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf8ef9ffffc5fe7ff 0xff1df3ffff8bfcff

def z719 : W := mkw 0x279af73e7339baad 0x24f35ee7ce673755 0xaf13e63c73f1ffff 0xd5e27cc78e7e3fff

def z720 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x47fffdfff0000001 0x68ffffbffe000000

def z721 : W := mkw 0x10658acd9c56eeef 0x620cb159b38adddd 0xf0ed9bcf8c5e67ff 0xbe1db379f18bccff

def z722 : W := mkw 0x27dff7bb63291000 0x04fbfef76c652200 0xe7fffffff3800003 0xfcfffffffe700000

def z723 : W := mkw 0x020a0804951b8687 0x0041410092a370d0 0xdf0e1c0fff9f8787 0x7be1c381fff3f0f0

def z724 : W := mkw 0x06ba40000b6d5000 0x00d74800016daa00 0x9f13e0000ffff805 0xd3e27c0001ffff00

def z725 : W := mkw 0x0eba0166db7b82d7 0x81d7402cdb6f705a 0x20fe03fff07f8079 0x841fc07ffe0ff00f

def z726 : W := mkw 0x06ff40400b6d5050 0x00dfe808016daa0a 0x9fffe0000ffff87d 0xf3fffc0001ffff0f

def z727 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xffee1fcfff9f8787 0xfffdc3f9fff3f0f0

def z728 : W := mkw 0x27dff7bb62201000 0x04fbfef76c440200 0xe7fffffff0201803 0xfcfffffffe040300

def z729 : W := mkw 0x0f9a152253a98191 0x81f342a44a753032 0x0f02040073818180 0x41e040800e703030

def z730 : W := mkw 0x102008449c56e6e7 0x42040108938adcdc 0x180000000c5fe7e4 0x03000000018bfcfc

def z731 : W := mkw 0x0f9ab73e73b9abbd 0xa1f356e7ce773577 0xaf13e63c73f1ffff 0xd5e27cc78e7e3fff

def z732 : W := mkw 0x25d5f7bb60000000 0x04babef76c000000 0xe0fdfffff0000003 0xbc1fbffffe000000

def z733 : W := mkw 0x2cd5ebbdb59b8787 0x859abd77b6b370f0 0x38f1e3f00f9f8784 0x871e3c7e01f3f0f0

def z734 : W := mkw 0x27dff7bb62a00110 0x04fbfef76c540022 0xeffffffff3e007ff 0xfdfffffffe7c00ff

def z735 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xff1ffe3fffffffff 0xffe3ffc7ffffffff

def z736 : W := mkw 0x082008449ffb87d7 0x8104010893ff70fa 0x180000000f9f8784 0x0300000001f3f0f0

def z737 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0x50ed99c38c1e6001 0x2a1db3387183cc00

def z738 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x9fffe4300ffff99d 0xf3fffc8601ffff33

def z739 : W := mkw 0x0db01d62cee20552 0x81b603ac59dc40aa 0xfff01ff38fe007fe 0xfffe03fe71fc00ff

def z740 : W := mkw 0x106508c58c564646 0x420ca118b18ac8c8 0x50ec19cf8c1e0001 0x2a1d8339f183c000

def z741 : W := mkw 0x10658acd9c56eeef 0x620cb159b38adddd 0xf0ed9bcf8c5ffe67 0xbe1db379f18bffcc

def z742 : W := mkw 0x0045828d80120206 0x0008b051b0024040 0xe0ed9bcf801e0003 0xbc1db379f003c000

def z743 : W := mkw 0x10658acd9c56e6e7 0x420cb159b38adcdc 0xf0ef9bcffc5fe667 0xbe1df379ff8bfccc

def z744 : W := mkw 0x37ba7d76ec566666 0x46f74faedd8acccc 0x171264307c5e6664 0x42e24c860f8bcccc

def z745 : W := mkw 0x1065aad9ac464442 0x420cb55b3588c888 0xf0fffffffc0e0003 0xfe1fffffff81c000

def z746 : W := mkw 0x26dfe29b60000000 0x04dbfc536c000000 0xe7fffbcff0000003 0xfcffff79fe000000

def z747 : W := mkw 0x0df55c06def6d787 0x81beab80dbdedaf0 0x40f1fc0ff0607f82 0x881e3f81fe0c0ff0

def z748 : W := mkw 0x07df552240000000 0x00fbeaa448000000 0xe7fffffff0000003 0xfcfffffffe000000

def z749 : W := mkw 0x106508c58c566666 0x420ca118b18acccc 0x50ec19c38c0e0660 0x2a1d83387181c0cc

def z750 : W := mkw 0x06ffe21c3b7dfaad 0x20dffc43876fbf55 0x37ec063c7f8e07fa 0x26fd80c78ff1c0ff

def z751 : W := mkw 0x1065aaddbef6efff 0x620cb55bb7deddff 0xf8ffffffffffffff 0xff1fffffffffffff

def z752 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x5f0e1c0fff8f8782 0x6be1c381fff1f0f0

def z753 : W := mkw 0x224fe29b60000000 0x0449fc536c000000 0x40eff9cff0000001 0x281dff39fe000000

def z754 : W := mkw 0x10658acd8c564646 0x420cb159b18ac8c8 0xf0ed9bcf8c1e0607 0xbe1db379f183c0c0

def z755 : W := mkw 0x0b0a1d26d59b8787 0x816143a4dab370f0 0xff0e1fffff9f8787 0x7fe1c3fffff3f0f0

def z756 : W := mkw 0x05901d6006a00550 0x00b203ac00d400aa 0xeff01ff003a007fa 0xfdfe03fe007400ff

def z757 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x7ff01ff00fa007fa 0x6ffe03fe01f400ff

def z758 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x7ff01bf00fe007fc 0xaffe037e01fc00ff

def z759 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf1e7c0fffbf9f87 0x7be3cf81fff7f3f0

def z760 : W := mkw 0x27dff7bb62a00110 0x04fbfef76c540022 0xe7fffffff3800003 0xfcfffffffe700000

def z761 : W := mkw 0x182008449cd6e7e7 0xc3040108939adcfc 0x100000000c5e67e4 0x02000000018bccfc

def z762 : W := mkw 0x10658ac98c464442 0x420cb1593188c888 0x70ed9bc38c0e0000 0xae1db3787181c000

def z763 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xffffffffff800007 0xfffffffffff00000

def z764 : W := mkw 0x279af7bb60000000 0x04f35ef76c000000 0xe7f27ffff0000002 0xfcfe4ffffe000000

def z765 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0xd0ec19cf8c0e0003 0x3a1d8339f181c000

def z766 : W := mkw 0x0045aa9db412aeaf 0x2008b553b68255d5 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z767 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x5f0e180fff9f8785 0x2be1c301fff3f0f0

def z768 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xe7fffffff0506007 0xfcfffffffe0a0c00

def z769 : W := mkw 0x14f5a3f92a646878 0x629eb47f254c8d0f 0x20f1e3f000607878 0x841e3c7e000c0f0f

def z770 : W := mkw 0x0590152002a00110 0x00b202a400540022 0xeff01ff003e007fe 0xfdfe03fe007c00ff

def z771 : W := mkw 0x27dff7bb61090000 0x04fbfef76c212000 0xfffffffffffff807 0xffffffffffffff00

def z772 : W := mkw 0x27dff7bb63291000 0x04fbfef76c652200 0xeffffffff3f1f807 0xfdfffffffe7e3f00

def z773 : W := mkw 0x2f9a552251898181 0x85f34aa44a313030 0x0f02040073818180 0x41e040800e703030

def z774 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xffe01ff00f8007fe 0x7ffc03fe01f000ff

def z775 : W := mkw 0x05b015200a600000 0x00b602a4014c0000 0xfff01ff00fe007fe 0xfffe03fe01fc00ff

def z776 : W := mkw 0x34f5e3f92a646070 0x469ebc7f254c8c0e 0x20f1e3f000606078 0x841e3c7e000c0c0f

def z777 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xd70e180fff9f8607 0x3ae1c301fff3f0c0

def z778 : W := mkw 0x10658ac98c464442 0x420cb1593188c888 0xf0ed9bcf8c4e0667 0xbe1db379f189c0cc

def z779 : W := mkw 0x0065a29928444000 0x000cb45325088800 0xf8fffffffc7ff807 0xff1fffffff8fff00

def z780 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x5f0c1c0fff9f8786 0x2be18381fff3f0f0

def z781 : W := mkw 0x10658acd8ef66776 0x420cb159b1deccee 0xf8fd9fff8ffe67ff 0xff1fb3fff1ffccff

def z782 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xd0ed99cf8c5e6005 0xba1db339f18bcc00

def z783 : W := mkw 0x24d5e3b920000000 0x049abc7724000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z784 : W := mkw 0x10458a8d84166626 0x4208b151b082ccc4 0xf0ed9bcf8c1e6607 0xbe1db379f183ccc0

def z785 : W := mkw 0x020a000241090000 0x0041400048212000 0x9f0e000fff9f8005 0x73e1c001fff3f000

def z786 : W := mkw 0x026f0000094d4000 0x004de0000129a800 0x9fffe0000ffff805 0xf3fffc0001ffff00

def z787 : W := mkw 0x169acacd873b3666 0x42d35959b0e766cc 0x6f127bcf83a19e62 0x4de24f79f07433cc

def z788 : W := mkw 0x05b0bf7c3ef0affd 0x20b617ef87de15ff 0x57e3f9cc7f91f801 0x2afc7f398ff23f00

def z789 : W := mkw 0x00658a8d8c564606 0x000cb151b18ac8c0 0xf0ed9bcf8c5e6607 0xbe1db379f18bccc0

def z790 : W := mkw 0x00658ac90c444440 0x000cb15921888888 0xf0ed9bcf8c5e6667 0xbe1db379f18bcccc

def z791 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xeffffffff0000787 0xfdfffffffe0000f0

def z792 : W := mkw 0x1045828980064002 0x4208b0513000c800 0xe0ed9bcf800e0003 0xbc1db379f001c000

def z793 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf1ffc0fff9f8787 0xfbe3ff81fff3f0f0

def z794 : W := mkw 0x0b0abe1ae58b2d2a 0xa16157c35cb165a5 0x771dfa338fee7878 0xaee3bf4671fdcf0f

def z795 : W := mkw 0x04f540000b6d5000 0x009ea800016daa00 0x9ff1e0000ffff804 0xf3fe3c0001ffff00

def z796 : W := mkw 0x279a753261090000 0x04f34ea64c212000 0x0f12643073818000 0x41e24c860e703000

def z797 : W := mkw 0x106508c58c564646 0x420ca118b18ac8c8 0x50ec19cf8c0e0602 0x2a1d8339f181c0c0

def z798 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x1fffe0000fbff801 0x63fffc0001f7ff00

def z799 : W := mkw 0x1100bffdb492afff 0x622017ffb69255ff 0x60001ffff00007fa 0x0c0003fffe0000ff

def z800 : W := mkw 0x0b0a140251898181 0x816142804a313030 0xdf0e1c0fff9f8187 0x7be1c381fff3f030

def z801 : W := mkw 0x034f148340000000 0x0069e29068000000 0xc7ee1dcff0000003 0x78fdc3b9fe000000

def z802 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xc7fff9cff0000001 0xf8ffff39fe000000

def z803 : W := mkw 0x034fb69b60000000 0x0069f6d36c000000 0xe7fffffff0000003 0xfcfffffffe000000

def z804 : W := mkw 0x05901d2004800500 0x00b203a4009000a0 0xfff01ff00fe007fe 0xfffe03fe01fc00ff

def z805 : W := mkw 0x27dff7bb61090000 0x04fbfef76c212000 0xeffffffff3818003 0xfdfffffffe703000

def z806 : W := mkw 0x04f500000a644000 0x009ea000014c8800 0x9fffe0000ffff805 0xf3fffc0001ffff00

def z807 : W := mkw 0x14f5e2d92a647868 0x629ebc5b254c8f0d 0x20f1e3f000607878 0x841e3c7e000c0f0f

def z808 : W := mkw 0x10658acd9c56e6e7 0x420cb159b38adcdc 0xf8ffffcffc7fffe7 0xff1ffff9ff8ffffc

def z809 : W := mkw 0x000020143010aaad 0x2000040286021555 0x8813e4307071fffd 0xd1027c860e0e3fff

def z810 : W := mkw 0x2120b7bb6b6d5000 0x042416f76d6daa00 0x78001ffffffff806 0x0f0003ffffffff00

def z811 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x70ed9bcf8c5e6061 0xae1db379f18bcc0c

def z812 : W := mkw 0x079a152240000000 0x00f342a448000000 0xc7ee1dcff0000003 0x78fdc3b9fe000000

def z813 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xe7ee1ffff0000003 0x7cfdc3fffe000000

def z814 : W := mkw 0x00458a8984020402 0x0008b15130804080 0xf0ed9bcf8c0e0003 0xbe1db379f181c000

def z815 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x1f1fe0000ffff805 0x43e3fc0001ffff00

def z816 : W := mkw 0x2145b7bb60000000 0x0428b6f76c000000 0x60e19ffff0000002 0x8c1c33fffe000000

def z817 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0xd0ec19c38c1e0005 0x3a1d83387183c000

def z818 : W := mkw 0x0b0a1c02c58b0502 0x8161438058b160a0 0x570e180fff8e0001 0x2ae1c301fff1c000

def z819 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0ed9bcf8c1e6003 0xbe1db379f183cc00

def z820 : W := mkw 0x082008449ffbafff 0xa104010893ff75ff 0x180000000ffffffc 0x0300000001ffffff

def z821 : W := mkw 0x030a1c06c51b0606 0x00614380d8a360c0 0xdf0e1c0fff9f8607 0x7be1c381fff3f0c0

def z822 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0xd8fff9c38c7ff805 0xfb1fff38718fff00

def z823 : W := mkw 0x0045a29920000000 0x0008b45324000000 0xe0ed9ffff0000003 0xbc1db3fffe000000

def z824 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xd0ed99cf8c1e6607 0x3a1db339f183ccc0

def z825 : W := mkw 0x05b01d624ee00550 0x00b603ac49dc00aa 0xfff01fffffe007fe 0xfffe03fffffc00ff

def z826 : W := mkw 0x1b0a1c46d59ba7e7 0xc3614388dab374fc 0xdf0e1c0fff9f87e7 0x7be1c381fff3f0fc

def z827 : W := mkw 0x05b015600ae00150 0x00b602ac015c002a 0xaff007f003e007fe 0xd5fe00fe007c00ff

def z828 : W := mkw 0x1045828d80166226 0x4208b051b002cc44 0x40ed99cf801e6001 0x281db339f003cc00

def z829 : W := mkw 0x06ff40400b6d5040 0x00dfe808016daa08 0xbfffe3c00ffff865 0xf7fffc7801ffff0c

def z830 : W := mkw 0x0b0a1c02c58b0502 0x8161438058b160a0 0x570c1c0fff8e0002 0x2ae18381fff1c000

def z831 : W := mkw 0x10658acd8ef66776 0x420cb159b1deccee 0xf0ed9bcf8fde6667 0xbe1db379f1fbcccc

def z832 : W := mkw 0x06dfe29920000000 0x00dbfc5324000000 0xe7fffffff0000003 0xfcfffffffe000000

def z833 : W := mkw 0x2145b7bb60000000 0x0428b6f76c000000 0x60ec1ffff0000002 0x2c1d83fffe000000

def z834 : W := mkw 0x10658ac98c466462 0x420cb1593188cc8c 0x50ed99c38c0e6000 0x2a1db3387181cc00

def z835 : W := mkw 0x05901d6004800550 0x00b203ac009000aa 0xfff01ff00f8007fe 0xfffe03fe01f000ff

def z836 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0xd0ed99c38c0e0001 0xba1db3387181c000

def z837 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x50ec19cf8c0e0000 0x2a1d8339f181c000

def z838 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf8efffcffc5fffe7 0xff1dfff9ff8bfffc

def z839 : W := mkw 0x1065aaddac566666 0x420cb55bb58acccc 0xf0fdfbff8c5e6667 0xbe1fbf7ff18bcccc

def z840 : W := mkw 0x10658ac98c466462 0x420cb1593188cc8c 0xf0ed9bcf8c4e6063 0xbe1db379f189cc0c

def z841 : W := mkw 0x106508c58c564646 0x420ca118b18ac8c8 0x50ec19c38c1e0604 0x2a1d83387183c0c0

def z842 : W := mkw 0x04b001600a600050 0x0096002c014c000a 0xbff007f00fe007fe 0xf7fe00fe01fc00ff

def z843 : W := mkw 0x1a4fa29ff11feaaf 0xe349f453fe23fd55 0x000fe00ff01ff801 0x0001fc01fe03ff00

def z844 : W := mkw 0x27df55a75010aaad 0x24fbeab4ea021555 0x4fec19c38071fffc 0x29fd8338700e3fff

def z845 : W := mkw 0x01201d600cc00550 0x002403ac019800aa 0xffe01ff00fc007fe 0xfffc03fe01f800ff

def z846 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x1ff3e0000ffff804 0xc3fe7c0001ffff00

def z847 : W := mkw 0x27dff7bb610d5000 0x04fbfef76c21aa00 0xeffffffff07ff807 0xfdfffffffe0fff00

def z848 : W := mkw 0x279a753263a91110 0x04f34ea64c752222 0x0f12643073a19998 0x41e24c860e743333

def z849 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0x70ec1bc38c4e0060 0xae1d83787189c00c

def z850 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xf7e01ff00fc007fe 0xbefc03fe01f800ff

def z851 : W := mkw 0x106508c59c56eeef 0x620ca118b38adddd 0x58ec19c38c7ffffc 0x2b1d8338718fffff

def z852 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf8ffffff8c7fffff 0xff1ffffff18fffff

def z853 : W := mkw 0x10208acd8c522666 0x42041159b18a44cc 0xf0ec1bcf8c5e0667 0xbe1d8379f18bc0cc

def z854 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0x50ec19c38c4e0664 0x2a1d83387189c0cc

def z855 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf8ed9fcf8c5e67e7 0xff1db3f9f18bccfc

def z856 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x70ed9bcf8c4e6662 0xae1db379f189cccc

def z857 : W := mkw 0x0f9a552253a99191 0x81f34aa44a753232 0x0f12643073a19998 0x41e24c860e743333

def z858 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0xf0ec1bc38c0e0002 0xbe1d83787181c000

def z859 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x1fefe0000ffff805 0x23fdfc0001ffff00

def z860 : W := mkw 0x25d5b7bb60000000 0x04bab6f76c000000 0xe7fd9ffff0000003 0xfcffb3fffe000000

def z861 : W := mkw 0x37dff7bb60046020 0x46fbfef76c008c04 0xe7fffffff0006003 0xfcfffffffe000c00

def z862 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0xd0ec19c38c0e0606 0x3a1d83387181c0c0

def z863 : W := mkw 0x1045008180064002 0x4208a0103000c800 0x40ec19c3800e0000 0x281d83387001c000

def z864 : W := mkw 0x10458acd84166666 0x4208b159b082cccc 0xe0ed9bcf801e6663 0xbc1db379f003cccc

def z865 : W := mkw 0x04b000000b6d5000 0x00960000016daa00 0x9ff3e0000ffff805 0xf3fe7c0001ffff00

def z866 : W := mkw 0x082008449fffd7d7 0x8104010893fffafa 0x180000000ffffffc 0x0300000001ffffff

def z867 : W := mkw 0x0b0a1406d19b8387 0x81614280da337070 0x9f0e040fff9f8185 0x73e1c081fff3f030

def z868 : W := mkw 0x0b0a1c06d59bafaf 0xa1614380dab375f5 0xdf1ffc0fffffffff 0xfbe3ff81ffffffff

def z869 : W := mkw 0x24f5e3f92a645050 0x049ebc7f254c8a0a 0x20f1e3f000607878 0x841e3c7e000c0f0f

def z870 : W := mkw 0x06df400001090000 0x00dbe80000212000 0x9fffe0000ffff805 0xf3fffc0001ffff00

def z871 : W := mkw 0x024f4000010d5000 0x0049e8000021aa00 0x170fe0000f9ff801 0x22e1fc0001f3ff00

def z872 : W := mkw 0x0020aa5cbc52aeef 0x2004154b978a55dd 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z873 : W := mkw 0x1b6f96cb59cde1e1 0xc36df2d96b39bc3c 0x2fe387c073c1e1e0 0xc5fc70f80e783c3c

def z874 : W := mkw 0x182008449ddfc7c7 0xc304010893bbf8f8 0x180000000f9f8784 0x0300000001f3f0f0

def z875 : W := mkw 0x2f9af73e71998385 0x85f35ee7ce333070 0xaf13e63c73918787 0xd5e27cc78e7230f0

def z876 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0xbfffe2000ffffe67 0xf7fffc4001ffffcc

def z877 : W := mkw 0x1065aaddac566666 0x420cb55bb58acccc 0xf0ed9ffffc5e6667 0xbe1db3ffff8bcccc

def z878 : W := mkw 0x0f9a152653b98395 0x81f342a4ca773072 0xaf12063c73f187ff 0xd5e240c78e7e30ff

def z879 : W := mkw 0x18658acd9cd6e7e7 0xc30cb159b39adcfc 0xf0ed9bcf8c5e67e7 0xbe1db379f18bccfc

def z880 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xd70e1c0fff8e0783 0x7ae1c381fff1c0f0

def z881 : W := mkw 0x034f5d60058d5550 0x0069ebac00b1aaaa 0x600ffff0001ffffb 0x0c01fffe0003ffff

def z882 : W := mkw 0x279a753261091000 0x04f34ea64c212200 0x0712643070019800 0x40e24c860e003300

def z883 : W := mkw 0x0000a2183000a8a9 0x2000144306001515 0xa813e6307061fffe 0xd5027cc60e0c3fff

def z884 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0fffbcf8c5e6667 0xfe1fff79f18bcccc

def z885 : W := mkw 0x27ff5de34fed5550 0x04ffebbc69fdaaaa 0x57ec19c38f8e0000 0x2afd833871f1c000

def z886 : W := mkw 0x05b01d608ee20552 0x00b603ac11dc40aa 0xfffc1ff38fee07fe 0xffff83fe71fdc0ff

def z887 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf8fffbcffc7ffe67 0xff1fff79ff8fffcc

def z888 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf8effbcffc7fffff 0xbf1dff79ff8fffff

def z889 : W := mkw 0x279a753263291000 0x04f34ea64c652200 0x0712643073800000 0x40e24c860e700000

def z890 : W := mkw 0x024f828b40000000 0x0049f05168000000 0xe0ef9bcff0000003 0xbc1df379fe000000

def z891 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xc7effdcff0000003 0x78fdffb9fe000000

def z892 : W := mkw 0x2590b7bb60000000 0x04b216f76c000000 0xe7f3fffff0000003 0xfcfe7ffffe000000

def z893 : W := mkw 0x05d5b7b920000000 0x00bab6f724000000 0xe7fffffff0000003 0xfcfffffffe000000

def z894 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf0e1c0fffffff87 0x7be1c381fffffff0

def z895 : W := mkw 0x0000a21cb012aaaf 0x2000144396025555 0xa81fe63ff07fffff 0xd503fcc7fe0fffff

def z896 : W := mkw 0x106508c58c566666 0x420ca118b18acccc 0x50ec19c38c1e6000 0x2a1d83387183cc00

def z897 : W := mkw 0x0045088184020402 0x0008a11030804080 0x50ec19c38c0e0000 0x2a1d83387181c000

def z898 : W := mkw 0x030a140651198285 0x00614280ca233050 0xdf0e1c0fff9f8787 0x7be1c381fff3f0f0

def z899 : W := mkw 0x020a000001090000 0x0041400000212000 0x9f0fe0000f9ff805 0x73e1fc0001f3ff00

def z900 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xd70c1c0fff9e0787 0x3ae18381fff3c0f0

def z901 : W := mkw 0x0045828900000000 0x0008b05120000000 0xe0ef9fcff0000003 0xfc1df3f9fe000000

def z902 : W := mkw 0x16ff40c10b6d5040 0x42dfe818216daa08 0x9fffe1c00ffff805 0xf3fffc3801ffff00

def z903 : W := mkw 0x0a0a0806d59b8787 0x81414100dab370f0 0x9f0e000fff9f8785 0x73e1c001fff3f0f0

def z904 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x7fe01ff00fe007fe 0x2ffc03fe01fc00ff

def z905 : W := mkw 0x1045a29db016eaaf 0x6208b453b602dd55 0xe0fffffff01ff803 0xfc1ffffffe03ff00

def z906 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf8fd9ffffc7e67ff 0xff1fb3ffff8fccff

def z907 : W := mkw 0x226feadb6ee00550 0x044dfd5b6ddc00aa 0x180fe00fffe007fd 0x0301fc01fffc00ff

def z908 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0xb81fe63c7c7fffff 0xf703fcc78f8fffff

def z909 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x17ffe0000ffff801 0xa2fffc0001ffff00

def z910 : W := mkw 0x15b01d608ee64552 0x42b603ac11dcc8aa 0xfff01ff00fee07fe 0xfffe03fe01fdc0ff

def z911 : W := mkw 0x27dff7bb62200010 0x04fbfef76c440002 0xe7fffffff020001b 0xfcfffffffe040003

def z912 : W := mkw 0x2f9a753273a99181 0x85f34ea64e753230 0x0f12643073a19980 0x41e24c860e743330

def z913 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf8fd9bcf8c7e6667 0xff1fb379f18fcccc

def z914 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf8ed9bcf8c7e67ff 0xbf1db379f18fccff

def z915 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0xdffff80f8ffff807 0xfbffff01f1ffff00

def z916 : W := mkw 0x106508c18c466462 0x420ca1183188cc8c 0x50ec19c38c4e6060 0x2a1d83387189cc0c

def z917 : W := mkw 0x06df4000010d5000 0x00dbe8000021aa00 0x9fffe0000f9ff805 0xf3fffc0001f3ff00

def z918 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xfffc1fff8fe007ff 0xffff83fff1fc00ff

def z919 : W := mkw 0x0b0a1c06d59bafaf 0xa1614380dab375f5 0xdf0e1c0fff9fff87 0x7be1c381fff3fff0

def z920 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf0f9c0fffdfe787 0xfbe1f381fffbfcf0

def z921 : W := mkw 0x06ff41200b6d5010 0x00dfe824016daa02 0x9fffe0300ffff81d 0xf3fffc0601ffff03

def z922 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xf7fffffffc1e0007 0xfeffffffff83c000

def z923 : W := mkw 0x224fe29b60000000 0x0449fc536c000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z924 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf8ed9ffffc7fffff 0xbf1db3ffff8fffff

def z925 : W := mkw 0x0b0a5c06d59b9787 0x81614b80dab372f0 0xdf0e7c0fff9f9f87 0x7be1cf81fff3f3f0

def z926 : W := mkw 0x2f9af73e7199abad 0xa5f35ee7ce333575 0xaf13e63c73f1ffff 0xd5e27cc78e7e3fff

def z927 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf0c1c0fff8e0786 0x7be18381fff1c0f0

def z928 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf8ed9bcf8c7ffe67 0xbf1db379f18fffcc

def z929 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0x70ec1ffffc0e07fa 0x2e1d83ffff81c0ff

def z930 : W := mkw 0x279ab7bb60000000 0x04f356f76c000000 0xe7fe1ffff0000003 0xfcffc3fffe000000

def z931 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xeffffffff071ffff 0xfdfffffffe0e3fff

def z932 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x6ff01ff003e007fa 0xcdfe03fe007c00ff

def z933 : W := mkw 0x0065008108444000 0x000ca01021088800 0x50ec19c38c0e0000 0x2a1d83387181c000

def z934 : W := mkw 0x27dff7bb610d5000 0x04fbfef76c21aa00 0xffffffffff9ff807 0xfffffffffff3ff00

def z935 : W := mkw 0x04b009600ee00550 0x0096012c01dc00aa 0xbff003f00fe007fc 0xf7fe007e01fc00ff

def z936 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0ef9fcffc5e6667 0xfe1df3f9ff8bcccc

def z937 : W := mkw 0x27df75b360000000 0x04fbeeb66c000000 0xc7fe7dfff0000003 0x78ffcfbffe000000

def z938 : W := mkw 0x279a552243291000 0x04f34aa448652200 0x0f12600003a19800 0x41e24c0000743300

def z939 : W := mkw 0x1065aaddac566e6e 0x620cb55bb58acdcd 0xf8fffbff8c7ffe7f 0xff1fff7ff18fffcf

def z940 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0xbfffe2300ffff87d 0xf7fffc4601ffff0f

def z941 : W := mkw 0x0f9a353273a98999 0xa1f346a64e753133 0x0f12643073a19998 0x41e24c860e743333

def z942 : W := mkw 0x27dff7bb60002828 0x24fbfef76c000505 0xe7fffffff0007803 0xfcfffffffe000f00

def z943 : W := mkw 0x030a140241090000 0x0061428048212000 0xd70e1c0fff8e0003 0x7ae1c381fff1c000

def z944 : W := mkw 0x27dff7bb62200000 0x04fbfef76c440000 0xeffffffff3a00003 0xfdfffffffe740000

def z945 : W := mkw 0x0045aa9db4128687 0x0008b553b68250d0 0xf8fffffffc1f8787 0xff1fffffff83f0f0

def z946 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x0813e43c7071fffd 0x41027c878e0e3fff

def z947 : W := mkw 0x1065aad9ac466c6a 0x620cb55b3588cd8d 0x70fdfbf38c6e7878 0xae1fbf7e718dcf0f

def z948 : W := mkw 0x002008408c420442 0x0004010811884088 0xf0ec1bc38c4e0666 0xbe1d83787189c0cc

def z949 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xeffffffff0219803 0xfdfffffffe043300

def z950 : W := mkw 0x2fdff7bb61890100 0x85fbfef76c312020 0xe7fffffff3800003 0xfcfffffffe700000

def z951 : W := mkw 0x27dff7bb61090000 0x04fbfef76c212000 0xe7fffffff01f8003 0xfcfffffffe03f000

def z952 : W := mkw 0x06ff41600b6d5050 0x00dfe82c016daa0a 0x9fffe1c00ffff805 0xf3fffc3801ffff00

def z953 : W := mkw 0x069a400003291000 0x00d3480000652200 0x9f1fe0000ffff805 0xf3e3fc0001ffff00

def z954 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf0fffbfffc7ffe7f 0xbe1fff7fff8fffcf

def z955 : W := mkw 0x2f9a753271098081 0x85f34ea64e213010 0x0712643070018000 0x40e24c860e003000

def z956 : W := mkw 0x2a4fe29ff11baaaf 0xa549fc53fe237555 0x000fe00ff01ff801 0x0001fc01fe03ff00

def z957 : W := mkw 0x234ff7bb60000000 0x0469fef76c000000 0xe0effffff0000003 0xbc1dfffffe000000

def z958 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf0ed9bcffc5e6667 0xbe1db379ff8bcccc

def z959 : W := mkw 0x006508448c564646 0x000ca108918ac8c8 0xf0ed9bcf8c5e6667 0xbe1db379f18bcccc

def z960 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x50ed99cf8c5e6665 0x2a1db339f18bcccc

def z961 : W := mkw 0x0b0a1d66d59b87d7 0x816143acdab370fa 0xff1e1fffffff87ff 0xffe3c3fffffff0ff

def z962 : W := mkw 0x0f9a152243a90110 0x81f342a448752022 0x0f10043003a00198 0x41e2008600740033

def z963 : W := mkw 0x0000a29d3010aaad 0x20001453a6021555 0xe813fffff071ffff 0xdd027ffffe0e3fff

def z964 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x60ed9bcf805e6663 0x8c1db379f00bcccc

def z965 : W := mkw 0x1065aaddbc56e6e7 0x420cb55bb78adcdc 0xf8fffffffc5fe7e7 0xff1fffffff8bfcfc

def z966 : W := mkw 0x2f9a552241890100 0x85f34aa448312020 0x0700000003800000 0x00e0000000700000

def z967 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x2013e63c7071fffb 0x84027cc78e0e3fff

def z968 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0fd9bff8c7e667f 0xbe1fb37ff18fcccf

def z969 : W := mkw 0x182008449ffff7e7 0xc304010893fffefc 0x180000000fffffe4 0x0300000001fffffc

def z970 : W := mkw 0x1000a29db012aaaf 0x62001453b6025555 0xa813e63ff071ffff 0xd5027cc7fe0e3fff

def z971 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x67fdfffff0000002 0xacffbffffe000000

def z972 : W := mkw 0x27dff7bb63291000 0x04fbfef76c652200 0xffffffffffbf9807 0xfffffffffff7f300

def z973 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xfff19ff00ff067ff 0xfffe33fe01fe0cff

def z974 : W := mkw 0x10658acd8c566e6e 0x620cb159b18acdcd 0xf0ed9bcf8c7e7e7f 0xbe1db379f18fcfcf

def z975 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0xf0ed9bc38c5e6667 0xbe1db378718bcccc

def z976 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x77f01ff00fe007fa 0xaefe03fe01fc00ff

def z977 : W := mkw 0x106508c58c564646 0x420ca118b18ac8c8 0xf0ec1bcf8c5e0667 0xbe1d8379f18bc0cc

def z978 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x70ec1bcf8c5e6666 0x2e1d8379f18bcccc

def z979 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xfff21ffc7fe007ff 0xfffe43ff8ffc00ff

def z980 : W := mkw 0x0045a29920000000 0x0008b45324000000 0xe0effbcff0000003 0xbc1dff79fe000000

def z981 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xfff3fff00fe007ff 0xfffe7ffe01fc00ff

def z982 : W := mkw 0x27dff7bb60002828 0x24fbfef76c000505 0xe7fffffff000007b 0xfcfffffffe00000f

def z983 : W := mkw 0x0000201030008889 0x2000040206001111 0xa813e6307071ffff 0xd5027cc60e0e3fff

def z984 : W := mkw 0x0045828900044000 0x0008b05120008800 0xe0ed9bcf801e6003 0xbc1db379f003cc00

def z985 : W := mkw 0x102008449c56eeef 0x62040108938adddd 0x100000000c5e67fc 0x02000000018bccff

def z986 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x70ed9bcf8c1e6663 0x2e1db379f183cccc

def z987 : W := mkw 0x102008449f7ffeef 0x6204010893efffdd 0x180000000ffffffc 0x0300000001ffffff

def z988 : W := mkw 0x06ff40810b6d5000 0x00dfe810216daa00 0xdffff9c38ffff805 0xfbffff3871ffff00

def z989 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0xbf13e63c7ff1ffff 0xf7e27cc78ffe3fff

def z990 : W := mkw 0x1045a29db016eaaf 0x6208b453b602dd55 0xe8fffffff07fffff 0xfd1ffffffe0fffff

def z991 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xfff21ff00ff187ff 0xfffe43fe01fe30ff

def z992 : W := mkw 0x102008449c56eeef 0x62040108938adddd 0x100000000c5ffe64 0x02000000018bffcc

def z993 : W := mkw 0x002008408c420442 0x0004010811884088 0x50ec19c38c0e0000 0x2a1d83387181c000

def z994 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x97efe0000fdff805 0xb2fdfc0001fbff00

def z995 : W := mkw 0x0b0a1c46d59b87d7 0x81614388dab370fa 0xdf0e1c0fff9f87ff 0x7be1c381fff3f0ff

def z996 : W := mkw 0x182008449fffe7f7 0xc304010893fffcfe 0x180000000fffe7fc 0x0300000001fffcff

def z997 : W := mkw 0x24f5e2992a645000 0x049ebc53254c8a00 0x00f1e00000607800 0x801e3c00000c0f00

def z998 : W := mkw 0x0f9a152243a90110 0x81f342a448752022 0x0700000003800000 0x00e0000000700000

def z999 : W := mkw 0x10658acd9ef6efff 0x620cb159b3deddff 0xf8ed9bcf8fffffff 0xbf1db379f1ffffff

def z1000 : W := mkw 0x0b0a1c02c58b0502 0x8161438058b160a0 0xdf0e1c0fff8e0787 0x7be1c381fff1c0f0

def z1001 : W := mkw 0x234ff69b60000000 0x0469fed36c000000 0xe7efffcff0000003 0xfcfdfff9fe000000

def z1002 : W := mkw 0x10658acd9c56e6e7 0x420cb159b38adcdc 0xf0ed9fcffc5e67e7 0xbe1db3f9ff8bccfc

def z1003 : W := mkw 0x182008449d5fe6e7 0xc304010893abfcdc 0x100000000c5fe664 0x02000000018bfccc

def z1004 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x67f3fffff0000002 0xccfe7ffffe000000

def z1005 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0x50eff9cffc1ff801 0x2a1dff39ff83ff00

def z1006 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xfff1fff00fe07ffe 0xfffe3ffe01fc0fff

def z1007 : W := mkw 0x0b0a1c06c59b0706 0x81614380d8b360e0 0xd70e1c0fff9e0607 0x7ae1c381fff3c0c0

def z1008 : W := mkw 0x10658acd8cd66766 0x420cb159b19accec 0xf8ed9bcf8fde67e7 0xbf1db379f1fbccfc

def z1009 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf8fdfbff8c7fffff 0xbf1fbf7ff18fffff

def z1010 : W := mkw 0x0b0a1c06d59b8f8f 0xa1614380dab371f1 0xdf0e1c0fffbf9f9f 0x7be1c381fff7f3f3

def z1011 : W := mkw 0x09001c06d4928787 0x81200380da9250f0 0xdf0c1c0fff9e0787 0x7be18381fff3c0f0

def z1012 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf0ffc0fff9fff87 0x7be1ff81fff3fff0

def z1013 : W := mkw 0x10658ac98c466462 0x420cb1593188cc8c 0xf0ed9bc38c5e6065 0xbe1db378718bcc0c

def z1014 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf0fffffffc5e67ff 0xfe1fffffff8bccff

def z1015 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xe7fffffff011f803 0xfcfffffffe023f00

def z1016 : W := mkw 0x022a00000b6d5000 0x00454000016daa00 0x9f1fe0000ffff805 0xf3e3fc0001ffff00

def z1017 : W := mkw 0x06ff40024b6d5000 0x00dfe800496daa00 0x9fffe00ffffff805 0xf3fffc01ffffff00

def z1018 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xfff01ff00ff1fffe 0xfffe03fe01fe3fff

def z1019 : W := mkw 0x27dff7bb60000808 0x24fbfef76c000101 0xe7fffffff020181b 0xfcfffffffe040303

def z1020 : W := mkw 0x1900bedff492afef 0xe32017dbfe9255fd 0x60001ffff00007fa 0x0c0003fffe0000ff

def z1021 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0x70ec1bc38c0e0662 0x2e1d83787181c0cc

def z1022 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xfffc1ff00ffe07ff 0xffff83fe01ffc0ff

def z1023 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x9fefe0000f9ff805 0x73fdfc0001f3ff00

def z1024 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xfff27ff00fe19ffe 0xfffe4ffe01fc33ff

def z1025 : W := mkw 0x27dff7bb60002020 0x04fbfef76c000404 0xe7fffffff0406063 0xfcfffffffe080c0c

def z1026 : W := mkw 0x27dff7bb60044000 0x04fbfef76c008800 0xe7fffffff01e6003 0xfcfffffffe03cc00

def z1027 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf0effffffc5fffff 0xbe1dffffff8bffff

def z1028 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf0fffffffc5ffe67 0xfe1fffffff8bffcc

def z1029 : W := mkw 0x27df55a340000000 0x04fbeab468000000 0x47ec1dcff0000002 0x28fd83b9fe000000

def z1030 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0effbcf8c5ffe67 0xbe1dff79f18bffcc

def z1031 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x60fffffff0000003 0x8c1ffffffe000000

def z1032 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x5f0e1c0fff9f8181 0x6be1c381fff3f030

def z1033 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0x70ed9bc38c5e6664 0xae1db378718bcccc

def z1034 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x67effffff0000003 0x2cfdfffffe000000

def z1035 : W := mkw 0x106508c58c566666 0x420ca118b18acccc 0xd0ec19cf8c5e6667 0x3a1d8339f18bcccc

def z1036 : W := mkw 0x0b0a1c02d58b8583 0x816143805ab170b0 0xdf0e1c0fff8f8183 0x7be1c381fff1f030

def z1037 : W := mkw 0x05b01d600ee44550 0x00b603ac01dc88aa 0xfff01ff00ffe67fe 0xfffe03fe01ffccff

def z1038 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xd70e1c0fff9f8003 0x7ae1c381fff3f000

def z1039 : W := mkw 0x0a0a0006d11b8287 0x81414000da237050 0x9f0e040fff9f8787 0x73e1c081fff3f0f0

def z1040 : W := mkw 0x182008449ddfefef 0xe304010893bbfdfd 0x180000000ffffffc 0x0300000001ffffff

def z1041 : W := mkw 0x10658acd8cd66776 0x420cb159b19accee 0xf0ed9bcf8c5e67ff 0xbe1db379f18bccff

def z1042 : W := mkw 0x0900bf7ef492afff 0xa12017efde9255ff 0x60001ffff00007fa 0x0c0003fffe0000ff

def z1043 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0xfffffbc00ffff807 0xffffff7801ffff00

def z1044 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x1ffde0000ffff804 0xa3ffbc0001ffff00

def z1045 : W := mkw 0x04b008400e600440 0x0096010801cc0088 0xfff01ff00fe007fe 0xfffe03fe01fc00ff

def z1046 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0ed9fff8c5e67ff 0xbe1db3fff18bccff

def z1047 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0fd9fff8c5e6667 0xfe1fb3fff18bcccc

def z1048 : W := mkw 0x279af73a63291000 0x04f35ee74c652200 0xaf13e63c73f1f807 0xd5e27cc78e7e3f00

def z1049 : W := mkw 0x10658ac98c464442 0x420cb1593188c888 0xf0ed9bcf8c5e6007 0xbe1db379f18bcc00

def z1050 : W := mkw 0x06df4000032d5000 0x00dbe8000065aa00 0x9f1fe0000fbff805 0x73e3fc0001f7ff00

def z1051 : W := mkw 0x1045828d80166226 0x4208b051b002cc44 0xe0ed9bcf805e6667 0xbc1db379f00bcccc

def z1052 : W := mkw 0x030a1c0245890500 0x0061438048b120a0 0xdf0e1c0fff9f8787 0x7be1c381fff3f0f0

def z1053 : W := mkw 0x10658acd9c56eeef 0x620cb159b38adddd 0xf8fffbcf8c7fffff 0xff1fff79f18fffff

def z1054 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xff0e1e3fff9f87ff 0x7fe1c3c7fff3f0ff

def z1055 : W := mkw 0x27dff7bb60800110 0x04fbfef76c100022 0xe7fffffff000019b 0xfcfffffffe000033

def z1056 : W := mkw 0x07df97ab40000000 0x00fbf2f568000000 0xe7ff9ffff0000003 0xfcfff3fffe000000

def z1057 : W := mkw 0x10658ac98c466462 0x420cb1593188cc8c 0xf0ed9bc38c4e6666 0xbe1db3787189cccc

def z1058 : W := mkw 0x279a753273299889 0x24f34ea64e653311 0x0f12643073a19998 0x41e24c860e743333

def z1059 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0ec1bcf8c4e0666 0xbe1d8379f189c0cc

def z1060 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xe7fffffff0607803 0xfcfffffffe0c0f00

def z1061 : W := mkw 0x27dff7bb61090000 0x04fbfef76c212000 0xf7ffffffff8e0003 0xfefffffffff1c000

def z1062 : W := mkw 0x0b0a1c06d59ba7a7 0x81614380dab374f4 0xdf0e1c0fffdfe7e7 0x7be1c381fffbfcfc

def z1063 : W := mkw 0x234fb7bb60000000 0x0469f6f76c000000 0xe7ef9ffff0000003 0xfcfdf3fffe000000

def z1064 : W := mkw 0x026f4000094d5000 0x004de8000129aa00 0x9fefe0000fdff805 0xf3fdfc0001fbff00

def z1065 : W := mkw 0x026f40000b6d5000 0x004de800016daa00 0x9f0fe0000ffff805 0x73e1fc0001ffff00

def z1066 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xff0e1e0fffdf87e7 0xffe1c3c1fffbf0fc

def z1067 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x97ffe0000f9ff801 0xf2fffc0001f3ff00

def z1068 : W := mkw 0x0000000410108285 0x0000000082021050 0xa813e63c7071ffff 0xd5027cc78e0e3fff

def z1069 : W := mkw 0x10658ac98c464442 0x420cb1593188c888 0x50ed99cf8c0e0001 0x2a1db339f181c000

def z1070 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf0e180fff9f8005 0x7be1c301fff3f000

def z1071 : W := mkw 0x2f9a753273a98191 0x85f34ea64e753032 0x0f12643073a18198 0x41e24c860e743033

def z1072 : W := mkw 0x079ab73a60000000 0x00f356e74c000000 0xe7fffffff0000003 0xfcfffffffe000000

def z1073 : W := mkw 0x25d5f7bb60000000 0x04babef76c000000 0x60e01ffff0000002 0x0c1c03fffe000000

def z1074 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x2813e63c7061fffa 0xc5027cc78e0c3fff

def z1075 : W := mkw 0x07dfd68b40000000 0x00fbfad168000000 0xe7ffffcff0000003 0xfcfffff9fe000000

def z1076 : W := mkw 0x0b0a1406d11b8287 0x81614280da237050 0xdf0e1c0fff9f8007 0x7be1c381fff3f000

def z1077 : W := mkw 0x2045a29b60000000 0x0408b4536c000000 0xe0ed9bcff0000003 0xbc1db379fe000000

def z1078 : W := mkw 0x00658acd8c520646 0x000cb159b18a40c8 0xf0ed9bcf8c5e0667 0xbe1db379f18bc0cc

def z1079 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x67fffbfff0000001 0xacffff7ffe000000

def z1080 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xff1e1e3fff9f8787 0xffe3c3c7fff3f0f0

def z1081 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xe7ed9ffff0000003 0xbcfdb3fffe000000

def z1082 : W := mkw 0x24f5e3b92a645000 0x049ebc77254c8a00 0x20f1e3f000000000 0x841e3c7e00000000

def z1083 : W := mkw 0x06ff41600b6d5050 0x00dfe82c016daa0a 0xbfffe7f00fffffff 0xf7fffcfe01ffffff

def z1084 : W := mkw 0x01201c400cc00540 0x00240388019800a8 0xfff01ff00fe007fe 0xfffe03fe01fc00ff

def z1085 : W := mkw 0x224fe29f711dfaad 0x2449fc53ee23bf55 0x000fe00ff01ff801 0x0001fc01fe03ff00

def z1086 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x9fffe40c7ffff807 0xf3fffc818fffff00

def z1087 : W := mkw 0x2900bfbff492afaf 0xa52017f7fe9255f5 0x60001ffff00007fa 0x0c0003fffe0000ff

def z1088 : W := mkw 0x2f9a753261890100 0x85f34ea64c312020 0x0712643073800000 0x40e24c860e700000

def z1089 : W := mkw 0x106582cd88566266 0x420cb059b10acc4c 0xe0ed9bcf805e6063 0xbc1db379f00bcc0c

def z1090 : W := mkw 0x106508c58c566666 0x420ca118b18acccc 0xd0ed99c38c5e6665 0xba1db338718bcccc

def z1091 : W := mkw 0x0b0a1c46d59b87c7 0x81614388dab370f8 0xff0e1fcfff9f87e7 0x7fe1c3f9fff3f0fc

def z1092 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0xbfffe6300ffff807 0xf7fffcc601ffff00

def z1093 : W := mkw 0x26ff41a10b6d5000 0x04dfe834216daa00 0x9fffe1c00ffff805 0xf3fffc3801ffff00

def z1094 : W := mkw 0x2100b7bb60000000 0x042016f76c000000 0xe0e01ffff0000002 0xbc1c03fffe000000

def z1095 : W := mkw 0x05b05d600ee01550 0x00b60bac01dc02aa 0xfff07ff00fe01ffe 0xfffe0ffe01fc03ff

def z1096 : W := mkw 0x10658acd9c56eeef 0x620cb159b38adddd 0xf8ef9fcffc7fffff 0xff1df3f9ff8fffff

def z1097 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x47ec19cff0000000 0x28fd8339fe000000

def z1098 : W := mkw 0x106508c18ee64552 0x420ca11831dcc8aa 0x58ec19c38fee07fc 0x2b1d833871fdc0ff

def z1099 : W := mkw 0x10458acd84122666 0x4208b159b08244cc 0xf0ed9bcf8c1e0667 0xbe1db379f183c0cc

def z1100 : W := mkw 0x0a0a0806d51b8687 0x81414100daa370d0 0xdf0e180fff9f8607 0x7be1c301fff3f0c0

def z1101 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xe7fffffff060007b 0xfcfffffffe0c000f

def z1102 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0x2813e6307071fffc 0xc5027cc60e0e3fff

def z1103 : W := mkw 0x0f9a152251898181 0x81f342a44a313030 0x0f12043073818180 0x41e240860e703030

def z1104 : W := mkw 0x0065828d08546224 0x000cb051a10a8c44 0xf0ed9bcf8c5e6667 0xbe1db379f18bcccc

def z1105 : W := mkw 0x26ff40834b6d5000 0x04dfe810696daa00 0x9fffe0038ffff805 0xf3fffc0071ffff00

def z1106 : W := mkw 0x106508c58c566666 0x420ca118b18acccc 0xf0ec1bc38c5e6666 0xbe1d8378718bcccc

def z1107 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf8ef9bcf8c5fe667 0xff1df379f18bfccc

def z1108 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0x50ec19c38c5e6004 0x2a1d8338718bcc00

def z1109 : W := mkw 0x27dff7bb61091000 0x04fbfef76c212200 0xe7fffffff0019803 0xfcfffffffe003300

def z1110 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0xe81ffe3ff071ffff 0xfd03ffc7fe0e3fff

def z1111 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x570e1c0fff9f8783 0x2ae1c381fff3f0f0

def z1112 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xe7fc1ffff0000002 0xfcff83fffe000000

def z1113 : W := mkw 0x1065aaddac566e6e 0x620cb55bb58acdcd 0xf0ed9bff8c5e667f 0xbe1db37ff18bcccf

def z1114 : W := mkw 0x279a552243291000 0x04f34aa448652200 0x0700000003800000 0x00e0000000700000

def z1115 : W := mkw 0x0065008108444000 0x000ca01021088800 0xd0ed99c38c5e6005 0xba1db338718bcc00

def z1116 : W := mkw 0x106508c58c564646 0x420ca118b18ac8c8 0xd0ed99cf8c5e6607 0xba1db339f18bccc0

def z1117 : W := mkw 0x27dfd7ab40000000 0x04fbfaf568000000 0xe7ef9fcff0000003 0xfcfdf3f9fe000000

def z1118 : W := mkw 0x030a1c06c4920706 0x00614380d89240e0 0xdf0e1c0fff9e0787 0x7be1c381fff3c0f0

def z1119 : W := mkw 0x34f5e3f92a647060 0x469ebc7f254c8e0c 0x20f1e3f000607860 0x841e3c7e000c0f0c

def z1120 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xe7fffffff0400667 0xfcfffffffe0800cc

def z1121 : W := mkw 0x27dff7bb610d5000 0x04fbfef76c21aa00 0xe7fffffff00e0003 0xfcfffffffe01c000

def z1122 : W := mkw 0x06ff41200b6d5000 0x00dfe824016daa00 0xbfffe3f00ffff805 0xf7fffc7e01ffff00

def z1123 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0x50ed99c38c4e6000 0xaa1db3387189cc00

def z1124 : W := mkw 0x279a753260000000 0x04f34ea64c000000 0xe7fe7ffff0000003 0xfcffcffffe000000

def z1125 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0x3ff007f00fe007fc 0xc7fe00fe01fc00ff

def z1126 : W := mkw 0x0045088584120606 0x0008a110b08240c0 0xd0ec19cf8c1e0607 0x3a1d8339f183c0c0

def z1127 : W := mkw 0x27df55a340000000 0x04fbeab468000000 0x47ee19cff0000001 0x28fdc339fe000000

def z1128 : W := mkw 0x1065828d88566226 0x420cb051b10acc44 0xf0ed9bcf8c5e6007 0xbe1db379f18bcc00

def z1129 : W := mkw 0x1065cacd8c567666 0x420cb959b18acecc 0xf0edfbcf8c5e7e67 0xbe1dbf79f18bcfcc

def z1130 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xeffffffff020019b 0xfdfffffffe040033

def z1131 : W := mkw 0x106508c18ee64552 0x420ca11831dcc8aa 0x50ec19c38f8e0000 0x2a1d833871f1c000

def z1132 : W := mkw 0x25d5f7bb60000000 0x04babef76c000000 0xe0f3fffff0000003 0xdc1e7ffffe000000

def z1133 : W := mkw 0x24f5e3b92a647828 0x249ebc77254c8f05 0x20f1e3f000607878 0x841e3c7e000c0f0f

def z1134 : W := mkw 0x0000080484120606 0x00000100908240c0 0xf0ec1bcf8c1e0607 0xbe1d8379f183c0c0

def z1135 : W := mkw 0x0b0a1c06d59bafaf 0xa1614380dab375f5 0xff1e1e3fffffffff 0xffe3c3c7ffffffff

def z1136 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf0e1c0fffff87ff 0x7be1c381fffff0ff

def z1137 : W := mkw 0x0b0a1c02c58b0502 0x8161438058b160a0 0xdf0e1c0fff9f8007 0x7be1c381fff3f000

def z1138 : W := mkw 0x124fe29db11ffaaf 0x6249fc53b623ff55 0x000fe00ff01ff801 0x0001fc01fe03ff00

def z1139 : W := mkw 0x27df55a340000000 0x04fbeab468000000 0xe7fe1ffff0000003 0xfcffc3fffe000000

def z1140 : W := mkw 0x0900be1ef492afaf 0xa12017c3de9255f5 0x40001c0ff0000782 0x08000381fe0000f0

def z1141 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xeffffffff0118007 0xfdfffffffe023000

def z1142 : W := mkw 0x2145b7bb60000000 0x0428b6f76c000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z1143 : W := mkw 0x01001c0494928787 0x00200380929250f0 0xdf0e1c0fff9f8787 0x7be1c381fff3f0f0

def z1144 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf1e1c3fffbf879f 0x7be3c387fff7f0f3

def z1145 : W := mkw 0x1065aaddac566e6e 0x620cb55bb58acdcd 0xf8fdffff8c7e7fff 0xff1fbffff18fcfff

def z1146 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x9fffe0000ffffffd 0xf3fffc0001ffffff

def z1147 : W := mkw 0x2590b7bb60000000 0x04b216f76c000000 0x60f01ffff0000002 0x8c1e03fffe000000

def z1148 : W := mkw 0x0b0a1c06d59bafaf 0xa1614380dab375f5 0xdf0e1c0fff9f87ff 0x7be1c381fff3f0ff

def z1149 : W := mkw 0x2f9a753271898989 0xa5f34ea64e313131 0x0f12643073a19998 0x41e24c860e743333

def z1150 : W := mkw 0x0000a21820000000 0x0000144304000000 0xa813e63c7071ffff 0xd5027cc78e0e3fff

def z1151 : W := mkw 0x102008448c566666 0x42040108918acccc 0xf0ec1bcf8c5e6667 0xbe1d8379f18bcccc

def z1152 : W := mkw 0x1065aaddac566666 0x420cb55bb58acccc 0xf8fffffffc7e67ff 0xff1fffffff8fccff

def z1153 : W := mkw 0x0065a29d3854eaad 0x200cb453a70a9d55 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z1154 : W := mkw 0x106508c59c56c6c7 0x420ca118b38ad8d8 0xd8ee1dcffc1f8787 0x7b1dc3b9ff83f0f0

def z1155 : W := mkw 0x0b0a1d26d59b8797 0x816143a4dab370f2 0xdf0e1c3fff9f879f 0x7be1c387fff3f0f3

def z1156 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0xdf1e1c0fffff8787 0xfbe3c381fffff0f0

def z1157 : W := mkw 0x00208a4c8c522666 0x00041149918a44cc 0xf0ed9bcf8c5e6667 0xbe1db379f18bcccc

def z1158 : W := mkw 0x2590b7bb60000000 0x04b216f76c000000 0x67e01ffff0000002 0x2cfc03fffe000000

def z1159 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0ec1bcf8c1e0667 0x3e1d8379f183c0cc

def z1160 : W := mkw 0x1065aaddbc56eeef 0x620cb55bb78adddd 0xf0fdfffffc7e7fff 0xbe1fbfffff8fcfff

def z1161 : W := mkw 0x10658ac98c466462 0x420cb1593188cc8c 0x70ec1bc38c0e0060 0x2e1d83787181c00c

def z1162 : W := mkw 0x1065aaddac566666 0x420cb55bb58acccc 0xf8fffffffc7ffe67 0xff1fffffff8fffcc

def z1163 : W := mkw 0x06ba00000b690000 0x00d74000016d2000 0x9fffe0000ffff805 0xf3fffc0001ffff00

def z1164 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0fdfbcf8c7e7e67 0xbe1fbf79f18fcfcc

def z1165 : W := mkw 0x0590152240000000 0x00b202a448000000 0xe7f01ffff0000002 0xfcfe03fffe000000

def z1166 : W := mkw 0x10658acd9c56e6e7 0x420cb159b38adcdc 0xf8ed9bcf8c5fe7e7 0xbf1db379f18bfcfc

def z1167 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xf0ed9bcf8c0e0663 0xbe1db379f181c0cc

def z1168 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xe7fffffff00007fb 0xfcfffffffe0000ff

def z1169 : W := mkw 0x106508c18c464442 0x420ca1183188c888 0xd0ec19c38c4e0004 0xba1d83387189c000

def z1170 : W := mkw 0x030a140240000000 0x0061428048000000 0xe7ee1fcff0000003 0xfcfdc3f9fe000000

def z1171 : W := mkw 0x27dff7bb60045000 0x04fbfef76c008a00 0xe7fffffff0007803 0xfcfffffffe000f00

def z1172 : W := mkw 0x06ff40000b6d5000 0x00dfe800016daa00 0x9fffe4000fffff87 0xf3fffc8001fffff0

def z1173 : W := mkw 0x10658acd8e766666 0x420cb159b1cecccc 0xf8ed9bcf8ffe6667 0xbf1db379f1ffcccc

def z1174 : W := mkw 0x27dff7bb60002828 0x24fbfef76c000505 0xeffffffff071f87f 0xfdfffffffe0e3f0f

def z1175 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0x67fe7ffff0000002 0x6cffcffffe000000

def z1176 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xeffffffff0600007 0xfdfffffffe0c0000

def z1177 : W := mkw 0x26dfe3bb60000000 0x04dbfc776c000000 0xe0fffbfff0000003 0xbc1fff7ffe000000

def z1178 : W := mkw 0x27dff7bb60002828 0x24fbfef76c000505 0xeffffffff0607fff 0xfdfffffffe0c0fff

def z1179 : W := mkw 0x27dff7bb632d5000 0x04fbfef76c65aa00 0xeffffffff3bff803 0xfdfffffffe77ff00

def z1180 : W := mkw 0x0b0a1d66d59b87d7 0x816143acdab370fa 0xdf0e1dcfff9f8787 0x7be1c3b9fff3f0f0

def z1181 : W := mkw 0x0065828908444000 0x000cb05121088800 0xf0ed9bcf8c0e0003 0xbe1db379f181c000

def z1182 : W := mkw 0x27dff7bb60800100 0x04fbfef76c100020 0xeffffffff3800183 0xfdfffffffe700030

def z1183 : W := mkw 0x10658acd9c56eeef 0x620cb159b38adddd 0xf8fd9fff8c7fffff 0xff1fb3fff18fffff

def z1184 : W := mkw 0x1065aaddac566e6e 0x620cb55bb58acdcd 0xf0edfbcf8c5e7e67 0xbe1dbf79f18bcfcc

def z1185 : W := mkw 0x00458a8d84122626 0x0008b151b08244c4 0xf0ed9bcf8c5e6667 0xbe1db379f18bcccc

def z1186 : W := mkw 0x10658acd9c56e6e7 0x420cb159b38adcdc 0xf8ff9ffffc7fe7ff 0xff1ff3ffff8ffcff

def z1187 : W := mkw 0x106582c908446060 0x420cb05921088c0c 0xf0ed9bcf8c5e6067 0xbe1db379f18bcc0c

def z1188 : W := mkw 0x1065aaddac566666 0x420cb55bb58acccc 0xf0effbcffc5e6667 0xbe1dff79ff8bcccc

def z1189 : W := mkw 0x10658acd8c566666 0x420cb159b18acccc 0xffed9bcf8fde6667 0xfffdb379f1fbcccc

def z1190 : W := mkw 0x0b0a1c06d59b8787 0x81614380dab370f0 0x1f0e040fff9f8785 0x43e1c081fff3f0f0

def z1191 : W := mkw 0x0fff5d62cfef5552 0x81ffebac59fdeaaa 0x57ec19c38f8e0000 0x2afd833871f1c000

def z1192 : W := mkw 0x25d5f7bb60000000 0x04babef76c000000 0xe7f1fffff0000002 0xfcfe3ffffe000000

def z1193 : W := mkw 0x082008449ddb87c7 0x8104010893bb70f8 0x180000000fdf87e4 0x0300000001fbf0fc

def z1194 : W := mkw 0x05b01d600ee45550 0x00b603ac01dc8aaa 0xfff01ff00fe07ffe 0xfffe03fe01fc0fff

def z1195 : W := mkw 0x10658ac98c464442 0x420cb1593188c888 0x70ec1bcf8c0e0002 0x2e1d8379f181c000

def z1196 : W := mkw 0x05b01d600ee00550 0x00b603ac01dc00aa 0xf7f01ff00f8007fa 0xfefe03fe01f000ff

def z1197 : W := mkw 0x3065eaddac566666 0x460cbd5bb58acccc 0xf0edfbcf8c5e6667 0xbe1dbf79f18bcccc

def z1198 : W := mkw 0x0145968b40000000 0x0028b2d168000000 0xe0ed9fcff0000003 0xbc1db3f9fe000000

def z1199 : W := mkw 0x27dff7bb60000000 0x04fbfef76c000000 0xe7effbcff0000003 0xbcfdff79fe000000

def z1200 : W := mkw 0x0000a21c3010aaad 0x2000144386021555 0xe8f3fffc7071ffff 0xfd1e7fff8e0e3fff

def z1201 : W := mkw 0x002008448c520646 0x00040108918a40c8 0xd0ec19cf8c1e0607 0x3a1d8339f183c0c0

def z1202 : W := mkw 0x0a0a0006d11b8287 0x81414000da237050 0x170e000fff9f8001 0x22e1c001fff3f000

def z1203 : W := mkw 0x002008449c5286c7 0x00040108938a50d8 0xf8fe1ffffc7f87ff 0xff1fc3ffff8ff0ff

def z1204 : W := mkw 0x10658acd8e767666 0x420cb159b1cececc 0xf0ed9bcf8c7e7e67 0xbe1db379f18fcfcc

def z1205 : W := mkw 0x082008449ef287d7 0x8104010893de50fa 0x180000000fe007fc 0x0300000001fc00ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z8,z6]),(0,[z0,z9,z2,z3,z4,z10,z6]),(0,[z0,z11,z2,z3,z4,z10,z6])],[(0,[z0,z2,z12,z3,z4,z8,z6]),(0,[z0,z13,z2,z3,z4,z10,z6]),(0,[z14,z0,z2,z15,z4,z10,z6]),(0,[z14,z2,z3,z15,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z16]),(0,[z0,z17,z3,z4,z10,z6,z18]),(0,[z0,z19,z2,z3,z4,z20,z6]),(0,[z0,z2,z3,z4,z10,z21,z6]),(0,[z22,z0,z2,z3,z4,z10,z6])],[(0,[z0,z23,z2,z3,z4,z10,z5]),(1,[z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z25,z10,z6]),(0,[z0,z26,z2,z3,z4,z27,z10])],[(0,[z28,z0,z29,z3,z4,z10,z6]),(0,[z30,z0,z2,z3,z4,z10,z6]),(0,[z0,z31,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z32,z4,z8,z6]),(0,[z0,z2,z3,z33,z4,z8,z6]),(0,[z0,z2,z3,z34,z4,z10,z6]),(0,[z35,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z36])],[(0,[z37,z29,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z38,z10,z6]),(0,[z0,z2,z3,z39,z4,z10,z6]),(0,[z0,z40,z2,z3,z4,z10,z6]),(0,[z22,z0,z2,z3,z4,z41,z6])],[(0,[z0,z42,z2,z3,z4,z43,z6]),(0,[z0,z2,z3,z4,z44,z10,z6]),(0,[z0,z2,z45,z3,z4,z10,z6]),(0,[z46,z0,z2,z3,z4,z10,z6])],[(0,[z47,z0,z2,z3,z4,z10,z6]),(0,[z0,z48,z2,z3,z4,z10,z6])],[(0,[z0,z49,z2,z3,z4,z10,z6]),(0,[z0,z2,z32,z34,z4,z10,z6]),(0,[z0,z2,z3,z4,z50,z10,z6]),(1,[z22,z0,z2,z3,z51,z6])]],
   [[],[(1,[z28,z12,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z52,z6]),(0,[z2,z53,z3,z15,z4,z10,z6]),(0,[z0,z54,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z55,z6]),(0,[z0,z1,z2,z3,z4,z10,z56])],[(0,[z57,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z58]),(0,[z0,z2,z3,z4,z59,z10,z6]),(0,[z0,z60,z2,z3,z4,z10,z6])],[(0,[z0,z2,z61,z3,z4,z8,z6]),(0,[z0,z62,z2,z3,z4,z10,z6]),(0,[z63,z0,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z64,z4,z10,z6]),(0,[z37,z0,z2,z3,z4,z65,z6]),(0,[z0,z2,z3,z4,z10,z66,z6]),(0,[z0,z2,z3,z4,z67,z10,z6])],[(0,[z0,z2,z3,z4,z10,z68,z6]),(0,[z37,z0,z29,z3,z4,z10,z6]),(0,[z69,z0,z2,z3,z4,z10,z6]),(0,[z70,z0,z2,z3,z4,z8,z6]),(0,[z0,z71,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z72,z5,z6]),(0,[z0,z73,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z10,z6,z74]),(0,[z0,z2,z3,z4,z8,z75,z6]),(0,[z0,z76,z2,z32,z4,z10,z6])]],
   [[(0,[z0,z12,z3,z32,z4,z10,z6]),(0,[z0,z2,z3,z77,z4,z10,z6]),(0,[z14,z0,z78,z3,z4,z10,z6]),(0,[z79,z0,z2,z3,z4,z5,z6]),(0,[z80,z0,z2,z3,z4,z8,z6]),(0,[z0,z81,z26,z2,z3,z10,z6]),(0,[z0,z82,z2,z3,z4,z10,z6])],[(0,[z28,z37,z2,z3,z4,z10,z6]),(0,[z14,z0,z2,z3,z4,z10,z6]),(0,[z0,z83,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z84])],[(0,[z85,z0,z2,z3,z4,z86,z6]),(0,[z0,z2,z3,z87,z4,z10,z6]),(0,[z88,z0,z89,z2,z3,z4,z10]),(0,[z0,z2,z3,z4,z10,z90,z6]),(0,[z0,z2,z3,z91,z4,z10,z6])],[(0,[z0,z92,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z93,z10,z6]),(1,[z0,z81,z2,z94,z10,z6]),(0,[z0,z2,z3,z95,z41,z10,z6])],[(0,[z0,z2,z3,z4,z96,z10,z6]),(0,[z0,z2,z3,z4,z97,z10,z6]),(0,[z0,z2,z3,z4,z98,z10,z6])],[(0,[z99,z0,z2,z3,z4,z10,z6]),(0,[z85,z2,z3,z100,z4,z10,z6]),(0,[z88,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z101,z6]),(0,[z0,z102,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z103,z10,z6])],[(0,[z0,z104,z2,z3,z4,z10,z6]),(0,[z105,z0,z2,z3,z4,z10,z6])],[(1,[z0,z2,z3,z4,z106,z6]),(1,[z0,z2,z3,z107,z10,z6]),(0,[z0,z2,z3,z108,z4,z10,z6]),(0,[z109,z0,z2,z3,z4,z10,z6]),(1,[z0,z26,z2,z3,z10,z110])]],
   [[(0,[z111,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z112,z6]),(0,[z113,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z114,z3,z4,z10,z6]),(0,[z115,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z116,z10,z6]),(0,[z0,z89,z2,z3,z4,z27,z6]),(0,[z117,z0,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z5,z6,z118]),(0,[z119,z0,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z120,z4,z10,z6]),(0,[z121,z0,z2,z3,z4,z5,z6]),(0,[z0,z122,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z123,z6]),(0,[z0,z2,z3,z4,z10,z124,z6]),(0,[z0,z2,z3,z95,z4,z41,z6]),(0,[z0,z2,z3,z4,z125,z10,z6])],[(0,[z0,z2,z3,z4,z126,z5,z6]),(0,[z22,z0,z42,z2,z3,z4,z6])],[(0,[z0,z2,z3,z34,z100,z10,z6]),(0,[z0,z2,z3,z4,z127,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z128])],[(0,[z0,z81,z2,z3,z98,z10,z6]),(0,[z0,z2,z3,z4,z10,z129,z6]),(0,[z0,z2,z3,z130,z4,z10,z6]),(0,[z0,z73,z2,z3,z4,z10,z131]),(0,[z0,z73,z26,z2,z3,z4,z10]),(0,[z132,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z133,z6])],[(0,[z0,z2,z3,z4,z10,z134,z6]),(0,[z135,z0,z2,z3,z4,z136,z6]),(0,[z0,z2,z3,z137,z4,z10,z6]),(0,[z0,z2,z3,z138,z4,z10,z6]),(1,[z0,z2,z3,z4,z10,z139]),(0,[z22,z0,z2,z3,z4,z51,z6]),(0,[z0,z2,z3,z33,z4,z27,z10])],[(0,[z0,z2,z3,z100,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z6,z140]),(0,[z0,z141,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z142,z4,z10,z6]),(0,[z0,z2,z143,z3,z4,z10,z6])]],
   [[(1,[z0,z2,z3,z4,z134,z6]),(0,[z0,z2,z3,z4,z8,z6,z18]),(0,[z0,z144,z2,z3,z4,z10,z6]),(0,[z0,z2,z145,z3,z4,z10,z6])],[(0,[z0,z146,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z8,z147,z6]),(0,[z0,z81,z148,z2,z4,z10,z6])],[(0,[z0,z149,z2,z3,z4,z10,z6]),(1,[z0,z148,z2,z34,z10,z6]),(0,[z0,z2,z3,z4,z10,z150,z6]),(0,[z0,z2,z151,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z8,z5,z6]),(0,[z0,z2,z3,z4,z5,z43,z6]),(0,[z0,z148,z2,z3,z98,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z152]),(0,[z0,z2,z3,z4,z153,z10,z6]),(0,[z0,z154,z2,z3,z4,z10,z6])],[(0,[z0,z76,z12,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z20,z8,z6]),(0,[z0,z2,z155,z3,z4,z10,z6])],[(0,[z156,z0,z2,z3,z4,z10,z6]),(0,[z0,z26,z2,z3,z4,z5,z6]),(0,[z0,z54,z2,z3,z95,z4,z6]),(0,[z0,z73,z2,z3,z33,z4,z10]),(0,[z157,z0,z2,z3,z4,z10,z6])],[(0,[z28,z0,z2,z3,z158,z10,z6]),(0,[z0,z2,z3,z4,z159,z10,z6]),(0,[z0,z54,z2,z3,z4,z10,z139])],[(0,[z0,z2,z160,z3,z4,z10,z6]),(0,[z0,z26,z2,z3,z4,z10,z140]),(0,[z0,z2,z3,z4,z10,z161,z6]),(1,[z0,z2,z3,z4,z27,z162])]],
   [[(0,[z14,z0,z2,z3,z4,z163,z6]),(0,[z0,z164,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z165,z10,z6]),(0,[z0,z2,z3,z4,z10,z166,z6]),(0,[z0,z2,z167,z3,z4,z10,z6]),(0,[z0,z82,z2,z3,z10,z6,z56])],[(0,[z0,z2,z3,z168,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z169]),(0,[z0,z2,z3,z4,z170,z10,z6]),(0,[z0,z171,z2,z3,z4,z10,z6])],[(1,[z0,z2,z3,z4,z10,z172]),(0,[z0,z54,z2,z3,z4,z10,z6]),(0,[z173,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z174,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z10,z6,z175]),(0,[z0,z76,z2,z3,z4,z5,z6]),(0,[z80,z0,z2,z3,z4,z27,z10]),(0,[z176,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z177,z6])],[(0,[z0,z2,z3,z178,z4,z10,z6]),(0,[z88,z2,z3,z4,z10,z179,z6]),(0,[z0,z89,z2,z3,z4,z43,z6]),(0,[z0,z2,z3,z180,z4,z10,z6]),(0,[z0,z2,z3,z4,z181,z10,z6]),(0,[z182,z0,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z183,z5,z6]),(0,[z0,z2,z3,z4,z10,z184,z6])],[(0,[z79,z85,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z185]),(0,[z88,z0,z2,z3,z4,z10,z179]),(0,[z0,z186,z2,z3,z4,z10,z6]),(0,[z0,z187,z2,z3,z4,z10,z6])],[(0,[z188,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z72,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z110]),(0,[z0,z2,z3,z4,z10,z6,z189])]],
   [[(0,[z0,z190,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z15,z4,z8,z6]),(0,[z0,z2,z3,z191,z4,z10,z6]),(0,[z22,z0,z2,z3,z10,z51,z6]),(0,[z0,z2,z3,z4,z10,z192,z6])],[(0,[z79,z0,z2,z3,z4,z10,z6]),(1,[z88,z2,z3,z4,z10,z179]),(0,[z0,z2,z3,z4,z193,z10,z6]),(1,[z0,z2,z3,z4,z6,z189])],[(0,[z14,z0,z2,z3,z194,z10,z6]),(0,[z195,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z196,z10,z6])],[(0,[z0,z2,z3,z4,z197,z10,z6]),(0,[z0,z198,z2,z3,z4,z10,z6]),(0,[z199,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z200,z6])],[(1,[z135,z2,z53,z4,z10,z6]),(0,[z79,z0,z2,z3,z4,z201,z6]),(0,[z2,z3,z100,z4,z72,z10,z6]),(0,[z0,z202,z2,z3,z203,z10,z6]),(0,[z0,z2,z3,z204,z4,z10,z6]),(0,[z0,z2,z3,z95,z4,z51,z6])],[(0,[z28,z0,z2,z205,z4,z10,z6]),(0,[z135,z0,z2,z3,z4,z8,z6]),(0,[z0,z206,z2,z53,z4,z10,z6]),(1,[z0,z2,z3,z4,z200,z6]),(0,[z207,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z27,z10,z18]),(0,[z0,z2,z3,z4,z10,z6,z208]),(0,[z0,z209,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z210])],[(0,[z88,z0,z2,z3,z4,z10,z6]),(0,[z211,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z212,z6]),(0,[z0,z2,z3,z4,z10,z213,z6]),(0,[z0,z214,z2,z3,z4,z10,z6])],[(0,[z0,z2,z215,z3,z4,z5,z6]),(0,[z0,z2,z3,z216,z4,z10,z6]),(0,[z0,z2,z217,z3,z4,z10,z6]),(0,[z0,z218,z2,z3,z4,z6,z110]),(0,[z0,z89,z2,z3,z4,z6,z185])]],
   [[(0,[z219,z0,z2,z3,z4,z10,z6]),(0,[z0,z23,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z220,z10,z6]),(0,[z0,z2,z3,z4,z221,z10,z6])],[(1,[z0,z2,z3,z222,z10,z6]),(1,[z0,z2,z3,z4,z163,z6]),(0,[z113,z0,z2,z3,z4,z10,z6]),(1,[z70,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z95,z4,z5,z6]),(0,[z0,z206,z3,z32,z4,z10,z6]),(0,[z223,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z185])],[(0,[z28,z0,z2,z3,z4,z224,z6]),(0,[z225,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z226,z3,z4,z10,z6]),(0,[z227,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z110])],[(0,[z135,z0,z2,z34,z4,z10,z6]),(0,[z121,z0,z2,z3,z4,z10,z6]),(0,[z80,z0,z2,z3,z4,z228,z6]),(0,[z0,z2,z3,z4,z10,z229,z6]),(0,[z0,z230,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z231,z10,z6])],[(1,[z0,z42,z3,z4,z43,z6]),(1,[z0,z54,z3,z4,z183,z6]),(0,[z0,z81,z2,z3,z94,z10,z6])],[(0,[z0,z2,z3,z4,z10,z6,z232]),(0,[z0,z54,z2,z3,z4,z183,z6]),(0,[z0,z2,z233,z3,z4,z10,z6])],[(0,[z0,z206,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z234,z6]),(0,[z0,z235,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z10,z6,z6]),(0,[z0,z2,z3,z236,z4,z10,z6]),(0,[z0,z148,z2,z34,z4,z10,z6])],[(0,[z0,z2,z12,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z179,z6]),(0,[z0,z237,z2,z3,z4,z10,z6]),(0,[z0,z238,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z4,z10,z239]),(0,[z0,z240,z2,z3,z4,z10,z6]),(0,[z0,z241,z2,z3,z4,z10,z6])]],
   [[(0,[z0,z2,z3,z100,z4,z10,z6]),(1,[z79,z2,z3,z72,z10,z6]),(0,[z0,z242,z2,z3,z4,z5,z6]),(0,[z0,z0,z2,z3,z4,z8,z6]),(0,[z0,z243,z2,z3,z98,z10,z6]),(0,[z244,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z245,z10,z6]),(0,[z0,z2,z246,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z247,z6])],[(0,[z0,z2,z3,z32,z4,z5,z6]),(0,[z0,z2,z3,z33,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z248,z6])],[(0,[z249,z0,z2,z3,z4,z10,z6]),(0,[z0,z148,z2,z3,z94,z10,z6])],[(0,[z0,z250,z2,z3,z4,z10,z6]),(0,[z0,z251,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z194,z10,z6]),(0,[z0,z2,z3,z4,z10,z252,z6]),(0,[z0,z2,z3,z33,z4,z10,z140]),(0,[z0,z2,z3,z4,z253,z10,z6]),(0,[z0,z254,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z8,z10,z6]),(1,[z0,z2,z3,z10,z255,z6]),(0,[z0,z256,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z158,z10,z6]),(0,[z0,z202,z2,z3,z4,z8,z6])],[(0,[z85,z0,z2,z3,z4,z10,z257]),(0,[z0,z2,z3,z4,z258,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z259]),(0,[z0,z260,z2,z3,z4,z10,z6]),(0,[z0,z1,z2,z215,z4,z10,z6]),(1,[z0,z2,z3,z95,z41,z6]),(0,[z0,z261,z2,z3,z4,z10,z6])],[(0,[z0,z2,z262,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z8,z41,z6]),(0,[z0,z2,z3,z4,z10,z6,z263]),(0,[z0,z2,z3,z4,z264,z10,z6]),(0,[z0,z2,z3,z4,z10,z172,z6]),(0,[z0,z81,z2,z3,z4,z10,z265]),(0,[z0,z2,z3,z4,z266,z10,z6])]],
   [[(0,[z0,z76,z267,z3,z4,z10,z6]),(0,[z0,z2,z3,z268,z4,z10,z6])],[(0,[z0,z269,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z270,z4,z10,z6]),(0,[z2,z3,z4,z8,z10,z5,z6]),(0,[z0,z2,z271,z3,z4,z10,z6]),(0,[z88,z0,z2,z3,z4,z200,z6]),(1,[z0,z272,z2,z3,z4,z6])],[(0,[z79,z0,z2,z3,z100,z10,z6]),(0,[z0,z2,z3,z4,z8,z6,z56]),(0,[z0,z2,z273,z3,z4,z10,z6]),(0,[z0,z2,z3,z274,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z275,z6])],[(0,[z0,z29,z2,z3,z4,z8,z6]),(0,[z70,z0,z2,z3,z4,z5,z6]),(0,[z88,z0,z2,z3,z276,z10,z6]),(0,[z0,z17,z2,z3,z4,z10,z18])],[(0,[z0,z277,z2,z3,z4,z10,z6]),(0,[z0,z76,z2,z3,z4,z10,z6])],[(0,[z28,z0,z2,z3,z4,z8,z6]),(0,[z278,z0,z2,z3,z4,z10,z6]),(0,[z14,z135,z2,z3,z4,z10,z6]),(0,[z0,z279,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z280,z6]),(1,[z0,z243,z3,z98,z10,z6]),(0,[z0,z281,z2,z3,z4,z10,z6]),(0,[z0,z282,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z75,z56])],[(0,[z0,z2,z3,z4,z10,z6,z283]),(0,[z80,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z284,z8,z6]),(0,[z0,z2,z3,z4,z183,z10,z6])],[(0,[z0,z206,z2,z15,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z285]),(0,[z0,z286,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z4,z10,z287])]],
   [[(0,[z288,z0,z2,z3,z4,z10,z6]),(0,[z88,z80,z2,z3,z4,z10,z6]),(0,[z80,z0,z2,z3,z4,z10,z140]),(0,[z0,z2,z3,z4,z10,z289,z6]),(0,[z0,z2,z3,z4,z290,z10,z6])],[(0,[z28,z0,z2,z3,z291,z10,z6]),(0,[z292,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z293]),(0,[z0,z2,z3,z4,z24,z10,z6]),(0,[z0,z2,z3,z294,z4,z10,z6])],[(0,[z295,z0,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z4,z10,z265]),(0,[z0,z2,z3,z296,z4,z10,z6])],[(0,[z0,z2,z3,z4,z10,z6,z257]),(0,[z85,z0,z2,z3,z4,z5,z6]),(0,[z0,z297,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z179,z18]),(0,[z0,z298,z2,z3,z4,z10,z6]),(0,[z0,z89,z19,z2,z3,z4,z6])],[(1,[z0,z2,z299,z4,z10,z6]),(0,[z0,z2,z3,z4,z300,z5,z6]),(0,[z0,z301,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z302,z10,z6]),(0,[z0,z303,z2,z3,z4,z10,z6])],[(0,[z14,z0,z304,z3,z4,z10,z6]),(0,[z0,z42,z2,z3,z4,z8,z6]),(0,[z0,z267,z2,z32,z4,z10,z6]),(0,[z0,z2,z3,z4,z305,z10,z6]),(0,[z306,z0,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z307,z4,z10,z6]),(0,[z0,z2,z3,z276,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z308]),(0,[z0,z89,z2,z3,z4,z10,z18]),(0,[z0,z81,z2,z3,z4,z10,z309])],[(0,[z0,z2,z3,z4,z310,z10,z6])]],
   [[(0,[z0,z2,z3,z4,z10,z280,z6]),(0,[z0,z311,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z312,z6]),(0,[z0,z2,z3,z4,z10,z147,z140]),(0,[z0,z81,z206,z2,z4,z10,z6]),(0,[z313,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z215,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z314,z10,z6]),(0,[z0,z2,z3,z4,z27,z162,z6])],[(0,[z0,z2,z315,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z316,z6]),(0,[z22,z0,z54,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z10,z317,z6]),(0,[z0,z2,z3,z4,z318,z10,z6])],[(0,[z0,z2,z3,z4,z5,z319,z6]),(0,[z320,z0,z2,z3,z4,z10,z6]),(0,[z0,z42,z3,z4,z10,z43,z6]),(0,[z0,z2,z3,z4,z10,z321,z6]),(0,[z0,z2,z3,z95,z4,z10,z6])],[(0,[z0,z2,z3,z4,z27,z8,z6]),(0,[z88,z0,z2,z3,z38,z10,z6]),(0,[z0,z2,z3,z4,z322,z10,z6]),(0,[z0,z323,z2,z3,z4,z10,z6])],[(0,[z0,z324,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z325,z6]),(0,[z0,z326,z2,z3,z4,z10,z6])],[(1,[z0,z2,z3,z4,z93,z6]),(1,[z0,z202,z3,z203,z10,z6]),(0,[z0,z19,z2,z4,z10,z325,z6])],[(0,[z0,z327,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z328,z6]),(1,[z0,z329,z2,z4,z10,z6]),(0,[z0,z2,z4,z20,z10,z325,z6]),(0,[z0,z2,z3,z33,z4,z10,z110]),(0,[z0,z2,z3,z4,z10,z330,z6])],[(0,[z0,z2,z3,z4,z331,z10,z6]),(0,[z0,z26,z2,z3,z100,z10,z6]),(0,[z0,z7,z2,z3,z4,z10,z6]),(0,[z0,z206,z2,z3,z4,z10,z6]),(0,[z0,z3,z4,z183,z10,z43,z6]),(0,[z0,z2,z3,z4,z27,z10,z56])]],
   [[(0,[z0,z2,z12,z3,z4,z10,z6]),(0,[z0,z76,z29,z3,z4,z10,z6]),(0,[z135,z0,z81,z2,z4,z10,z6]),(1,[z0,z2,z3,z4,z328,z6]),(0,[z0,z2,z3,z100,z10,z75,z6]),(0,[z0,z332,z2,z3,z4,z5,z6]),(0,[z0,z333,z2,z3,z4,z10,z6])],[(0,[z0,z334,z2,z3,z4,z10,z6]),(0,[z0,z2,z335,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z336,z6]),(0,[z0,z242,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z8,z51,z6]),(1,[z0,z2,z3,z4,z10,z309]),(0,[z0,z337,z2,z3,z4,z10,z6])],[(0,[z0,z304,z2,z3,z4,z10,z6]),(0,[z338,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z20,z5,z6]),(0,[z0,z2,z3,z203,z4,z8,z6]),(0,[z0,z2,z3,z32,z4,z10,z6]),(0,[z0,z2,z3,z4,z43,z162,z6]),(0,[z0,z2,z3,z339,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z340]),(0,[z0,z2,z3,z33,z4,z10,z6])],[(0,[z0,z2,z3,z4,z41,z5,z6]),(0,[z0,z2,z3,z4,z341,z10,z6])],[(0,[z0,z81,z2,z3,z203,z10,z6]),(0,[z0,z1,z2,z3,z4,z10,z6])],[(0,[z342,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z343,z4,z10,z6]),(0,[z0,z344,z2,z3,z4,z10,z6]),(0,[z0,z2,z45,z3,z4,z10,z239]),(0,[z0,z2,z3,z4,z10,z345,z6])],[(0,[z0,z2,z3,z4,z10,z112,z6]),(1,[z0,z304,z3,z4,z10,z6]),(0,[z0,z2,z3,z346,z4,z10,z6]),(0,[z0,z2,z3,z4,z347,z10,z5]),(0,[z0,z202,z2,z138,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z348]),(0,[z0,z2,z3,z349,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z350])],[(0,[z0,z2,z3,z34,z72,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z118]),(0,[z0,z2,z3,z4,z351,z8,z6]),(0,[z0,z2,z3,z4,z10,z352,z6]),(0,[z0,z353,z2,z3,z4,z10,z6]),(0,[z354,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z325,z6]),(0,[z0,z2,z215,z3,z4,z10,z131]),(0,[z0,z2,z3,z4,z10,z6,z355])]],
   [[(1,[z0,z2,z205,z4,z10,z6]),(0,[z0,z2,z3,z203,z72,z10,z6]),(0,[z0,z81,z2,z4,z94,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z356])],[(0,[z357,z0,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z4,z136,z6]),(0,[z0,z329,z2,z3,z4,z10,z6])],[(0,[z0,z2,z61,z3,z4,z10,z6]),(0,[z0,z148,z2,z3,z203,z10,z6]),(0,[z0,z2,z3,z4,z10,z358,z6]),(0,[z0,z359,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z360,z6]),(0,[z0,z2,z3,z361,z4,z10,z6])],[(0,[z14,z0,z2,z3,z222,z10,z6]),(0,[z0,z2,z15,z32,z4,z10,z6]),(0,[z0,z362,z2,z3,z4,z10,z6]),(0,[z363,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z6,z189,z110])],[(0,[z0,z364,z2,z3,z4,z10,z6]),(0,[z70,z0,z2,z3,z4,z10,z6]),(0,[z365,z0,z2,z3,z4,z10,z6]),(0,[z0,z73,z2,z3,z4,z8,z6]),(0,[z0,z267,z3,z32,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z366,z6]),(1,[z0,z2,z3,z4,z10,z367]),(0,[z0,z164,z202,z2,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z368]),(0,[z0,z2,z3,z369,z4,z10,z6]),(1,[z0,z19,z2,z4,z325,z6]),(0,[z0,z2,z3,z370,z4,z10,z6])],[(1,[z0,z2,z3,z4,z224,z6]),(0,[z28,z2,z12,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z371,z6]),(0,[z0,z2,z3,z372,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z373,z6]),(0,[z0,z2,z3,z374,z4,z10,z6]),(0,[z375,z0,z2,z3,z4,z10,z6]),(0,[z0,z26,z2,z3,z4,z10,z75]),(0,[z0,z2,z3,z4,z10,z376,z6])],[(0,[z0,z2,z3,z15,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z6,z377]),(0,[z378,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z379,z10,z6]),(0,[z0,z2,z3,z380,z4,z10,z6]),(0,[z0,z381,z2,z3,z4,z10,z6])],[(0,[z382,z0,z2,z3,z4,z10,z6]),(0,[z14,z0,z2,z3,z4,z8,z6]),(0,[z0,z383,z2,z3,z4,z10,z6]),(0,[z80,z0,z2,z3,z4,z10,z6]),(0,[z0,z384,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z385,z10,z6]),(0,[z0,z386,z2,z3,z4,z10,z6])]],
   [[(0,[z0,z2,z3,z4,z10,z6,z387]),(0,[z0,z2,z3,z4,z5,z162,z6]),(0,[z0,z2,z3,z4,z388,z10,z6]),(0,[z0,z389,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z390])],[(0,[z0,z267,z2,z3,z4,z5,z6]),(0,[z0,z17,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z10,z43,z6]),(0,[z0,z2,z45,z3,z4,z20,z6])],[(0,[z0,z391,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z392,z6]),(0,[z0,z2,z3,z4,z98,z8,z6]),(0,[z0,z393,z2,z3,z4,z10,z6]),(0,[z0,z394,z2,z3,z4,z10,z6])],[(1,[z0,z2,z3,z4,z10,z371]),(0,[z135,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z395,z3,z4,z10,z6]),(0,[z0,z1,z2,z3,z4,z10,z131])],[(0,[z85,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z396,z6]),(0,[z0,z19,z2,z3,z4,z5,z6])],[(0,[z14,z0,z2,z34,z4,z10,z6]),(0,[z0,z2,z397,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z300,z10,z6]),(0,[z0,z81,z2,z3,z4,z8,z6]),(0,[z0,z17,z2,z3,z4,z10,z56]),(0,[z0,z398,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z399,z6])],[(0,[z0,z2,z3,z4,z10,z131,z140]),(0,[z0,z2,z3,z4,z10,z400,z6]),(0,[z401,z0,z2,z3,z4,z10,z6])],[]],
   [[(0,[z0,z2,z3,z402,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z403]),(0,[z0,z404,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z405]),(0,[z0,z2,z3,z406,z4,z10,z6])],[(0,[z407,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z408,z6]),(0,[z0,z2,z409,z3,z4,z10,z6]),(0,[z0,z410,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z411,z6]),(0,[z0,z2,z3,z4,z10,z412,z6])],[(0,[z0,z2,z3,z72,z10,z75,z6]),(0,[z0,z2,z3,z4,z413,z10,z6]),(0,[z0,z414,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z162,z6,z185])],[(0,[z415,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z416,z10,z6]),(0,[z0,z148,z2,z3,z4,z8,z6]),(0,[z0,z54,z2,z3,z4,z43,z6]),(0,[z0,z2,z3,z4,z10,z417,z6]),(0,[z0,z2,z3,z4,z10,z162,z6])],[(0,[z0,z89,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z10,z6,z418]),(0,[z0,z419,z2,z3,z4,z10,z6]),(0,[z0,z420,z2,z3,z4,z10,z6])],[(0,[z28,z0,z2,z3,z4,z10,z74]),(0,[z0,z2,z3,z4,z10,z179,z56]),(0,[z0,z2,z3,z4,z10,z6,z139]),(0,[z0,z2,z3,z4,z10,z421,z6])],[(0,[z0,z2,z3,z422,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z423,z6]),(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z424,z6]),(0,[z0,z2,z3,z4,z10,z6,z425])],[(0,[z0,z426,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z126,z10,z6]),(0,[z427,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z428,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z429])]],
   [[(0,[z430,z0,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z4,z423,z6]),(1,[z0,z2,z3,z4,z8,z6]),(0,[z0,z431,z2,z3,z4,z10,z6]),(0,[z432,z0,z2,z3,z4,z10,z6]),(0,[z0,z89,z2,z3,z4,z10,z56])],[(0,[z0,z26,z2,z3,z4,z10,z179]),(0,[z0,z2,z3,z4,z10,z433,z6])],[(0,[z0,z434,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z33,z10,z75,z6])],[(0,[z0,z202,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z435,z4,z10,z6]),(0,[z0,z243,z3,z4,z98,z10,z6]),(0,[z0,z2,z3,z4,z20,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z436])],[(1,[z0,z2,z3,z291,z10,z6]),(0,[z28,z0,z12,z3,z4,z10,z6]),(0,[z14,z0,z2,z3,z4,z10,z437]),(0,[z0,z76,z2,z3,z107,z10,z6]),(0,[z0,z2,z3,z4,z10,z438,z6]),(0,[z0,z2,z3,z4,z41,z10,z6])],[(0,[z0,z2,z3,z4,z10,z439,z6]),(0,[z0,z440,z2,z3,z4,z10,z6]),(0,[z0,z2,z53,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z10,z441,z6]),(0,[z0,z26,z2,z3,z4,z10,z110])],[(0,[z0,z2,z3,z4,z8,z6,z140]),(0,[z0,z2,z3,z4,z10,z6,z442]),(0,[z0,z443,z2,z3,z4,z10,z6]),(0,[z444,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z421,z6,z56])],[(0,[z0,z2,z3,z4,z10,z445,z6]),(0,[z0,z2,z78,z3,z4,z10,z6]),(0,[z0,z2,z3,z107,z4,z10,z6]),(0,[z0,z2,z4,z10,z131,z6,z56]),(1,[z0,z218,z2,z3,z4,z6])]],
   [[(0,[z0,z2,z2,z3,z4,z10,z6]),(0,[z446,z0,z2,z3,z4,z10,z6]),(0,[z0,z447,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z448,z10,z6]),(0,[z0,z54,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z10,z6,z367]),(0,[z0,z2,z449,z3,z4,z10,z6]),(0,[z0,z450,z2,z3,z4,z10,z6])],[(0,[z28,z0,z2,z451,z4,z10,z6]),(0,[z0,z452,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z100,z98,z10,z6]),(0,[z70,z2,z3,z4,z10,z5,z6]),(0,[z0,z73,z2,z3,z4,z10,z18]),(0,[z0,z2,z3,z4,z453,z10,z6]),(0,[z0,z26,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z33,z4,z10,z75])],[(0,[z0,z2,z3,z4,z454,z10,z6]),(0,[z0,z2,z3,z4,z455,z10,z6]),(0,[z0,z2,z3,z4,z5,z179,z6]),(0,[z0,z2,z3,z4,z5,z131,z6]),(0,[z0,z456,z2,z3,z4,z10,z6])],[(0,[z28,z0,z2,z3,z4,z5,z6]),(0,[z0,z457,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z458,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z459,z6]),(0,[z0,z73,z2,z3,z4,z321,z6])],[(0,[z460,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z461,z6]),(0,[z0,z2,z3,z4,z10,z462,z6]),(0,[z0,z2,z463,z3,z4,z10,z6])],[(0,[z464,z0,z2,z3,z4,z10,z6]),(1,[z14,z2,z15,z4,z10,z6]),(0,[z85,z0,z2,z3,z100,z10,z6]),(0,[z465,z0,z2,z3,z4,z10,z6]),(0,[z0,z76,z206,z2,z4,z10,z6]),(0,[z466,z0,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z33,z10,z75]),(0,[z0,z2,z3,z4,z10,z6,z467])],[(0,[z0,z2,z3,z4,z136,z10,z6]),(0,[z0,z2,z468,z3,z4,z5,z6]),(0,[z80,z0,z89,z2,z3,z4,z10]),(0,[z0,z2,z3,z4,z10,z469,z6]),(1,[z0,z2,z3,z4,z10,z358])],[(0,[z470,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z15,z4,z10,z6]),(0,[z0,z2,z471,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z27,z10,z147]),(0,[z0,z2,z45,z3,z4,z325,z6]),(0,[z0,z2,z3,z4,z10,z6,z472])]],
   [[(0,[z0,z2,z3,z4,z201,z10,z6]),(0,[z85,z0,z2,z3,z4,z10,z473]),(1,[z0,z23,z2,z3,z4,z10])],[(0,[z0,z2,z3,z4,z94,z8,z6]),(0,[z0,z2,z3,z4,z10,z140,z18]),(1,[z0,z2,z3,z4,z474,z6]),(0,[z0,z2,z3,z4,z10,z131,z110]),(0,[z0,z475,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z476,z8,z6]),(0,[z80,z0,z2,z3,z4,z24,z6]),(0,[z0,z267,z2,z3,z4,z10,z6]),(0,[z0,z477,z2,z3,z4,z10,z6])],[(0,[z0,z42,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z6,z478])],[(0,[z135,z0,z2,z3,z4,z10,z6])],[(1,[z0,z2,z3,z4,z10,z437]),(0,[z0,z19,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z131,z6])],[(0,[z28,z0,z2,z3,z4,z479,z6]),(0,[z0,z54,z2,z3,z4,z10,z358])],[(0,[z0,z2,z480,z3,z4,z10,z6]),(0,[z481,z0,z2,z3,z4,z10,z6])]],
   [[(0,[z0,z2,z3,z4,z65,z10,z6]),(0,[z0,z243,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z10,z482,z6]),(0,[z483,z0,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z27,z5,z6]),(0,[z0,z2,z3,z4,z10,z6,z484]),(0,[z0,z2,z3,z4,z10,z6,z485])],[(0,[z486,z0,z2,z3,z4,z10,z6]),(0,[z37,z0,z2,z3,z4,z8,z6]),(0,[z14,z0,z81,z2,z4,z10,z6]),(0,[z0,z2,z487,z3,z4,z10,z6]),(0,[z0,z2,z3,z488,z4,z10,z6]),(0,[z0,z489,z2,z3,z4,z10,z6])],[(1,[z37,z29,z3,z4,z10,z6]),(0,[z0,z2,z3,z490,z4,z10,z6]),(1,[z0,z73,z3,z4,z10,z147]),(0,[z491,z0,z2,z3,z4,z10,z6]),(1,[z0,z82,z2,z3,z10,z6]),(0,[z0,z2,z3,z10,z75,z6,z110])],[(1,[z0,z2,z3,z158,z10,z6]),(0,[z0,z2,z3,z4,z347,z5,z6]),(0,[z0,z23,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z492,z6])],[(0,[z0,z235,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z75,z6]),(0,[z0,z493,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z33,z4,z10,z179]),(0,[z0,z2,z3,z4,z10,z494,z6]),(0,[z0,z2,z3,z4,z474,z10,z6]),(0,[z0,z1,z2,z4,z10,z131,z6])],[(0,[z0,z2,z3,z495,z4,z10,z6]),(0,[z0,z2,z3,z496,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z239]),(1,[z0,z1,z2,z4,z10,z131])],[(0,[z0,z0,z2,z3,z4,z10,z6]),(0,[z28,z0,z2,z3,z4,z10,z68]),(1,[z0,z2,z3,z4,z321,z6]),(0,[z22,z0,z2,z3,z4,z162,z6]),(0,[z0,z2,z3,z4,z10,z497,z6])]],
   [[(0,[z0,z2,z498,z3,z4,z10,z6]),(0,[z0,z2,z3,z203,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z6,z185]),(0,[z0,z2,z3,z499,z4,z10,z6]),(0,[z0,z73,z2,z3,z4,z10,z147]),(0,[z0,z500,z2,z3,z4,z10,z6]),(0,[z0,z501,z2,z3,z4,z10,z6])],[(0,[z0,z502,z2,z3,z4,z10,z6]),(0,[z0,z2,z503,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z8,z6,z110]),(0,[z0,z2,z3,z4,z10,z6,z504]),(1,[z0,z2,z138,z4,z10,z6]),(0,[z0,z2,z3,z505,z4,z10,z6]),(0,[z0,z2,z3,z4,z506,z10,z6]),(0,[z0,z272,z2,z3,z4,z6,z56])],[(0,[z29,z2,z12,z3,z4,z10,z6]),(0,[z0,z507,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z473,z6]),(0,[z22,z0,z2,z3,z4,z8,z6]),(0,[z508,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z509,z10,z6]),(0,[z0,z2,z3,z4,z10,z510,z6])],[(0,[z0,z511,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z512,z4,z10,z6]),(0,[z0,z2,z3,z4,z513,z10,z6]),(0,[z0,z2,z45,z3,z4,z162,z6])],[(0,[z0,z2,z3,z4,z5,z514,z6]),(0,[z0,z2,z3,z34,z4,z8,z6]),(0,[z0,z202,z2,z3,z4,z10,z6]),(0,[z0,z515,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z222,z4,z10,z6]),(0,[z14,z0,z2,z3,z4,z10,z371]),(0,[z0,z516,z2,z3,z4,z10,z6]),(0,[z517,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z518,z4,z10,z6]),(0,[z0,z17,z2,z3,z4,z10,z147]),(0,[z0,z2,z3,z4,z10,z519,z6]),(0,[z0,z2,z3,z4,z520,z10,z6]),(0,[z0,z2,z45,z3,z4,z10,z521])],[(1,[z2,z3,z4,z8,z5,z6]),(0,[z0,z2,z45,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z522,z10,z6]),(0,[z0,z2,z3,z4,z523,z10,z6]),(0,[z524,z0,z2,z3,z4,z10,z6])],[(0,[z0,z2,z53,z32,z4,z10,z6]),(0,[z47,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z10,z525,z6]),(0,[z0,z526,z2,z3,z4,z10,z6]),(0,[z0,z2,z527,z3,z4,z10,z6])]],
   [[(0,[z0,z528,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z319,z6]),(0,[z0,z2,z3,z100,z94,z10,z6]),(0,[z0,z2,z3,z4,z8,z248,z6]),(0,[z529,z0,z2,z3,z4,z10,z6]),(0,[z22,z0,z2,z3,z95,z10,z6]),(0,[z530,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z75,z6])],[(0,[z0,z2,z3,z4,z10,z531,z6]),(0,[z0,z2,z3,z4,z10,z532,z6]),(0,[z0,z2,z3,z4,z10,z228,z6]),(0,[z0,z206,z2,z3,z4,z10,z367]),(0,[z0,z2,z3,z4,z533,z10,z6]),(1,[z0,z2,z215,z4,z10,z56])],[(0,[z0,z73,z2,z3,z4,z5,z6]),(0,[z80,z0,z2,z3,z4,z10,z179]),(0,[z0,z206,z2,z3,z4,z10,z172]),(0,[z0,z534,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z287,z6])],[(1,[z0,z2,z3,z4,z228,z6])],[(0,[z28,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z535]),(0,[z0,z2,z3,z4,z5,z51,z6]),(1,[z0,z2,z3,z305,z10,z6])],[(0,[z135,z0,z2,z53,z4,z10,z6]),(0,[z0,z2,z3,z4,z284,z10,z6]),(0,[z536,z0,z2,z3,z4,z10,z6])],[(0,[z537,z0,z2,z3,z4,z10,z6]),(0,[z538,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z18]),(1,[z0,z2,z3,z4,z347,z10]),(0,[z0,z2,z3,z4,z10,z101,z6]),(0,[z0,z539,z2,z3,z4,z10,z6])],[(0,[z540,z0,z2,z3,z4,z10,z6]),(0,[z14,z0,z2,z3,z4,z541,z6]),(0,[z0,z2,z468,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z542,z10,z6]),(0,[z0,z17,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z147,z6]),(0,[z88,z0,z2,z3,z4,z27,z10]),(0,[z0,z42,z2,z3,z95,z4,z6]),(1,[z0,z2,z45,z4,z20,z6]),(0,[z0,z2,z3,z4,z10,z56,z110])]],
   [[(1,[z0,z2,z3,z4,z10,z74]),(0,[z543,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z98,z5,z6]),(0,[z0,z89,z2,z3,z4,z10,z147]),(0,[z0,z544,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z10,z6,z437]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z206,z267,z2,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z545,z6]),(1,[z0,z546,z2,z3,z4,z6]),(1,[z0,z2,z3,z294,z4,z10]),(0,[z0,z2,z3,z4,z10,z6,z265])],[(0,[z79,z0,z2,z3,z4,z328,z6]),(1,[z85,z2,z3,z100,z10,z6]),(0,[z0,z2,z3,z4,z10,z147,z179])],[(0,[z0,z81,z2,z3,z4,z5,z6]),(0,[z0,z301,z2,z3,z4,z10,z6]),(0,[z0,z547,z2,z3,z4,z10,z6]),(0,[z0,z73,z2,z3,z4,z10,z56]),(0,[z0,z548,z2,z3,z4,z10,z6])],[(0,[z113,z70,z2,z3,z4,z10,z6]),(0,[z88,z0,z2,z3,z4,z93,z6]),(0,[z0,z42,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z549,z10,z6]),(0,[z0,z89,z2,z45,z3,z4,z6]),(0,[z0,z2,z3,z4,z550,z10,z6])],[(0,[z0,z2,z3,z4,z551,z10,z6]),(0,[z0,z2,z3,z4,z10,z552,z6]),(0,[z0,z2,z3,z553,z4,z10,z6]),(0,[z0,z554,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z287,z51]),(0,[z0,z2,z3,z4,z555,z10,z6]),(0,[z0,z2,z3,z95,z4,z162,z6]),(0,[z0,z2,z3,z4,z27,z10,z185])],[(0,[z0,z2,z3,z556,z4,z10,z6]),(0,[z0,z19,z2,z45,z4,z10,z6])],[(0,[z557,z0,z2,z3,z4,z10,z6]),(0,[z0,z148,z2,z3,z10,z75,z6])]],
   [[(0,[z0,z558,z2,z3,z4,z10,z6])],[(0,[z0,z148,z2,z3,z4,z5,z6]),(0,[z0,z546,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z18]),(0,[z0,z2,z3,z4,z10,z309,z6]),(0,[z0,z2,z3,z559,z4,z10,z6])],[(1,[z0,z23,z2,z3,z4,z5]),(0,[z0,z89,z2,z3,z4,z5,z6]),(0,[z0,z560,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z147,z6]),(0,[z0,z2,z3,z4,z561,z10,z6]),(0,[z0,z2,z3,z4,z27,z10,z6])],[(0,[z0,z2,z3,z4,z10,z140,z56]),(0,[z0,z2,z3,z294,z4,z98,z10]),(0,[z0,z42,z54,z3,z4,z10,z6]),(0,[z0,z3,z4,z10,z147,z6,z18]),(0,[z562,z0,z2,z3,z4,z10,z6])],[(1,[z0,z2,z451,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z5,z6]),(1,[z113,z2,z3,z4,z8,z6]),(0,[z0,z2,z563,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z131,z75]),(0,[z0,z2,z3,z4,z10,z564,z6])],[(0,[z0,z565,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z347,z10,z6]),(0,[z0,z206,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z566,z10,z6]),(0,[z0,z567,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z568]),(1,[z0,z89,z2,z3,z4,z185])],[(0,[z0,z2,z3,z4,z10,z541,z6]),(0,[z569,z0,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z234,z5,z6]),(0,[z0,z2,z3,z4,z10,z6,z570])],[(0,[z0,z2,z3,z4,z8,z312,z6]),(0,[z0,z2,z3,z571,z4,z10,z6]),(0,[z0,z2,z3,z4,z572,z10,z6])]],
   [[(1,[z0,z2,z3,z4,z541,z6]),(1,[z0,z2,z3,z4,z86,z6])],[(0,[z0,z573,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z574,z4,z10,z6]),(0,[z79,z2,z3,z4,z72,z10,z6]),(0,[z0,z2,z575,z3,z4,z10,z6]),(0,[z0,z2,z3,z203,z4,z10,z6]),(0,[z0,z2,z3,z576,z4,z10,z6])],[(0,[z0,z2,z3,z72,z94,z10,z6]),(0,[z0,z1,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z577,z4,z10,z6]),(1,[z0,z2,z3,z4,z10,z521]),(1,[z0,z2,z3,z4,z421,z6])],[(0,[z0,z2,z53,z3,z4,z5,z6]),(0,[z0,z2,z3,z578,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z579,z6]),(0,[z0,z206,z2,z34,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z580,z6]),(0,[z0,z2,z3,z581,z4,z10,z6])],[(0,[z0,z332,z2,z3,z4,z10,z6]),(0,[z0,z582,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z583,z4,z10,z6]),(0,[z584,z0,z2,z3,z4,z10,z6]),(0,[z585,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z586,z6]),(0,[z0,z2,z3,z4,z27,z10,z162])],[(0,[z0,z2,z3,z4,z351,z10,z6]),(0,[z0,z587,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z10,z479,z6]),(0,[z0,z29,z3,z32,z4,z10,z6]),(0,[z135,z0,z2,z15,z4,z10,z6]),(0,[z0,z2,z588,z3,z4,z10,z6]),(0,[z0,z42,z2,z3,z4,z183,z6]),(0,[z0,z2,z3,z4,z589,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z590]),(0,[z0,z2,z3,z4,z10,z6,z591]),(0,[z0,z2,z3,z4,z10,z592,z6])]],
   [[(0,[z0,z593,z2,z3,z4,z10,z6])],[(1,[z0,z2,z3,z4,z479,z6]),(0,[z0,z2,z3,z4,z10,z6,z594]),(0,[z0,z2,z3,z4,z10,z595,z6]),(0,[z596,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z597,z4,z10,z6]),(1,[z0,z17,z3,z4,z10,z18]),(0,[z0,z2,z3,z4,z27,z10,z131])],[(0,[z0,z243,z2,z3,z203,z10,z6]),(0,[z0,z81,z2,z3,z34,z10,z6]),(0,[z0,z2,z3,z598,z4,z10,z6])],[(0,[z0,z2,z3,z4,z599,z10,z6]),(0,[z0,z2,z3,z4,z4,z10,z6]),(0,[z0,z2,z3,z4,z474,z98,z6])],[(0,[z0,z2,z3,z4,z224,z10,z6]),(0,[z0,z29,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z600,z6]),(0,[z0,z2,z601,z3,z4,z10,z6])],[(0,[z378,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z178,z4,z8,z6]),(0,[z0,z602,z2,z3,z4,z10,z6]),(0,[z0,z26,z2,z3,z33,z10,z6])],[(0,[z0,z603,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z8,z325,z6]),(0,[z0,z604,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z605,z6])],[(0,[z0,z2,z3,z4,z606,z10,z6]),(0,[z0,z2,z3,z4,z94,z5,z6]),(0,[z0,z607,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z343,z4,z98,z10]),(0,[z0,z2,z608,z3,z4,z10,z6]),(0,[z0,z582,z2,z3,z4,z10,z51])]],
   [[(0,[z0,z2,z609,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z72,z8,z6]),(0,[z0,z2,z3,z4,z10,z131,z179]),(0,[z0,z610,z2,z3,z4,z10,z6]),(0,[z0,z2,z611,z3,z4,z10,z6]),(0,[z0,z17,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z612,z10,z6]),(0,[z0,z148,z2,z3,z34,z10,z6])],[(0,[z37,z0,z12,z3,z4,z10,z6]),(0,[z0,z2,z3,z299,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z140]),(0,[z0,z2,z3,z4,z10,z613,z6]),(0,[z0,z73,z2,z3,z4,z322,z6]),(0,[z0,z614,z2,z3,z4,z10,z6])],[(1,[z0,z2,z3,z4,z10,z68]),(0,[z0,z2,z3,z4,z10,z106,z6]),(0,[z79,z0,z2,z3,z4,z8,z6]),(0,[z85,z0,z2,z3,z4,z423,z6]),(0,[z85,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z10,z6,z615]),(0,[z616,z0,z2,z3,z4,z10,z6])],[(0,[z617,z0,z2,z3,z4,z10,z6]),(0,[z618,z0,z2,z3,z4,z10,z6])],[(0,[z0,z619,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z86,z10,z6]),(0,[z0,z2,z3,z4,z620,z10,z6]),(0,[z88,z0,z2,z3,z4,z10,z140]),(0,[z0,z81,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z621,z6])],[(0,[z135,z0,z2,z3,z4,z134,z6]),(0,[z622,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z623,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z163,z10,z6]),(0,[z0,z243,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z10,z179,z6,z140]),(0,[z0,z76,z2,z3,z305,z10,z6]),(0,[z0,z2,z3,z624,z4,z10,z6]),(0,[z0,z89,z2,z3,z95,z4,z6]),(0,[z0,z2,z3,z4,z10,z6,z625]),(0,[z0,z89,z2,z3,z4,z10,z185])],[(0,[z0,z626,z2,z3,z4,z10,z6]),(0,[z88,z0,z2,z3,z4,z8,z6])]],
   [[(0,[z37,z0,z2,z3,z4,z5,z6]),(0,[z79,z0,z2,z3,z72,z10,z6]),(0,[z85,z0,z2,z3,z72,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z56]),(1,[z0,z2,z3,z4,z347,z5]),(0,[z0,z2,z3,z4,z8,z43,z6]),(0,[z0,z2,z3,z627,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z179,z6]),(0,[z0,z628,z2,z3,z4,z10,z6]),(0,[z0,z2,z629,z3,z4,z10,z6])],[(0,[z0,z2,z3,z630,z4,z10,z6]),(0,[z135,z2,z53,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z416,z8,z6]),(0,[z0,z631,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z203,z100,z10,z6]),(0,[z113,z0,z2,z3,z4,z8,z6]),(1,[z80,z2,z3,z4,z10,z140]),(0,[z0,z81,z2,z32,z4,z10,z6]),(0,[z0,z148,z2,z3,z4,z10,z6]),(0,[z0,z218,z2,z3,z4,z10,z6])],[(0,[z0,z89,z2,z3,z4,z10,z6])],[(0,[z632,z0,z2,z3,z4,z10,z6]),(0,[z0,z633,z2,z3,z4,z10,z6]),(0,[z0,z19,z2,z3,z4,z325,z6]),(0,[z0,z634,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z10,z10,z6]),(0,[z0,z426,z2,z3,z4,z8,z6]),(0,[z0,z202,z3,z203,z4,z10,z6]),(0,[z0,z2,z3,z4,z635,z10,z6])],[(1,[z0,z78,z3,z4,z10,z6]),(0,[z113,z2,z3,z4,z8,z10,z6]),(0,[z0,z272,z2,z3,z4,z10,z6]),(0,[z0,z636,z2,z3,z4,z10,z6]),(1,[z0,z582,z2,z3,z4,z10])],[(1,[z0,z2,z3,z4,z10,z6]),(0,[z0,z17,z2,z3,z4,z10,z131]),(0,[z0,z2,z215,z4,z10,z6,z56]),(0,[z0,z637,z2,z3,z4,z10,z6])]],
   [[(0,[z638,z0,z2,z3,z4,z10,z6]),(0,[z22,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z100,z4,z8,z6]),(1,[z0,z267,z32,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z639,z6])],[(1,[z0,z2,z3,z4,z201,z6]),(0,[z0,z2,z3,z34,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z162,z6])],[(0,[z0,z2,z451,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z56])],[(0,[z0,z2,z53,z3,z4,z10,z6]),(0,[z0,z2,z3,z578,z4,z10,z6]),(0,[z0,z2,z45,z3,z4,z5,z6]),(0,[z22,z0,z89,z2,z3,z4,z6])],[(0,[z0,z2,z3,z205,z4,z10,z6]),(0,[z640,z0,z2,z3,z4,z10,z6]),(0,[z47,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z8,z6]),(0,[z0,z243,z202,z3,z4,z10,z6]),(1,[z0,z2,z3,z4,z322,z6]),(0,[z0,z2,z3,z4,z10,z641,z6])],[(0,[z0,z2,z3,z72,z98,z10,z6]),(0,[z0,z642,z2,z3,z4,z10,z6]),(0,[z0,z89,z2,z3,z4,z10,z162])],[(0,[z14,z0,z2,z53,z4,z10,z6]),(0,[z0,z2,z299,z4,z72,z10,z6]),(0,[z0,z26,z2,z3,z4,z8,z6]),(0,[z0,z546,z2,z3,z4,z98,z6]),(0,[z0,z2,z3,z643,z4,z10,z6]),(0,[z0,z17,z2,z3,z33,z4,z10]),(0,[z0,z644,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z645,z6]),(0,[z646,z0,z2,z3,z4,z10,z6])]],
   [[(0,[z0,z647,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z648]),(0,[z0,z2,z3,z649,z4,z10,z6]),(0,[z0,z650,z2,z3,z4,z10,z6])],[(0,[z651,z0,z2,z3,z4,z10,z6]),(0,[z0,z652,z2,z3,z4,z10,z6]),(0,[z0,z2,z45,z4,z20,z10,z6])],[(0,[z653,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z654,z6]),(0,[z0,z89,z2,z3,z4,z10,z131]),(0,[z0,z89,z26,z2,z3,z4,z10])],[(0,[z0,z2,z3,z4,z10,z655,z6]),(0,[z0,z2,z3,z4,z10,z656,z6])],[(0,[z0,z2,z3,z4,z194,z10,z6]),(0,[z0,z2,z657,z3,z4,z10,z6]),(0,[z0,z2,z3,z658,z4,z10,z6]),(0,[z0,z2,z3,z4,z183,z162,z6])],[(0,[z0,z29,z2,z3,z4,z10,z6]),(0,[z0,z26,z2,z3,z72,z10,z6]),(0,[z0,z76,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z442]),(0,[z0,z2,z659,z3,z4,z10,z6]),(0,[z0,z202,z2,z3,z98,z10,z6]),(0,[z0,z2,z34,z4,z94,z10,z6]),(0,[z0,z2,z3,z4,z10,z255,z6])],[(0,[z37,z0,z2,z3,z4,z106,z6]),(1,[z0,z2,z3,z343,z4,z10]),(0,[z0,z89,z2,z3,z4,z183,z6]),(0,[z0,z660,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z10,z255,z6,z56]),(0,[z0,z2,z3,z4,z10,z661,z6]),(0,[z662,z0,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z183,z8,z6]),(0,[z80,z2,z3,z4,z10,z6,z140]),(0,[z0,z663,z2,z3,z4,z10,z6]),(0,[z0,z3,z203,z4,z98,z10,z6]),(1,[z0,z164,z2,z4,z10,z6])]],
   [[(0,[z14,z0,z2,z3,z4,z5,z6]),(0,[z0,z267,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z38,z10,z6]),(0,[z0,z54,z3,z4,z183,z10,z6]),(0,[z0,z2,z3,z4,z94,z10,z6]),(0,[z0,z19,z2,z3,z4,z162,z6]),(0,[z664,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z665,z6])],[(0,[z0,z2,z3,z291,z4,z10,z6]),(0,[z0,z2,z3,z4,z476,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z666]),(0,[z667,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z668,z4,z10,z6])],[(0,[z669,z0,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z4,z65,z6]),(0,[z0,z2,z3,z4,z10,z514,z6]),(0,[z0,z2,z3,z670,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z671,z6]),(0,[z0,z89,z2,z3,z33,z4,z10])],[(0,[z0,z19,z2,z3,z4,z8,z6])],[(1,[z0,z2,z3,z4,z10,z257]),(1,[z0,z2,z3,z276,z10,z6]),(0,[z0,z76,z206,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z672,z6]),(0,[z0,z81,z2,z3,z10,z75,z6]),(0,[z0,z2,z3,z4,z10,z6,z673]),(0,[z0,z2,z3,z4,z10,z674,z6]),(0,[z0,z2,z675,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z10,z676,z6]),(0,[z0,z2,z3,z4,z10,z677,z6]),(0,[z678,z0,z2,z3,z4,z10,z6])],[(0,[z679,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z680,z10,z6]),(0,[z681,z0,z2,z3,z4,z10,z6]),(0,[z0,z682,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z683,z4,z10,z6]),(0,[z0,z2,z684,z3,z4,z10,z6])],[(0,[z685,z0,z2,z3,z4,z10,z6]),(0,[z0,z243,z2,z3,z4,z10,z6]),(0,[z0,z73,z17,z3,z4,z10,z6]),(0,[z0,z2,z3,z686,z4,z10,z6]),(0,[z0,z26,z148,z2,z3,z10,z6]),(0,[z0,z687,z2,z3,z4,z10,z6]),(0,[z0,z688,z2,z3,z4,z10,z6])]],
   [[(0,[z0,z689,z2,z3,z4,z10,z6]),(0,[z0,z690,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z691,z6]),(0,[z0,z2,z3,z4,z10,z692,z6]),(0,[z0,z26,z2,z3,z10,z6,z110])],[(0,[z37,z0,z2,z3,z4,z10,z6]),(0,[z0,z329,z2,z4,z72,z10,z6]),(0,[z0,z122,z2,z3,z4,z5,z6]),(0,[z0,z2,z215,z3,z4,z8,z6]),(0,[z0,z693,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z694,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z521,z6])],[(0,[z0,z2,z3,z4,z10,z695,z6]),(0,[z0,z2,z3,z4,z10,z51,z6]),(0,[z0,z2,z3,z696,z4,z10,z6])],[(1,[z0,z2,z3,z4,z10,z473]),(0,[z0,z2,z3,z95,z4,z8,z6]),(0,[z0,z697,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z698,z4,z10,z6])],[(0,[z0,z2,z3,z4,z8,z131,z6])],[(0,[z699,z0,z2,z3,z4,z10,z6]),(0,[z0,z700,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z701]),(0,[z0,z2,z3,z702,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z6,z703]),(0,[z0,z73,z3,z4,z10,z147,z6]),(0,[z0,z2,z3,z4,z10,z704,z6]),(0,[z0,z2,z215,z3,z4,z10,z56])],[(0,[z0,z2,z3,z4,z705,z10,z6])],[(0,[z706,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z8,z482,z6]),(0,[z0,z26,z17,z2,z3,z4,z10]),(0,[z0,z2,z3,z41,z10,z51,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z2,z3,z4,z707,z10]),(0,[z0,z2,z3,z4,z10,z708]),(0,[z0,z23,z2,z468,z3,z4]),(0,[z2,z3,z4,z231,z8,z6]),(0,[z0,z2,z3,z4,z709,z6]),(0,[z0,z710,z2,z3,z4,z6])],[(0,[z0,z2,z3,z222,z8,z6]),(0,[z0,z2,z3,z4,z5,z473]),(0,[z80,z2,z3,z4,z10,z140]),(0,[z0,z2,z32,z107,z10,z6]),(0,[z0,z2,z3,z33,z253,z10])],[(1,[z2,z3,z4,z711,z6]),(0,[z0,z2,z3,z294,z4,z5]),(0,[z0,z2,z468,z4,z300,z6]),(0,[z0,z3,z4,z10,z712,z6]),(0,[z0,z2,z3,z4,z713,z6])],[(0,[z0,z2,z3,z4,z714,z6]),(0,[z0,z715,z2,z4,z10,z6]),(0,[z0,z2,z3,z716,z10,z6]),(0,[z0,z2,z3,z4,z10,z717]),(0,[z0,z202,z138,z203,z10,z6]),(0,[z0,z2,z3,z4,z718,z6]),(0,[z0,z2,z3,z4,z719,z6])],[(0,[z0,z2,z3,z4,z10,z720]),(0,[z0,z2,z3,z4,z134,z6]),(0,[z0,z2,z3,z4,z721,z6]),(0,[z0,z2,z3,z4,z10,z722]),(0,[z0,z723,z2,z3,z5,z6]),(0,[z0,z23,z2,z3,z4,z43]),(0,[z0,z7,z3,z4,z183,z6]),(0,[z0,z2,z724,z4,z10,z6]),(0,[z0,z243,z3,z725,z10,z6]),(0,[z0,z546,z2,z3,z294,z4])],[(0,[z0,z78,z3,z4,z10,z6]),(0,[z14,z2,z15,z4,z10,z371]),(0,[z0,z693,z3,z4,z10,z147]),(0,[z0,z2,z726,z4,z10,z6]),(0,[z0,z2,z3,z727,z10,z6]),(0,[z0,z2,z3,z4,z10,z728]),(0,[z0,z582,z2,z3,z4,z10]),(0,[z0,z2,z3,z95,z6,z210])],[(0,[z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z729,z6]),(0,[z0,z2,z3,z4,z730,z328]),(0,[z0,z2,z3,z4,z731,z6]),(0,[z0,z214,z3,z4,z183,z6]),(0,[z0,z2,z3,z4,z10,z732]),(0,[z0,z89,z2,z3,z4,z239]),(0,[z0,z2,z3,z4,z421,z239]),(0,[z0,z2,z3,z10,z75,z733])],[(0,[z0,z2,z3,z4,z10,z734]),(0,[z0,z2,z3,z735,z10,z6]),(0,[z0,z2,z608,z4,z10,z56])]],
   [[(0,[z0,z2,z3,z736,z4,z10]),(0,[z0,z2,z3,z194,z541,z6]),(0,[z0,z2,z3,z4,z737,z6])],[(0,[z0,z2,z205,z158,z10,z6]),(0,[z0,z2,z3,z291,z8,z6]),(0,[z0,z2,z738,z4,z10,z6]),(0,[z0,z3,z4,z739,z10,z6]),(0,[z0,z2,z3,z4,z740,z6])],[(0,[z0,z2,z3,z4,z741,z6]),(0,[z0,z2,z3,z38,z5,z6]),(0,[z0,z419,z3,z203,z10,z6])],[(0,[z0,z742,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z743,z6]),(0,[z0,z2,z3,z4,z10,z744])],[(0,[z0,z2,z3,z4,z745,z6]),(0,[z0,z2,z3,z4,z10,z746]),(1,[z0,z2,z747,z10,z6])],[(0,[z0,z2,z3,z158,z224,z6]),(0,[z0,z277,z2,z34,z10,z6]),(0,[z0,z2,z3,z95,z234,z6]),(0,[z0,z2,z3,z748,z4,z10]),(0,[z0,z2,z3,z4,z749,z6])],[(0,[z28,z12,z3,z4,z5,z6]),(0,[z14,z2,z15,z4,z541,z6]),(0,[z0,z2,z750,z4,z10,z6])]],
   [[(0,[z0,z26,z2,z3,z10,z285]),(0,[z0,z2,z3,z4,z751,z6]),(0,[z0,z89,z2,z3,z4,z200])],[(0,[z0,z2,z3,z752,z10,z6]),(0,[z2,z53,z750,z4,z10,z6]),(0,[z0,z2,z3,z4,z8,z753]),(0,[z0,z89,z2,z3,z4,z421])],[(0,[z14,z2,z15,z4,z8,z6]),(0,[z0,z2,z3,z4,z754,z6]),(0,[z0,z2,z3,z4,z5,z287]),(0,[z0,z2,z3,z33,z8,z75]),(0,[z0,z2,z3,z755,z10,z6]),(0,[z0,z756,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z8,z358]),(0,[z0,z431,z3,z4,z10,z18]),(0,[z0,z2,z3,z276,z10,z179])],[(0,[z0,z757,z3,z4,z10,z6]),(0,[z0,z758,z3,z4,z10,z6]),(0,[z22,z0,z2,z3,z4,z358])],[(0,[z0,z2,z3,z759,z10,z6]),(0,[z0,z2,z3,z4,z5,z760]),(0,[z0,z54,z3,z4,z126,z6]),(0,[z0,z243,z3,z98,z8,z6]),(0,[z0,z2,z3,z343,z4,z10]),(0,[z0,z2,z3,z10,z75,z390]),(0,[z0,z2,z3,z4,z10,z761]),(0,[z0,z2,z3,z4,z762,z6])],[(0,[z0,z2,z3,z4,z347,z8]),(0,[z0,z2,z3,z4,z10,z763]),(0,[z0,z164,z2,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z764]),(0,[z0,z2,z3,z4,z765,z6]),(0,[z0,z766,z2,z3,z4,z6])],[(0,[z0,z2,z3,z767,z10,z6]),(0,[z0,z2,z3,z4,z10,z768]),(0,[z0,z2,z3,z4,z541,z437]),(0,[z0,z2,z299,z4,z5,z6]),(0,[z0,z2,z3,z5,z769,z6]),(0,[z524,z2,z3,z4,z5,z6]),(0,[z0,z7,z3,z4,z351,z6]),(0,[z0,z770,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z27,z312])]],
   [[(0,[z135,z2,z53,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z771]),(0,[z0,z2,z3,z4,z8,z772]),(0,[z0,z2,z3,z4,z6,z773]),(0,[z0,z3,z203,z725,z10,z6])],[(0,[z0,z2,z3,z4,z65,z6]),(0,[z0,z774,z3,z4,z10,z6]),(0,[z0,z775,z3,z4,z10,z6]),(0,[z70,z23,z2,z3,z4,z5]),(0,[z105,z2,z3,z4,z5,z6]),(0,[z0,z23,z2,z3,z95,z4]),(0,[z0,z2,z3,z294,z4,z8]),(0,[z2,z3,z4,z302,z8,z6]),(0,[z0,z2,z3,z10,z6,z776]),(0,[z0,z2,z3,z95,z680,z6])],[(0,[z0,z2,z451,z158,z10,z6]),(0,[z0,z2,z3,z777,z10,z6]),(0,[z0,z2,z3,z4,z778,z6]),(0,[z0,z2,z3,z4,z8,z437]),(0,[z0,z779,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z8,z265])],[(0,[z0,z2,z3,z780,z10,z6]),(0,[z0,z2,z3,z4,z10,z257]),(0,[z0,z2,z3,z276,z10,z6]),(0,[z0,z89,z2,z3,z4,z347]),(0,[z0,z2,z3,z4,z781,z6])],[(0,[z0,z2,z3,z4,z782,z6]),(0,[z0,z78,z3,z4,z163,z6]),(0,[z0,z2,z3,z4,z10,z783]),(0,[z0,z2,z3,z4,z784,z6]),(0,[z0,z785,z2,z3,z10,z6])],[(0,[z0,z2,z205,z4,z10,z74]),(0,[z0,z2,z3,z4,z163,z6]),(0,[z0,z2,z3,z107,z5,z6]),(0,[z0,z122,z3,z4,z112,z6]),(0,[z0,z2,z3,z5,z255,z6]),(0,[z0,z786,z2,z4,z5,z6]),(0,[z0,z26,z2,z3,z5,z110]),(0,[z0,z2,z45,z4,z787,z6])],[(0,[z2,z788,z3,z4,z10,z6]),(0,[z0,z23,z2,z3,z4,z118]),(0,[z0,z546,z243,z3,z98,z6]),(0,[z0,z789,z2,z3,z4,z6])],[(0,[z0,z329,z2,z10,z75,z6]),(0,[z0,z790,z2,z3,z4,z6]),(0,[z0,z82,z2,z3,z421,z6]),(0,[z22,z0,z2,z3,z314,z6])]],
   [[(0,[z0,z2,z3,z4,z10,z791]),(0,[z0,z2,z3,z4,z792,z6]),(0,[z0,z2,z3,z793,z10,z6]),(0,[z2,z3,z794,z72,z10,z6]),(0,[z0,z202,z3,z203,z5,z6]),(0,[z0,z73,z3,z4,z8,z147]),(0,[z0,z82,z2,z3,z8,z6]),(0,[z0,z795,z2,z4,z10,z6]),(0,[z0,z42,z3,z4,z43,z6]),(0,[z0,z54,z3,z4,z183,z6]),(0,[z0,z2,z3,z4,z796,z265]),(0,[z0,z2,z3,z4,z797,z6])],[(0,[z0,z2,z3,z158,z8,z6]),(0,[z0,z329,z2,z4,z5,z6]),(0,[z0,z89,z2,z3,z4,z228]),(0,[z0,z2,z3,z747,z10,z6])],[(0,[z0,z2,z798,z4,z10,z6]),(0,[z0,z2,z3,z10,z769,z6]),(0,[z0,z2,z3,z4,z10,z473]),(0,[z0,z2,z4,z5,z799,z6]),(0,[z0,z2,z3,z4,z347,z514]),(0,[z0,z2,z3,z800,z10,z6])],[(0,[z0,z801,z2,z3,z4,z10])],[(0,[z0,z2,z3,z4,z10,z802]),(0,[z0,z803,z2,z3,z4,z10]),(0,[z0,z804,z3,z4,z10,z6]),(0,[z2,z3,z100,z794,z10,z6]),(0,[z616,z2,z3,z4,z5,z6]),(0,[z80,z2,z3,z4,z24,z140]),(0,[z0,z2,z3,z4,z10,z805])],[(0,[z0,z723,z2,z3,z10,z6]),(0,[z0,z806,z2,z4,z5,z6]),(0,[z0,z2,z3,z5,z807,z6])],[(0,[z0,z587,z2,z4,z10,z131]),(0,[z0,z2,z3,z4,z808,z6]),(0,[z809,z2,z3,z4,z10,z6])],[(0,[z79,z2,z3,z72,z201,z6]),(0,[z22,z0,z2,z3,z522,z6]),(0,[z0,z1,z2,z4,z10,z810])]],
   [[(0,[z0,z2,z3,z4,z811,z6]),(0,[z0,z2,z3,z812,z4,z10]),(0,[z0,z2,z3,z4,z10,z813]),(0,[z0,z814,z2,z3,z4,z6]),(0,[z0,z122,z3,z4,z43,z6]),(0,[z0,z546,z2,z3,z343,z4]),(0,[z0,z2,z815,z4,z10,z6]),(0,[z0,z2,z3,z10,z255,z6]),(0,[z0,z2,z3,z4,z10,z816])],[(0,[z0,z304,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z8,z309]),(0,[z0,z26,z2,z3,z189,z110]),(0,[z0,z2,z3,z4,z10,z733])],[(0,[z0,z2,z3,z4,z707,z5]),(0,[z0,z148,z2,z10,z510,z6])],[(0,[z0,z2,z205,z4,z5,z6]),(0,[z0,z304,z3,z4,z541,z6]),(0,[z0,z2,z3,z38,z10,z6]),(0,[z2,z3,z4,z347,z8,z5]),(0,[z2,z3,z4,z8,z711,z6]),(0,[z0,z243,z3,z474,z98,z6]),(0,[z0,z2,z3,z4,z817,z6])],[(0,[z678,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z818,z10,z6])],[(0,[z0,z2,z3,z4,z819,z6]),(0,[z0,z2,z3,z820,z4,z10]),(0,[z0,z2,z4,z10,z799,z6]),(0,[z80,z241,z2,z3,z4,z10]),(0,[z157,z2,z3,z4,z10,z140]),(0,[z0,z821,z2,z3,z10,z6]),(0,[z0,z2,z215,z4,z421,z56])],[(0,[z0,z2,z451,z4,z224,z6]),(0,[z0,z2,z3,z4,z822,z6]),(0,[z0,z823,z2,z3,z4,z134]),(0,[z0,z2,z215,z4,z8,z56]),(0,[z0,z2,z61,z4,z20,z6]),(0,[z0,z89,z2,z3,z4,z436]),(0,[z22,z0,z2,z3,z51,z6])],[(0,[z0,z2,z3,z4,z824,z6]),(0,[z0,z2,z3,z4,z5,z367]),(0,[z227,z2,z3,z4,z5,z6]),(0,[z0,z582,z2,z3,z4,z5]),(0,[z0,z81,z2,z165,z10,z6]),(0,[z0,z825,z3,z4,z10,z6]),(0,[z0,z2,z3,z10,z826,z6])]],
   [[(0,[z28,z12,z3,z4,z10,z6]),(0,[z0,z827,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z172]),(0,[z0,z2,z3,z4,z828,z6]),(0,[z0,z2,z829,z4,z10,z6]),(0,[z0,z3,z4,z183,z712,z6]),(0,[z0,z2,z3,z830,z10,z6]),(0,[z0,z89,z450,z2,z3,z4])],[(0,[z0,z2,z3,z4,z831,z6]),(0,[z0,z2,z832,z3,z4,z10]),(0,[z0,z2,z3,z305,z8,z6]),(0,[z0,z2,z3,z4,z8,z833])],[(0,[z0,z235,z2,z4,z101,z6]),(0,[z0,z2,z3,z4,z834,z6]),(0,[z0,z835,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z836,z6])],[(0,[z0,z23,z2,z3,z4,z185]),(0,[z0,z42,z3,z4,z248,z6]),(0,[z0,z2,z3,z4,z837,z6]),(0,[z0,z2,z3,z4,z838,z6])],[(0,[z0,z2,z3,z4,z839,z6]),(0,[z660,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z8,z74]),(0,[z0,z788,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z840,z6]),(0,[z0,z2,z3,z4,z841,z6])],[(0,[z0,z2,z205,z4,z479,z6]),(0,[z0,z2,z3,z4,z10,z760]),(0,[z0,z842,z3,z4,z10,z6]),(0,[z0,z3,z4,z5,z843,z6])],[(0,[z88,z2,z3,z4,z5,z179])]],
   [[(0,[z0,z78,z15,z4,z10,z6]),(0,[z0,z2,z3,z4,z541,z371]),(0,[z0,z2,z299,z4,z10,z6]),(0,[z0,z329,z2,z34,z10,z6]),(0,[z0,z81,z2,z193,z10,z6]),(0,[z0,z82,z17,z2,z3,z10])],[(0,[z0,z2,z3,z291,z224,z6]),(0,[z0,z2,z3,z291,z10,z74]),(0,[z88,z2,z3,z4,z10,z844]),(0,[z0,z272,z2,z215,z4,z56])],[(0,[z0,z845,z3,z4,z10,z6]),(0,[z0,z2,z846,z4,z10,z6]),(0,[z0,z89,z2,z3,z4,z615])],[(0,[z0,z2,z3,z4,z10,z847]),(0,[z0,z2,z3,z4,z8,z371]),(0,[z0,z2,z3,z100,z10,z473]),(0,[z0,z2,z3,z4,z848,z6]),(0,[z0,z2,z3,z4,z849,z6]),(0,[z0,z82,z2,z3,z27,z10])],[(0,[z0,z850,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z851,z6]),(0,[z0,z2,z3,z4,z852,z6]),(0,[z0,z2,z3,z4,z853,z6])],[(0,[z0,z2,z3,z4,z854,z6]),(0,[z0,z89,z2,z3,z296,z4])],[(0,[z0,z2,z3,z4,z855,z6]),(0,[z685,z2,z53,z4,z10,z6]),(0,[z121,z0,z23,z2,z3,z4]),(0,[z0,z2,z3,z107,z10,z6]),(0,[z0,z26,z2,z3,z10,z110])],[(0,[z0,z2,z205,z4,z10,z68]),(0,[z0,z2,z3,z4,z856,z6]),(0,[z0,z2,z3,z222,z5,z6]),(0,[z0,z2,z3,z343,z4,z5]),(0,[z0,z2,z3,z4,z857,z6])]],
   [[(0,[z29,z788,z3,z4,z10,z6]),(0,[z0,z2,z659,z4,z10,z56]),(0,[z0,z2,z3,z4,z858,z6])],[(0,[z0,z2,z451,z4,z8,z6]),(0,[z0,z2,z859,z4,z10,z6]),(0,[z0,z391,z206,z4,z10,z6]),(0,[z0,z3,z4,z10,z843,z6]),(0,[z2,z3,z4,z5,z166,z6]),(0,[z0,z2,z3,z4,z10,z860]),(0,[z0,z202,z3,z203,z10,z6]),(0,[z0,z2,z3,z4,z10,z861])],[(0,[z0,z329,z2,z4,z10,z6]),(1,[z2,z3,z794,z10,z6]),(0,[z0,z2,z3,z4,z862,z6])],[(0,[z0,z2,z3,z4,z863,z6]),(0,[z306,z2,z3,z4,z10,z179]),(0,[z0,z544,z32,z4,z10,z6])],[(0,[z28,z788,z3,z4,z10,z6]),(0,[z2,z750,z15,z4,z10,z6]),(0,[z0,z2,z3,z4,z328,z6]),(0,[z0,z2,z3,z4,z864,z6]),(0,[z0,z2,z3,z294,z4,z474])],[(0,[z0,z2,z451,z291,z10,z6]),(0,[z0,z865,z2,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z239]),(0,[z0,z2,z3,z866,z4,z10]),(0,[z0,z2,z3,z867,z10,z6]),(0,[z0,z2,z3,z4,z10,z139]),(0,[z0,z2,z3,z868,z10,z6])],[(0,[z0,z806,z2,z4,z10,z6]),(0,[z79,z2,z3,z72,z5,z6]),(0,[z0,z582,z2,z3,z4,z8]),(0,[z0,z2,z3,z10,z869,z6])],[(0,[z14,z2,z750,z4,z10,z6]),(0,[z0,z2,z870,z4,z10,z6]),(0,[z0,z871,z2,z4,z10,z6]),(0,[z241,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z521]),(0,[z0,z872,z2,z3,z4,z6]),(0,[z0,z3,z4,z712,z43,z6]),(0,[z0,z2,z3,z95,z873,z6])]],
   [[(0,[z0,z2,z3,z4,z8,z874]),(0,[z0,z2,z3,z4,z6,z875]),(0,[z227,z2,z3,z4,z10,z179]),(0,[z0,z82,z2,z215,z10,z56])],[(0,[z0,z2,z876,z4,z10,z6]),(0,[z0,z2,z3,z194,z5,z6]),(0,[z0,z2,z3,z4,z877,z6]),(0,[z2,z3,z4,z5,z192,z6]),(0,[z0,z2,z3,z4,z878,z6]),(0,[z0,z148,z2,z34,z10,z6]),(0,[z0,z2,z4,z787,z325,z6]),(0,[z0,z2,z3,z576,z10,z75]),(0,[z0,z2,z3,z4,z27,z744])],[(0,[z0,z304,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z27,z692]),(0,[z0,z2,z3,z4,z879,z6])],[(0,[z0,z2,z3,z880,z10,z6]),(0,[z135,z2,z750,z4,z10,z6]),(0,[z173,z2,z3,z100,z10,z6]),(0,[z0,z881,z2,z4,z10,z6]),(0,[z0,z2,z3,z4,z882,z367]),(0,[z883,z2,z3,z4,z10,z6])],[(0,[z0,z364,z32,z4,z10,z6]),(0,[z0,z2,z3,z4,z884,z6]),(0,[z2,z3,z4,z10,z6,z885])],[(0,[z0,z2,z3,z4,z136,z6]),(0,[z0,z886,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z887,z6]),(0,[z0,z2,z3,z4,z888,z6]),(0,[z0,z2,z3,z255,z421,z6])],[(0,[z0,z2,z3,z4,z889,z6]),(0,[z63,z2,z3,z72,z10,z6]),(0,[z0,z803,z2,z3,z4,z5]),(0,[z0,z17,z3,z4,z8,z18]),(0,[z0,z890,z2,z3,z4,z10]),(0,[z0,z2,z3,z4,z27,z162])],[(0,[z0,z2,z3,z4,z10,z891]),(0,[z0,z2,z3,z4,z10,z892]),(0,[z0,z2,z893,z3,z4,z10]),(0,[z0,z73,z3,z4,z103,z10])]],
   [[(0,[z0,z2,z3,z894,z10,z6]),(0,[z14,z2,z15,z4,z5,z6]),(0,[z646,z2,z3,z72,z10,z6]),(0,[z0,z332,z3,z4,z126,z6]),(0,[z0,z2,z3,z33,z5,z75]),(0,[z0,z2,z3,z4,z10,z367]),(0,[z895,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z896,z6]),(0,[z0,z89,z2,z3,z4,z648]),(0,[z0,z19,z2,z4,z325,z6])],[(0,[z0,z2,z3,z158,z10,z74]),(0,[z0,z2,z3,z4,z5,z358]),(0,[z0,z2,z3,z4,z10,z172]),(0,[z0,z333,z3,z4,z43,z6])],[(0,[z0,z897,z2,z3,z4,z6])],[(0,[z0,z81,z78,z4,z10,z6]),(0,[z0,z243,z3,z98,z5,z6]),(0,[z244,z2,z3,z4,z5,z6]),(0,[z71,z2,z3,z4,z5,z6]),(0,[z0,z218,z2,z3,z4,z56])],[(0,[z0,z898,z2,z3,z10,z6]),(0,[z0,z329,z2,z4,z10,z771])],[(0,[z0,z899,z2,z4,z10,z6]),(0,[z0,z2,z3,z900,z10,z6]),(0,[z0,z901,z2,z3,z4,z10]),(0,[z0,z2,z4,z10,z902,z6]),(0,[z0,z2,z3,z903,z10,z6])],[(0,[z0,z904,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z905,z6]),(0,[z0,z2,z3,z343,z4,z8]),(0,[z0,z2,z3,z4,z906,z6]),(0,[z0,z2,z3,z4,z10,z907]),(0,[z908,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z10,z75,z265])],[(0,[z0,z2,z909,z4,z10,z6]),(0,[z0,z2,z3,z4,z8,z68]),(0,[z37,z788,z3,z4,z10,z6]),(0,[z0,z23,z2,z3,z4,z112]),(0,[z0,z3,z4,z8,z910,z6]),(0,[z0,z2,z3,z4,z10,z911]),(0,[z0,z2,z3,z4,z6,z912])]],
   [[(0,[z0,z2,z3,z4,z913,z6]),(0,[z0,z2,z3,z4,z914,z6]),(0,[z0,z2,z3,z4,z5,z437]),(0,[z0,z2,z3,z4,z5,z265]),(0,[z88,z2,z3,z4,z10,z179]),(0,[z0,z2,z623,z4,z10,z56]),(0,[z0,z2,z915,z4,z10,z6]),(0,[z0,z2,z3,z4,z6,z189]),(0,[z0,z2,z3,z4,z916,z6])],[(0,[z135,z2,z53,z4,z134,z6]),(0,[z662,z2,z3,z4,z5,z6]),(0,[z0,z2,z917,z4,z10,z6]),(0,[z0,z2,z4,z10,z810,z56]),(0,[z0,z918,z3,z4,z10,z6])],[(0,[z0,z26,z2,z3,z10,z308])],[(0,[z0,z2,z3,z291,z10,z68]),(0,[z0,z2,z3,z919,z10,z6]),(0,[z0,z2,z3,z920,z10,z6]),(0,[z0,z2,z832,z3,z4,z5]),(0,[z0,z301,z2,z3,z4,z442]),(0,[z363,z2,z3,z4,z8,z6]),(1,[z2,z3,z4,z10,z844]),(0,[z0,z2,z921,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z922])],[(0,[z0,z2,z3,z4,z5,z923]),(0,[z0,z2,z3,z4,z200,z6]),(0,[z0,z2,z3,z4,z924,z6])],[(0,[z0,z2,z3,z925,z10,z6]),(0,[z0,z2,z3,z4,z6,z926])],[(0,[z0,z2,z3,z927,z10,z6]),(0,[z37,z29,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z928,z6]),(0,[z0,z2,z3,z4,z929,z6]),(0,[z0,z73,z3,z4,z5,z147]),(0,[z0,z82,z2,z3,z5,z6]),(0,[z0,z23,z2,z3,z4,z183]),(0,[z0,z2,z3,z4,z10,z930])],[(0,[z0,z2,z3,z158,z5,z6]),(0,[z0,z78,z3,z222,z10,z6]),(0,[z135,z2,z53,z4,z136,z6]),(0,[z0,z2,z3,z4,z10,z931]),(0,[z0,z164,z2,z98,z10,z6]),(0,[z0,z54,z3,z4,z183,z139]),(0,[z0,z932,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z744,z185])]],
   [[(0,[z0,z2,z3,z222,z10,z6]),(0,[z70,z2,z3,z4,z5,z6]),(0,[z0,z933,z2,z3,z4,z6]),(0,[z0,z82,z2,z3,z10,z140]),(0,[z0,z2,z3,z4,z10,z934]),(0,[z0,z935,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z936,z6]),(0,[z0,z2,z3,z4,z347,z162])],[(0,[z0,z2,z3,z4,z730,z10]),(0,[z0,z2,z3,z4,z10,z937]),(0,[z0,z2,z724,z4,z8,z6])],[(0,[z0,z2,z3,z4,z938,z6]),(0,[z0,z2,z3,z4,z939,z6]),(1,[z0,z2,z4,z10,z810]),(0,[z0,z2,z3,z10,z733,z110])],[(0,[z0,z2,z940,z4,z10,z6]),(0,[z0,z2,z3,z4,z941,z6]),(0,[z0,z2,z3,z4,z10,z942])],[(0,[z0,z2,z3,z4,z224,z74]),(0,[z0,z943,z2,z3,z10,z6]),(0,[z0,z2,z3,z4,z10,z944]),(0,[z0,z89,z2,z3,z4,z703]),(0,[z0,z323,z2,z4,z10,z131]),(0,[z0,z26,z2,z3,z10,z733])],[(0,[z0,z945,z2,z3,z4,z6]),(0,[z0,z267,z32,z4,z8,z6]),(0,[z946,z2,z3,z4,z10,z6]),(1,[z0,z3,z4,z10,z907]),(0,[z0,z2,z3,z4,z10,z239])],[(0,[z0,z12,z205,z4,z10,z6]),(0,[z79,z2,z3,z72,z10,z6]),(0,[z0,z2,z3,z4,z947,z6]),(0,[z0,z948,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z309])]],
   [[(0,[z0,z2,z3,z4,z10,z949])],[(0,[z0,z78,z34,z4,z10,z6]),(0,[z0,z78,z3,z194,z10,z6]),(0,[z2,z3,z4,z153,z5,z6]),(0,[z0,z2,z3,z4,z5,z950]),(0,[z0,z2,z138,z4,z8,z6]),(0,[z0,z2,z3,z4,z10,z951]),(0,[z0,z54,z3,z4,z181,z6])],[(0,[z0,z2,z3,z158,z479,z6]),(0,[z0,z2,z952,z4,z10,z6]),(0,[z0,z2,z3,z194,z10,z6]),(0,[z0,z2,z953,z4,z10,z6]),(0,[z0,z23,z2,z3,z4,z347]),(0,[z0,z2,z3,z4,z954,z6]),(0,[z0,z2,z3,z4,z6,z955]),(0,[z0,z42,z246,z3,z4,z6]),(0,[z0,z81,z2,z94,z10,z265]),(0,[z0,z26,z2,z3,z10,z350])],[(0,[z0,z3,z4,z10,z6,z956]),(0,[z0,z2,z3,z4,z10,z957]),(0,[z0,z2,z3,z4,z27,z421])],[(0,[z0,z2,z3,z4,z958,z6]),(0,[z0,z2,z215,z4,z5,z56]),(0,[z0,z959,z2,z3,z4,z6]),(0,[z0,z17,z3,z598,z4,z10])],[(0,[z0,z2,z3,z4,z960,z6]),(0,[z0,z2,z3,z961,z10,z6]),(0,[z88,z2,z3,z276,z10,z179]),(0,[z0,z2,z3,z95,z4,z358]),(0,[z0,z3,z4,z10,z907,z18]),(0,[z0,z2,z3,z95,z41,z6]),(0,[z0,z2,z3,z33,z10,z733]),(1,[z0,z2,z3,z4,z744]),(0,[z0,z2,z3,z4,z6,z744])],[(0,[z0,z2,z3,z4,z322,z56]),(0,[z0,z148,z2,z747,z10,z6])],[(0,[z0,z2,z3,z4,z962,z6]),(0,[z0,z2,z3,z305,z5,z6]),(0,[z963,z2,z3,z4,z10,z6])]],
   [[(0,[z14,z78,z15,z4,z10,z6]),(0,[z2,z3,z374,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z753]),(0,[z0,z2,z3,z4,z964,z6]),(0,[z0,z164,z2,z4,z10,z934]),(0,[z0,z272,z2,z3,z4,z6])],[(0,[z0,z2,z451,z4,z10,z74]),(0,[z14,z2,z15,z4,z10,z6]),(0,[z0,z89,z2,z3,z276,z10]),(0,[z0,z2,z3,z276,z200,z6]),(0,[z0,z2,z3,z33,z10,z75])],[(0,[z0,z26,z2,z3,z10,z377]),(0,[z508,z2,z3,z4,z8,z6]),(0,[z662,z2,z3,z4,z10,z179]),(0,[z0,z2,z3,z4,z10,z358]),(0,[z0,z2,z3,z4,z965,z6])],[(0,[z0,z2,z3,z158,z10,z68]),(0,[z0,z2,z3,z4,z5,z74]),(0,[z0,z2,z3,z10,z807,z6]),(0,[z651,z2,z3,z4,z5,z6]),(0,[z0,z710,z2,z3,z4,z265])],[(0,[z37,z29,z3,z4,z106,z6]),(0,[z187,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z578,z234,z6]),(0,[z0,z2,z3,z4,z6,z966]),(0,[z0,z23,z2,z3,z4,z10]),(0,[z0,z164,z2,z4,z8,z6]),(0,[z967,z2,z3,z4,z10,z6]),(0,[z0,z243,z3,z98,z10,z6])],[(0,[z0,z2,z3,z4,z968,z6]),(0,[z0,z2,z61,z4,z476,z6]),(0,[z0,z2,z3,z4,z474,z6]),(0,[z0,z2,z3,z4,z10,z969])],[(0,[z28,z12,z205,z4,z10,z6]),(0,[z2,z395,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z124,z6]),(0,[z0,z42,z3,z4,z712,z6]),(0,[z0,z2,z45,z4,z20,z521]),(0,[z0,z2,z3,z4,z10,z287])],[(0,[z0,z2,z3,z222,z163,z6]),(0,[z85,z2,z3,z100,z86,z6]),(0,[z0,z2,z3,z4,z10,z772]),(0,[z0,z82,z2,z3,z10,z179]),(0,[z2,z3,z4,z970,z10,z6])]],
   [[(0,[z0,z78,z3,z4,z10,z437]),(0,[z0,z2,z3,z4,z10,z971]),(0,[z0,z2,z3,z4,z10,z972])],[(0,[z0,z2,z3,z4,z10,z437]),(0,[z0,z973,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z371]),(0,[z0,z823,z2,z3,z4,z10]),(0,[z0,z2,z3,z4,z423,z257]),(0,[z0,z2,z3,z4,z8,z257]),(0,[z0,z2,z3,z4,z974,z6]),(0,[z0,z2,z893,z3,z4,z5]),(0,[z0,z2,z3,z4,z10,z265]),(0,[z0,z81,z2,z94,z10,z309])],[(0,[z0,z2,z3,z4,z975,z6]),(0,[z0,z976,z3,z4,z10,z6]),(0,[z85,z2,z3,z100,z423,z6]),(0,[z85,z2,z3,z100,z8,z6]),(0,[z70,z2,z3,z4,z347,z5])],[(0,[z0,z2,z3,z4,z977,z6]),(0,[z0,z2,z3,z4,z978,z6]),(0,[z0,z979,z3,z4,z10,z6]),(0,[z0,z82,z2,z3,z10,z110])],[(0,[z0,z980,z2,z3,z4,z10]),(0,[z0,z981,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z982]),(0,[z983,z2,z3,z4,z10,z6]),(0,[z0,z984,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z10,z923]),(0,[z0,z2,z3,z4,z985,z10]),(0,[z88,z2,z3,z38,z10,z179]),(0,[z0,z2,z4,z10,z787,z6])],[(0,[z0,z2,z3,z4,z986,z6]),(0,[z0,z2,z3,z4,z479,z74])],[(0,[z37,z29,z3,z4,z10,z6]),(0,[z0,z2,z451,z4,z5,z6]),(0,[z0,z2,z3,z4,z987,z10]),(0,[z2,z3,z4,z711,z5,z6]),(0,[z679,z2,z3,z4,z5,z6]),(0,[z0,z23,z2,z3,z4,z27]),(0,[z113,z2,z3,z4,z711,z6]),(0,[z35,z2,z3,z4,z8,z6]),(0,[z0,z206,z2,z107,z10,z6]),(0,[z0,z73,z3,z4,z10,z147]),(0,[z0,z82,z2,z3,z10,z6])]],
   [[(0,[z0,z2,z3,z158,z10,z6]),(0,[z79,z2,z3,z794,z10,z6]),(0,[z85,z2,z3,z794,z10,z6]),(0,[z378,z0,z2,z3,z482,z6]),(0,[z0,z2,z988,z4,z8,z6]),(0,[z989,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z194,z163,z6]),(0,[z0,z786,z2,z4,z10,z6]),(0,[z0,z2,z3,z38,z200,z6]),(0,[z0,z81,z2,z413,z10,z6]),(0,[z0,z2,z3,z343,z4,z474]),(0,[z0,z2,z3,z4,z990,z6])],[(0,[z0,z991,z3,z4,z10,z6]),(0,[z0,z17,z3,z4,z10,z907]),(0,[z0,z1,z2,z4,z10,z131])],[(0,[z0,z2,z3,z4,z992,z10]),(0,[z14,z660,z2,z4,z10,z6]),(0,[z0,z2,z3,z794,z10,z6]),(0,[z2,z3,z4,z5,z161,z6]),(0,[z0,z993,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z321,z6])],[(0,[z0,z2,z994,z4,z10,z6]),(0,[z0,z2,z3,z4,z93,z6]),(0,[z0,z689,z2,z34,z10,z6]),(0,[z0,z2,z3,z995,z10,z6]),(0,[z0,z2,z3,z4,z10,z996]),(0,[z0,z2,z3,z10,z997,z6]),(0,[z0,z89,z2,z3,z4,z128])],[(0,[z0,z2,z3,z4,z998,z6]),(0,[z0,z2,z3,z4,z5,z521]),(0,[z0,z73,z3,z4,z322,z147]),(0,[z0,z214,z3,z4,z10,z147])],[(0,[z0,z2,z3,z4,z711,z6]),(0,[z121,z0,z2,z3,z280,z6]),(0,[z0,z2,z3,z33,z10,z600])],[(0,[z0,z2,z3,z4,z224,z68]),(0,[z0,z2,z3,z4,z999,z6]),(0,[z0,z2,z3,z1000,z10,z6]),(0,[z22,z0,z23,z2,z3,z4]),(0,[z2,z3,z4,z428,z8,z6]),(0,[z0,z2,z3,z4,z10,z1001]),(0,[z0,z2,z3,z4,z322,z18])]],
   [[(0,[z0,z2,z3,z4,z1002,z6]),(0,[z0,z881,z267,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z1003]),(0,[z0,z3,z4,z10,z147,z907]),(0,[z0,z2,z3,z4,z10,z309]),(0,[z0,z2,z3,z4,z10,z1004])],[(0,[z0,z2,z3,z4,z1005,z6]),(0,[z0,z1006,z3,z4,z10,z6]),(0,[z0,z2,z3,z1007,z10,z6]),(0,[z0,z2,z3,z4,z1008,z6]),(0,[z0,z2,z463,z4,z10,z131])],[(0,[z0,z2,z451,z4,z479,z6]),(0,[z0,z2,z3,z291,z5,z6]),(0,[z0,z2,z3,z4,z10,z950]),(0,[z2,z3,z4,z8,z5,z6]),(0,[z2,z3,z4,z8,z564,z6]),(0,[z80,z2,z3,z4,z228,z140]),(0,[z0,z202,z3,z725,z10,z6]),(0,[z0,z2,z3,z4,z162,z355]),(0,[z0,z2,z3,z4,z1009,z6])],[(0,[z0,z329,z2,z98,z10,z6])],[(0,[z0,z17,z3,z4,z5,z18]),(0,[z261,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1010,z10,z6]),(0,[z0,z2,z3,z1011,z10,z6]),(0,[z0,z26,z2,z3,z314,z10])],[(0,[z0,z2,z3,z1012,z10,z6]),(0,[z0,z2,z3,z4,z1013,z6]),(0,[z244,z2,z3,z100,z10,z6]),(0,[z0,z2,z215,z4,z10,z56]),(0,[z0,z2,z3,z4,z1014,z6])],[(0,[z28,z12,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z10,z1015]),(0,[z0,z1016,z2,z4,z10,z6]),(0,[z0,z243,z3,z343,z98,z10]),(0,[z0,z2,z1017,z4,z10,z6])],[(0,[z0,z2,z205,z4,z10,z6]),(0,[z0,z1018,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z1019]),(0,[z0,z2,z3,z4,z228,z6]),(0,[z0,z2,z3,z8,z255,z6])]],
   [[(0,[z0,z2,z4,z5,z1020,z6]),(0,[z0,z2,z3,z4,z10,z833]),(0,[z0,z2,z3,z305,z10,z6]),(0,[z0,z2,z4,z747,z10,z6])],[(0,[z0,z2,z3,z4,z1021,z6]),(0,[z0,z1022,z3,z4,z10,z6]),(0,[z0,z2,z3,z873,z51,z6])],[(0,[z0,z2,z1023,z4,z10,z6]),(0,[z28,z12,z3,z291,z10,z6]),(0,[z37,z29,z3,z4,z65,z6]),(0,[z0,z1024,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z1025]),(0,[z0,z426,z3,z4,z248,z6]),(0,[z0,z2,z3,z4,z10,z1026]),(0,[z22,z0,z582,z2,z3,z51])],[(0,[z0,z2,z451,z4,z10,z68]),(0,[z662,z2,z3,z100,z10,z6]),(0,[z0,z2,z3,z4,z1027,z6]),(0,[z0,z2,z3,z4,z1028,z6]),(0,[z0,z2,z3,z33,z10,z247])],[(0,[z0,z2,z3,z4,z224,z6]),(0,[z0,z2,z3,z276,z27,z10]),(0,[z0,z243,z3,z294,z98,z10]),(0,[z0,z81,z2,z349,z10,z6]),(0,[z0,z2,z3,z4,z10,z1029])],[(0,[z0,z2,z3,z291,z479,z6]),(0,[z0,z2,z3,z4,z5,z68]),(0,[z0,z2,z3,z4,z1030,z6]),(0,[z0,z2,z3,z4,z284,z312]),(0,[z88,z2,z3,z4,z231,z10]),(0,[z0,z2,z3,z4,z10,z1031])],[(0,[z0,z2,z3,z488,z10,z75]),(0,[z0,z26,z2,z3,z4,z322])],[(0,[z0,z2,z3,z1032,z10,z6]),(0,[z0,z2,z3,z4,z1033,z6]),(0,[z0,z2,z3,z343,z100,z10]),(0,[z0,z19,z2,z4,z101,z6])]],
   [[(0,[z0,z2,z3,z4,z10,z1034]),(0,[z0,z2,z3,z4,z1035,z6]),(0,[z0,z2,z3,z1036,z10,z6]),(0,[z0,z81,z2,z94,z8,z6]),(0,[z562,z2,z3,z4,z8,z6])],[(0,[z0,z78,z3,z4,z10,z371]),(0,[z79,z2,z299,z72,z10,z6]),(0,[z0,z2,z3,z276,z93,z6]),(0,[z0,z1037,z3,z4,z10,z6])],[(0,[z0,z2,z3,z1038,z10,z6]),(0,[z0,z2,z3,z4,z10,z371]),(0,[z2,z3,z4,z5,z433,z6])],[(0,[z0,z2,z3,z1039,z10,z6]),(0,[z0,z2,z4,z10,z1020,z6]),(0,[z0,z2,z3,z4,z5,z1040]),(0,[z0,z2,z3,z178,z416,z6]),(0,[z0,z2,z3,z4,z1041,z6])],[(0,[z0,z2,z1042,z4,z10,z6]),(0,[z0,z164,z202,z203,z10,z6]),(0,[z0,z2,z1043,z4,z10,z6]),(0,[z0,z2,z215,z4,z10,z810]),(0,[z0,z2,z3,z41,z873,z6]),(0,[z0,z2,z3,z10,z6,z733])],[(0,[z0,z2,z1044,z4,z10,z6]),(0,[z0,z1045,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1046,z6]),(0,[z0,z2,z3,z4,z1047,z6]),(0,[z135,z2,z698,z4,z10,z6]),(0,[z0,z23,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z1048,z6]),(0,[z0,z2,z3,z4,z322,z147])],[(0,[z0,z2,z3,z4,z1049,z6]),(0,[z0,z2,z1050,z4,z10,z6])]],
   [[(0,[z0,z2,z451,z4,z10,z6]),(0,[z0,z2,z3,z4,z479,z68]),(0,[z113,z2,z3,z4,z8,z6]),(0,[z2,z3,z4,z711,z10,z6])],[],[(0,[z0,z2,z3,z4,z1051,z6]),(0,[z80,z2,z3,z4,z8,z140]),(0,[z0,z1052,z2,z3,z10,z6]),(0,[z0,z2,z3,z4,z1053,z6])],[(0,[z0,z29,z205,z4,z10,z6]),(0,[z0,z2,z3,z1054,z10,z6]),(0,[z0,z78,z3,z4,z541,z6]),(0,[z79,z329,z2,z72,z10,z6]),(0,[z0,z2,z3,z4,z8,z139]),(0,[z0,z2,z3,z4,z10,z1055]),(0,[z0,z2,z3,z1056,z4,z10])],[(0,[z0,z2,z3,z4,z1057,z6]),(0,[z0,z2,z3,z4,z541,z6]),(0,[z0,z304,z3,z222,z10,z6]),(0,[z0,z304,z3,z4,z163,z6]),(0,[z0,z2,z3,z4,z1058,z6]),(0,[z0,z2,z3,z4,z86,z6]),(0,[z0,z267,z32,z4,z5,z6]),(0,[z0,z242,z2,z4,z319,z6]),(0,[z637,z2,z3,z4,z8,z6]),(0,[z0,z89,z82,z2,z3,z10])],[(0,[z0,z2,z3,z4,z1059,z6]),(0,[z119,z29,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z1060]),(0,[z0,z2,z3,z4,z10,z1061]),(0,[z79,z2,z3,z72,z328,z6]),(0,[z0,z2,z3,z1062,z10,z6]),(1,[z0,z2,z4,z787,z6])],[(0,[z0,z78,z3,z4,z8,z6]),(0,[z0,z329,z2,z194,z10,z6]),(0,[z0,z242,z2,z4,z325,z6]),(0,[z0,z164,z2,z203,z10,z6]),(0,[z0,z2,z3,z4,z10,z1063]),(0,[z0,z2,z3,z4,z10,z521]),(0,[z0,z2,z3,z4,z421,z6]),(0,[z0,z82,z2,z3,z10,z75])],[(0,[z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z423,z6]),(0,[z0,z2,z138,z4,z5,z6]),(0,[z0,z148,z2,z34,z8,z6]),(0,[z0,z801,z2,z3,z4,z8]),(0,[z0,z1064,z2,z4,z10,z6]),(0,[z0,z1065,z2,z4,z10,z6])]],
   [[(0,[z0,z2,z3,z1066,z10,z6]),(0,[z0,z2,z1067,z4,z10,z6]),(0,[z0,z2,z3,z4,z8,z734]),(0,[z0,z83,z2,z4,z10,z131]),(0,[z1068,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z1069,z6]),(0,[z22,z0,z582,z2,z3,z4]),(0,[z0,z2,z3,z4,z27,z376])],[(0,[z0,z2,z3,z1070,z10,z6]),(0,[z0,z2,z3,z4,z987,z5]),(0,[z0,z2,z3,z38,z93,z6]),(0,[z0,z2,z3,z4,z6,z1071])],[(0,[z28,z12,z3,z158,z10,z6]),(0,[z0,z2,z3,z1072,z4,z10]),(0,[z0,z329,z2,z94,z10,z6]),(0,[z0,z2,z3,z4,z10,z1073]),(0,[z1074,z2,z3,z4,z10,z6]),(0,[z0,z582,z2,z3,z95,z4]),(0,[z0,z2,z3,z4,z162,z744])],[(0,[z0,z2,z3,z291,z10,z6]),(0,[z0,z2,z3,z1075,z4,z10])],[(0,[z0,z2,z3,z1076,z10,z6]),(0,[z0,z89,z2,z3,z4,z744])],[(0,[z0,z2,z34,z599,z10,z6]),(0,[z0,z2,z3,z4,z27,z200]),(0,[z0,z2,z3,z4,z10,z1077]),(0,[z0,z2,z3,z4,z712,z6]),(0,[z0,z17,z3,z4,z10,z18]),(0,[z0,z2,z3,z4,z796,z6]),(1,[z0,z2,z3,z873,z6])],[(0,[z0,z304,z3,z194,z10,z6]),(0,[z88,z2,z3,z4,z200,z179]),(0,[z0,z1078,z2,z3,z4,z6]),(0,[z0,z218,z2,z3,z4,z6])],[(0,[z2,z3,z4,z794,z10,z6]),(0,[z132,z2,z3,z4,z8,z6]),(0,[z0,z102,z3,z98,z10,z6])]],
   [[(0,[z0,z2,z3,z4,z10,z1079]),(0,[z0,z2,z3,z1080,z10,z6]),(0,[z0,z2,z3,z4,z10,z1081]),(0,[z0,z2,z3,z10,z1082,z6]),(0,[z0,z2,z1083,z4,z10,z6]),(0,[z0,z1084,z3,z4,z5,z6])],[(1,[z788,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z163,z371]),(0,[z0,z23,z2,z3,z4,z126]),(0,[z681,z2,z3,z4,z10,z140])],[(0,[z0,z3,z4,z10,z1085,z6]),(0,[z0,z164,z2,z4,z5,z6])],[(0,[z0,z2,z1086,z4,z10,z6]),(0,[z0,z2,z4,z10,z6,z1087]),(0,[z0,z2,z3,z4,z6,z1088]),(0,[z0,z23,z2,z3,z4,z228]),(0,[z0,z2,z3,z4,z1089,z6])],[(0,[z0,z2,z3,z4,z1090,z6]),(0,[z0,z2,z3,z1091,z10,z6]),(0,[z0,z54,z3,z4,z712,z6]),(0,[z0,z2,z4,z10,z810,z6])],[(0,[z0,z2,z1092,z4,z10,z6]),(0,[z14,z304,z15,z4,z10,z6]),(0,[z2,z3,z4,z10,z844,z140]),(0,[z0,z26,z2,z3,z10,z265])],[(0,[z0,z2,z4,z10,z1093,z6]),(0,[z0,z2,z3,z4,z10,z1094]),(0,[z0,z1095,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z5,z257]),(0,[z432,z2,z3,z4,z5,z6]),(0,[z0,z23,z242,z2,z3,z4]),(0,[z0,z2,z3,z4,z1096,z6])]],
   [[(0,[z0,z329,z26,z2,z10,z6]),(0,[z85,z2,z3,z100,z5,z6]),(0,[z0,z881,z32,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z1097])],[(0,[z135,z2,z53,z4,z8,z6]),(0,[z444,z2,z3,z72,z10,z6]),(0,[z0,z2,z3,z4,z86,z257]),(0,[z0,z770,z3,z4,z10,z6]),(0,[z0,z148,z2,z3,z343,z10])],[(0,[z0,z2,z3,z4,z1098,z6]),(0,[z0,z2,z3,z4,z1099,z6]),(0,[z0,z2,z3,z4,z10,z810])],[],[(0,[z0,z2,z3,z4,z10,z1040]),(0,[z0,z2,z3,z276,z8,z6]),(0,[z0,z2,z4,z8,z902,z6]),(0,[z0,z2,z3,z1100,z10,z6]),(0,[z0,z19,z2,z4,z787,z6]),(0,[z0,z89,z2,z3,z4,z84])],[(0,[z0,z2,z3,z4,z10,z1101]),(0,[z0,z304,z3,z4,z10,z437]),(1,[z0,z3,z4,z712,z6]),(0,[z0,z218,z2,z3,z4,z131]),(0,[z1102,z2,z3,z4,z10,z6])],[(0,[z28,z12,z3,z4,z224,z6]),(0,[z28,z12,z3,z4,z10,z74]),(0,[z0,z1045,z3,z4,z10,z6]),(0,[z70,z2,z3,z4,z711,z6]),(0,[z0,z2,z3,z4,z27,z228]),(0,[z0,z2,z3,z4,z882,z6]),(0,[z0,z2,z3,z4,z1103,z6])],[]],
   [[(0,[z0,z1104,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z86,z473]),(0,[z0,z23,z2,z45,z3,z4]),(0,[z0,z2,z3,z4,z347,z200]),(0,[z0,z218,z26,z2,z3,z110])],[(0,[z0,z19,z2,z696,z4,z6]),(0,[z0,z2,z3,z4,z162,z239])],[(0,[z0,z2,z4,z10,z1105,z6]),(0,[z0,z2,z3,z4,z1106,z6]),(0,[z0,z2,z3,z4,z1107,z6]),(0,[z0,z2,z3,z4,z1108,z6])],[(0,[z0,z2,z3,z4,z423,z473]),(0,[z0,z2,z3,z4,z8,z473]),(0,[z0,z2,z3,z4,z43,z358])],[(0,[z0,z190,z32,z4,z10,z6]),(0,[z0,z2,z3,z4,z8,z239]),(0,[z0,z2,z3,z4,z10,z1109]),(0,[z1110,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z1111,z10,z6]),(0,[z0,z2,z3,z4,z10,z1112]),(0,[z0,z2,z3,z4,z1113,z6]),(0,[z79,z2,z3,z72,z8,z6]),(0,[z0,z2,z3,z4,z1114,z6]),(0,[z0,z1115,z2,z3,z4,z6]),(0,[z0,z267,z32,z4,z10,z6])],[(0,[z0,z2,z3,z4,z1116,z6]),(0,[z0,z2,z3,z4,z201,z6]),(0,[z0,z2,z3,z4,z10,z1117]),(0,[z0,z311,z3,z203,z10,z6]),(0,[z313,z2,z3,z4,z5,z6]),(0,[z0,z984,z2,z3,z4,z367]),(0,[z0,z1118,z2,z3,z10,z6])],[(0,[z23,z2,z3,z4,z8,z5]),(0,[z0,z2,z3,z10,z6,z1119])]],
   [[(0,[z0,z2,z3,z4,z10,z1120]),(0,[z0,z2,z3,z4,z10,z1121]),(0,[z0,z2,z3,z194,z8,z6]),(0,[z0,z2,z953,z4,z8,z6]),(0,[z117,z2,z3,z4,z8,z6]),(0,[z0,z2,z138,z4,z10,z6]),(0,[z0,z2,z3,z4,z183,z358]),(0,[z0,z26,z2,z3,z318,z10]),(0,[z0,z81,z2,z180,z10,z6]),(0,[z0,z2,z34,z747,z10,z6])],[(0,[z0,z2,z3,z72,z10,z473]),(0,[z0,z2,z1122,z4,z10,z6]),(0,[z0,z2,z3,z4,z322,z6]),(0,[z0,z73,z3,z4,z10,z441]),(0,[z0,z2,z3,z4,z1123,z6]),(0,[z0,z2,z45,z4,z6,z429])],[(0,[z28,z12,z451,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z1124]),(0,[z0,z1125,z3,z4,z10,z6])],[(0,[z14,z2,z15,z222,z10,z6]),(0,[z14,z2,z15,z4,z163,z6]),(0,[z0,z2,z3,z4,z341,z162]),(0,[z0,z89,z2,z3,z4,z360])],[(0,[z2,z3,z750,z4,z10,z6]),(0,[z0,z2,z3,z38,z8,z6]),(0,[z22,z0,z2,z3,z482,z6]),(0,[z0,z1126,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z10,z1127]),(0,[z0,z2,z747,z94,z10,z6])],[(0,[z0,z554,z32,z4,z10,z6])],[(0,[z481,z12,z3,z4,z10,z6]),(0,[z0,z2,z34,z194,z10,z6]),(1,[z2,z750,z4,z10,z6]),(0,[z0,z2,z3,z4,z1128,z6])],[(0,[z0,z980,z2,z3,z4,z106]),(0,[z0,z54,z3,z4,z183,z358])]],
   [[(0,[z593,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z1129,z6])],[(0,[z0,z1084,z3,z4,z10,z6]),(0,[z0,z827,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z10,z1130]),(0,[z0,z329,z2,z203,z10,z6]),(0,[z0,z2,z3,z4,z1131,z6])],[(0,[z0,z2,z3,z222,z10,z437]),(0,[z0,z2,z3,z4,z163,z437]),(0,[z0,z2,z3,z4,z10,z1132]),(0,[z0,z148,z2,z583,z10,z6])],[(0,[z0,z2,z3,z10,z1133,z6]),(0,[z0,z2,z45,z4,z300,z6]),(0,[z0,z2,z3,z4,z8,z287]),(0,[z2,z3,z4,z10,z844,z6])],[(0,[z14,z2,z15,z194,z10,z6]),(0,[z0,z2,z3,z343,z72,z10]),(0,[z481,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z347,z10]),(0,[z211,z2,z3,z4,z8,z6]),(0,[z401,z2,z3,z4,z10,z140]),(0,[z2,z3,z4,z10,z179,z844]),(0,[z1134,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z1135,z10,z6])],[(0,[z0,z2,z3,z1136,z10,z6]),(0,[z0,z2,z3,z4,z992,z106]),(0,[z0,z2,z3,z1137,z10,z6]),(0,[z0,z81,z2,z94,z5,z6]),(0,[z0,z3,z4,z5,z1138,z6]),(0,[z88,z2,z3,z4,z93,z179]),(0,[z0,z2,z45,z4,z20,z6])],[(0,[z0,z2,z3,z4,z10,z74]),(0,[z28,z12,z3,z4,z479,z6])]],
   [[(0,[z0,z546,z2,z3,z4,z6]),(0,[z0,z2,z3,z294,z4,z10]),(0,[z0,z2,z3,z4,z322,z131])],[(0,[z0,z2,z3,z4,z10,z1139]),(0,[z85,z2,z3,z100,z10,z6]),(0,[z0,z2,z299,z4,z8,z6]),(0,[z0,z3,z725,z98,z10,z6])],[(0,[z0,z2,z205,z4,z224,z6]),(0,[z788,z12,z3,z4,z10,z6]),(0,[z0,z2,z1140,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z1141]),(0,[z2,z3,z4,z5,z6,z425])],[(0,[z0,z78,z53,z4,z10,z6]),(0,[z0,z146,z3,z98,z10,z6]),(0,[z0,z2,z3,z4,z5,z1142]),(0,[z0,z23,z2,z3,z578,z4])],[(0,[z0,z1143,z2,z3,z5,z6])],[(0,[z0,z2,z3,z194,z10,z437])],[(0,[z0,z2,z3,z1144,z10,z6]),(0,[z0,z304,z3,z4,z10,z371]),(0,[z223,z2,z3,z4,z5,z6]),(0,[z0,z420,z3,z4,z10,z18])],[(0,[z0,z2,z3,z107,z8,z6]),(0,[z0,z26,z2,z3,z8,z110]),(0,[z0,z2,z988,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z844]),(0,[z0,z2,z3,z725,z10,z6]),(0,[z0,z3,z4,z725,z10,z6]),(0,[z0,z2,z3,z4,z1145,z6])]],
   [[(0,[z0,z2,z1146,z4,z10,z6]),(0,[z28,z12,z3,z4,z10,z68]),(0,[z80,z2,z3,z4,z5,z140]),(0,[z0,z2,z3,z4,z10,z1147]),(0,[z0,z89,z2,z3,z4,z405]),(0,[z0,z2,z4,z20,z787,z6])],[(0,[z0,z3,z4,z10,z1138,z6]),(0,[z0,z2,z3,z1148,z10,z6]),(0,[z0,z2,z3,z4,z6,z1149]),(0,[z0,z2,z3,z4,z5,z139]),(0,[z1150,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z1151,z6]),(0,[z0,z2,z3,z4,z1152,z6]),(0,[z0,z2,z3,z33,z4,z322]),(0,[z0,z1153,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z1154,z6]),(0,[z0,z202,z3,z203,z8,z6]),(0,[z0,z2,z3,z1155,z10,z6])],[(0,[z0,z2,z3,z1156,z10,z6]),(0,[z0,z1157,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z10,z1158]),(0,[z0,z329,z2,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z722]),(0,[z0,z2,z3,z4,z873,z6])],[(0,[z0,z78,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1159,z6]),(0,[z14,z2,z15,z4,z10,z437]),(0,[z0,z89,z2,z3,z4,z185])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z148,z2,z34,z5,z6]),(0,[z0,z23,z19,z2,z3,z4]),(0,[z121,z0,z2,z3,z51,z6]),(0,[z0,z218,z26,z2,z3,z4])],[(0,[z481,z2,z15,z4,z10,z6]),(0,[z0,z329,z2,z4,z10,z1073]),(0,[z0,z2,z3,z4,z1160,z6])],[(0,[z0,z2,z3,z4,z1161,z6]),(0,[z0,z2,z3,z4,z1162,z6])]],
   [[(0,[z0,z2,z1163,z4,z10,z6]),(0,[z0,z2,z3,z4,z1164,z6]),(0,[z0,z1165,z2,z3,z4,z10])],[(0,[z0,z2,z3,z4,z1166,z6]),(0,[z0,z272,z2,z3,z255,z6]),(0,[z22,z0,z2,z3,z287,z51])],[(0,[z0,z2,z3,z4,z10,z874])],[(0,[z0,z76,z440,z4,z10,z6]),(0,[z0,z304,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z1167,z6]),(0,[z530,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z10,z1168]),(0,[z375,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z1169,z6]),(0,[z0,z1170,z2,z3,z4,z10])],[(0,[z0,z2,z205,z4,z8,z6]),(0,[z0,z2,z3,z4,z10,z1171]),(0,[z0,z81,z2,z747,z10,z6])],[(0,[z0,z2,z1172,z4,z10,z6]),(0,[z85,z2,z3,z100,z10,z257]),(0,[z171,z2,z3,z4,z8,z6]),(0,[z0,z886,z3,z4,z8,z6]),(0,[z0,z89,z2,z3,z4,z442]),(0,[z0,z2,z3,z4,z1173,z6]),(0,[z22,z0,z2,z3,z873,z6])],[(0,[z0,z2,z3,z4,z985,z134]),(1,[z0,z3,z725,z10,z6]),(0,[z0,z2,z3,z4,z10,z1174]),(0,[z0,z272,z82,z2,z3,z6])]],
   [[(0,[z0,z2,z3,z4,z479,z6]),(0,[z0,z2,z3,z4,z10,z1175]),(0,[z0,z3,z4,z10,z910,z6]),(0,[z0,z164,z2,z4,z10,z1147])],[(0,[z0,z2,z3,z4,z10,z1176]),(0,[z0,z2,z205,z291,z10,z6]),(0,[z0,z2,z3,z4,z8,z367]),(0,[z0,z2,z3,z4,z10,z1177])],[(0,[z0,z2,z3,z4,z8,z172]),(0,[z0,z2,z3,z4,z10,z1178]),(0,[z0,z2,z3,z4,z10,z1179]),(0,[z0,z3,z4,z10,z907,z6]),(0,[z0,z82,z2,z3,z10,z265]),(0,[z0,z2,z215,z10,z255,z56])],[(0,[z0,z2,z3,z1180,z10,z6]),(0,[z0,z81,z2,z194,z10,z6]),(0,[z0,z1181,z2,z3,z4,z6]),(0,[z0,z2,z45,z4,z20,z239]),(0,[z0,z2,z4,z10,z131,z810]),(1,[z0,z2,z3,z10,z733])],[(0,[z0,z2,z3,z222,z10,z371]),(0,[z0,z2,z3,z4,z10,z1182]),(0,[z0,z2,z3,z4,z1183,z6])],[(0,[z0,z2,z3,z4,z1184,z6]),(0,[z0,z49,z32,z4,z10,z6]),(0,[z0,z1185,z2,z3,z4,z6]),(0,[z85,z2,z3,z100,z10,z473]),(0,[z2,z3,z670,z4,z5,z6]),(0,[z0,z881,z3,z4,z10,z6]),(0,[z0,z81,z2,z3,z343,z10]),(0,[z0,z2,z3,z10,z873,z6])],[(0,[z0,z2,z3,z4,z1186,z6]),(0,[z0,z2,z3,z4,z1187,z6]),(0,[z0,z2,z629,z4,z10,z56]),(0,[z0,z218,z2,z3,z33,z4])],[(0,[z0,z2,z3,z4,z1188,z6]),(0,[z135,z2,z53,z4,z5,z6]),(0,[z0,z2,z3,z4,z1189,z6]),(0,[z0,z81,z2,z94,z10,z6])]],
   [[(0,[z0,z23,z2,z3,z4,z8]),(0,[z0,z2,z3,z1190,z10,z6]),(0,[z0,z17,z3,z4,z10,z21])],[(0,[z0,z2,z3,z4,z10,z68]),(0,[z0,z901,z2,z3,z4,z328]),(0,[z88,z2,z3,z4,z8,z179]),(0,[z80,z2,z3,z4,z10,z844]),(0,[z2,z3,z4,z1191,z10,z6]),(0,[z0,z2,z3,z4,z10,z1192]),(0,[z0,z2,z3,z1193,z4,z10]),(0,[z0,z73,z82,z2,z3,z10]),(0,[z0,z1194,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z1195,z6])],[(0,[z0,z1196,z3,z4,z10,z6]),(0,[z0,z2,z3,z276,z5,z6]),(0,[z0,z2,z3,z4,z6,z1197]),(0,[z0,z73,z3,z4,z10,z907]),(0,[z0,z1198,z2,z3,z4,z10])],[(0,[z0,z2,z3,z4,z106,z6]),(0,[z0,z2,z3,z4,z10,z1199]),(0,[z0,z2,z3,z4,z5,z783]),(0,[z1200,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z10,z1142]),(0,[z0,z2,z3,z276,z10,z140]),(0,[z0,z73,z3,z4,z321,z147]),(0,[z0,z2,z3,z4,z787,z6])],[(0,[z0,z1143,z2,z3,z10,z6]),(0,[z0,z1201,z2,z3,z4,z6]),(0,[z0,z2,z3,z1202,z10,z6]),(0,[z0,z1203,z2,z3,z4,z6]),(0,[z0,z2,z3,z178,z41,z6])],[(0,[z0,z2,z3,z194,z10,z371]),(0,[z0,z2,z3,z222,z541,z6])],[(0,[z0,z2,z3,z4,z347,z5]),(0,[z0,z2,z3,z4,z1204,z6]),(0,[z0,z2,z3,z1205,z4,z10])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 525) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 525).take 532) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1057).take 172) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1229)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [525, 532, 172] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 112).take 123).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 235).take 21).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [112, 123, 21] = true :=
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

end PEqualNP.Outside.L_meta_38905

theorem PEqualNP.Outside.L_meta_38905 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209682944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4209682944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38905.solve
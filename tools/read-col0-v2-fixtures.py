"""Original team inputs. Each suffix makes a distinct synthetic file."""

def proof(category, suffix=0):
    n = 'quartzVioletLarkₐ'
    head = f'def amber{suffix} ({n} : Nat) : '
    tail = f'theorem plum{suffix} : 0 = 0 := by\n  exact\nrfl\n'
    anchor = f'theorem ochre{suffix} : True := True.intro\n'
    # Subtraction keeps a real COL0 hold on main. A plus at the end of
    # the preceding line would let the existing continuation rule clear it.
    operand = head + 'Nat := (1 -\n' + n + '\n  )\n'
    other = head + 'Nat := (Nat.succ\n' + n + '\n  )\n'
    if category == 0:
        # The quoted literal also produces an independent baseline WORD hold.
        source = head + 'Prod String Nat := ("opal-cabinet-73951", (1 -\n' + n + '\n  ))\n' + anchor
    elif category == 1:
        source = other + anchor
    elif category == 2:
        source = tail
    elif category == 3:
        source = operand + tail
    elif category == 4:
        source = operand + '/-- A team documentation comment. -/\n' + anchor
    elif category == 5:
        # Five distinct shapes, all GROUP_OPERAND. Class equality cannot mask overflow.
        terms = ['(1 -\nN\n  )', '((1 -\nN\n  ))', '(((1 -\nN\n  )))',
                 '(1 -\nN + 0\n  )', '(1 -\nN - 0 - 0\n  )']
        source = ''.join(f'def russet{suffix}_{i} ({n} : Nat) : Nat := '
                         + term.replace('N', n) + '\n' for i, term in enumerate(terms)) + anchor
    else:
        raise ValueError
    return source.encode()

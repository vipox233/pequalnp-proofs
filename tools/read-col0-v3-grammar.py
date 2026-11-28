"""Frozen rd-2 grammar. All offsets are in the original bytes, including CRLF.

The file production is fully anchored. The expression reader only records a line
after consuming its first atom in a subtraction operand position and matching
both ends of an enclosing proof-term group. No Lean code or imports are run.
"""
import bisect
import re


class Refused(ValueError):
    pass


# A finite identifier alphabet avoids interpreting arbitrary extension keywords
# as terms. Match an entire token so adjacent unknown bytes cannot disappear.
LOCAL = rb'n(?:[0-9]{1,4}|' + 'ₐ'.encode() + rb')?'
IDENT = rb'(?:[a-zA-Z_0-9.]|[^\x00-\x7f])+'
TOKEN = re.compile(rb'--[^\r\n]*|/--|/-!|/-|:=|[():=-]|' + IDENT)
TRIVIA = re.compile(rb'(?: +|\r?\n)+')
NUMBER = re.compile(rb'(?:0|[1-9][0-9]{0,19})')
IMPORT = re.compile(rb'import (?:Mathlib|PEqualNP\.Defs) *(?:\r?\n)')


class Reader:
    def __init__(self, raw, held):
        self.raw = raw
        self.lines = [0] + [m.end() for m in re.finditer(b'\n', raw)]
        self.held = held
        self.operands = set()
        self.pos = 0
        self.local = None
        self.advance()

    def advance(self):
        while self.pos < len(self.raw):
            space = TRIVIA.match(self.raw, self.pos)
            if space:
                self.pos = space.end()
                continue
            token = TOKEN.match(self.raw, self.pos)
            if not token:
                raise Refused
            self.start, self.pos = token.span()
            self.token = token.group()
            if not self.token.startswith(b'--'):
                return
            # Only a standalone ordinary line comment is trivia. Block and doc
            # openers are distinct tokens with no accepting production.
            start = self.raw.rfind(b'\n', 0, self.start) + 1
            if self.raw[start:self.start].strip(b' '):
                raise Refused
        self.start = self.pos
        self.token = None

    def take(self, token):
        if self.token != token:
            raise Refused
        self.advance()

    def expression(self, depth=0, in_proof=False):
        rhs = False
        while True:
            if self.token == b'(':
                self.group(depth + 1, in_proof)
            elif self.token == self.local or NUMBER.fullmatch(self.token or b''):
                if rhs and in_proof and self.token == self.local:
                    line = bisect.bisect_right(self.lines, self.start)
                    if line in self.held and self.start == self.lines[line - 1]:
                        self.operands.add(line)
                self.advance()
            else:
                raise Refused
            if self.token != b'-':
                return
            # Only binary, whitespace-separated subtraction is in the grammar.
            before = self.raw[self.start - 1:self.start]
            after = self.raw[self.pos:self.pos + 1]
            if before not in (b' ', b'\n') or after not in (b' ', b'\r', b'\n'):
                raise Refused
            self.advance()
            rhs = True

    def group(self, depth, in_proof):
        if depth > 64:
            raise Refused
        opening = self.start
        self.take(b'(')
        self.expression(depth, in_proof)
        closing = self.start
        self.take(b')')
        return opening, closing

    def line_inside(self, n, opening, closing):
        # The half-open byte range includes trailing spaces and excludes EOL.
        start = self.lines[n - 1]
        end = self.lines[n] - 1 if n < len(self.lines) else len(self.raw)
        if self.raw[end - 1:end] == b'\r':
            end -= 1
        return opening < start and end <= closing

    def file(self, name):
        while self.token == b'import':
            header = IMPORT.match(self.raw, self.start)
            if not header or self.start != self.raw.rfind(b'\n', 0, self.start) + 1:
                raise Refused
            self.pos = header.end()
            self.advance()
        self.take(b'theorem')
        self.take(name)
        self.take(b'(')
        if not re.fullmatch(LOCAL, self.token or b''):
            raise Refused
        self.local = self.token
        self.advance()
        self.take(b':')
        self.take(b'Nat')
        self.take(b')')
        self.take(b':')
        self.expression()
        self.take(b'=')
        self.expression()
        self.take(b':=')
        function_end = self.pos
        self.take(b'Eq.refl')
        # Lean application is whitespace and layout sensitive. Freeze the
        # same-line form so an opening parenthesis cannot start another command.
        if not re.fullmatch(b' +', self.raw[function_end:self.start]):
            raise Refused
        opening, closing = self.group(1, True)
        return (self.token is None and self.pos == len(self.raw)
                and self.operands == self.held
                and all(self.line_inside(n, opening, closing) for n in self.held))


def covers(raw, name, held):
    if not held or len(raw) > 512 * 1024:
        return False
    try:
        return Reader(raw, held).file(name)
    except Refused:
        return False

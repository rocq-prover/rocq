from dataclasses import asdict, dataclass
from typing import TypeVar

from .parsing import parse
from .TacticNotationsParser import TacticNotationsParser
from .TacticNotationsVisitor import TacticNotationsVisitor


class NotationObject:
    def asdict(self):
        return asdict(self)

TaggedNotationObject = tuple[str, NotationObject]

SelfLiteral = TypeVar("Self", bound="Literal")
@dataclass
class Literal(NotationObject):
    value: str
    subscript: str | None
    @classmethod
    def new(cls, value: SelfLiteral) -> tuple[str, SelfLiteral]:
        return ("Literal", value)

SelfReference = TypeVar("Self", bound="Reference")
@dataclass
class Reference(NotationObject):
    value: str
    subscript: str | None
    @classmethod
    def new(cls, value: SelfReference) -> tuple[str, SelfReference]:
        return ("Reference", value)

SelfAlternative = TypeVar("Self", bound="Alternative")
@dataclass
class Alternative(NotationObject):
    children: list[TaggedNotationObject]
    @classmethod
    def new(cls, value: SelfAlternative) -> tuple[str, SelfAlternative]:
        return ("Alternative", value)

SelfRepeat = TypeVar("Self", bound="Repeat")
@dataclass
class Repeat(NotationObject):
    min: int
    max: int | None
    separator: str | None
    children: list[TaggedNotationObject]
    @classmethod
    def new(cls, value: SelfRepeat) -> tuple[str, SelfRepeat]:
        return ("Repeat", value)

class TacticNotationsToObjectVisitor(TacticNotationsVisitor):
    def defaultResult(self):
        return []

    def aggregateResult(self, aggregate, nextResult):
        # Flattening results into a single list of nodes
        if nextResult:
            if isinstance(nextResult, list):
                aggregate.extend(nextResult)
            else:
                aggregate.append(nextResult)
        return aggregate

    def visitAlternative(self, ctx: TacticNotationsParser.AlternativeContext):
        return [Alternative.new(Alternative(children=self.visitChildren(ctx)))]

    def visitAltblock(self, ctx: TacticNotationsParser.AltblockContext):
        return self.visitChildren(ctx)

    def visitRepeat(self, ctx: TacticNotationsParser.RepeatContext):
        separator = ctx.ATOM() or ctx.PIPE()
        # skip the '{'
        repeat_marker = ctx.LGROUP().getText()[1]

        min_rep, max_rep = None, None
        match repeat_marker:
            case "?":
                min_rep, max_rep = 0, 1
            case "+":
                min_rep, max_rep = 1, None
            case "*":
                min_rep, max_rep = 0, None
            case _:
                raise ValueError(f"Unexpected repeat marker: {repeat_marker}")

        return [Repeat.new(Repeat(
            min=min_rep,
            max=max_rep,
            separator=separator.getText() if separator else None,
            children=self.visitChildren(ctx)
        ))]

    def visitCurlies(self, ctx: TacticNotationsParser.CurliesContext):
        return [
            Literal.new(Literal(value=ctx.LBRACE().getText(), subscript=None)),
            *self.visitChildren(ctx),
            Literal.new(Literal(value=ctx.RBRACE().getText(), subscript=None))]

    def visitAtomic(self, ctx: TacticNotationsParser.AtomicContext):
        return [Literal.new(Literal(
            value=ctx.ATOM().getText(),
            # skip '__'
            subscript=ctx.SUB().getText()[2:] if ctx.SUB() else None
        ))]

    def visitHole(self, ctx: TacticNotationsParser.HoleContext):
        return [Reference.new(Reference(
            value=ctx.ID().getText()[1:],
            # skip '__'
            subscript=ctx.SUB().getText()[2:] if ctx.SUB() else None
        ))]

    def visitEscaped(self, ctx: TacticNotationsParser.EscapedContext):
        return [Literal.new(Literal(
            value=ctx.ESCAPED().getText().replace("%", ""),
            subscript=None
        ))]

def objectify(notation: str) -> list[TaggedNotationObject]:
    """Translate a notation into an object.

    It is essentially a simplified and normalized version of the ANTLR AST.
    """
    visitor = TacticNotationsToObjectVisitor()
    return visitor.visit(parse(notation))

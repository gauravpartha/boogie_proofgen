﻿using NUnit.Framework;
using System;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace CoreTests
{
  [TestFixture()]
  public class ExprImmutability : IErrorSink
  {
    public void Error(IToken tok, string msg)
    {
      Assert.Fail(msg);
    }

    // Cached hashcode checkers
    [Test()]
    public void CachedHashCodeLiteralExpr()
    {
      var literal = new LiteralExpr(Token.NoToken, true, /*immutable=*/true);
      Assert.AreEqual(literal.ComputeHashCode(), literal.GetHashCode());

      var literal2 = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(0), /*immutable=*/true);
      Assert.AreEqual(literal2.ComputeHashCode(), literal2.GetHashCode());

      var literal3 = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigDec.FromInt(0), /*immutable=*/true);
      Assert.AreEqual(literal3.ComputeHashCode(), literal3.GetHashCode());

      var literal4 = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(0), 8, /*immutable=*/true);
      Assert.AreEqual(literal4.ComputeHashCode(), literal4.GetHashCode());

      var literal5 = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigFloat.FromInt(0), /*immutable=*/true);
      Assert.AreEqual(literal5.ComputeHashCode(), literal5.GetHashCode());

      var literal6 = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.RoundingMode.RNE, /*immutable=*/true);
      Assert.AreEqual(literal6.ComputeHashCode(), literal6.GetHashCode());
    }

    [Test()]
    public void CachedHashCodeIdentifierExpr()
    {
      var id = new IdentifierExpr(Token.NoToken, "foo", BasicType.Bool, /*immutable=*/true);
      Assert.AreEqual(id.ComputeHashCode(), id.GetHashCode());

      var variable = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "foo2", BasicType.Int));
      var id2 = new IdentifierExpr(Token.NoToken, variable, /*immutable=*/true);
      Assert.AreEqual(id2.ComputeHashCode(), id2.GetHashCode());
    }

    [Test()]
    public void CachedHashCodeNAryExpr()
    {
      var nary = new NAryExpr(Token.NoToken, new UnaryOperator(Token.NoToken, UnaryOperator.Opcode.Not),
        new List<Expr>() {Expr.True}, /*immutable=*/true);
      Assert.AreEqual(nary.ComputeHashCode(), nary.GetHashCode());
    }

    [Test()]
    public void CachedHashCodeBvExtractExpr()
    {
      var literalBv = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(0), 4, /*immutable=*/true);
      var bvExtract = new BvExtractExpr(Token.NoToken, literalBv, 3, 0, /*immutable=*/true);
      Assert.AreEqual(bvExtract.ComputeHashCode(), bvExtract.GetHashCode());
    }

    [Test()]
    public void CachedHashCodeBvConcatExpr()
    {
      var literalBv = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(0), 4, /*immutable=*/true);
      var bvConcat = new BvConcatExpr(Token.NoToken, literalBv, literalBv, /*immutable=*/true);
      Assert.AreEqual(bvConcat.ComputeHashCode(), bvConcat.GetHashCode());
    }

    [Test()]
    public void CachedHashCodeOldExpr()
    {
      var literalBv = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(0), 4, /*immutable=*/true);
      var oldExpr = new OldExpr(Token.NoToken, literalBv, /*immutable=*/true);
      Assert.AreEqual(oldExpr.ComputeHashCode(), oldExpr.GetHashCode());
    }

    [Test()]
    public void CachedHashCodeForAllExpr()
    {
      var x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var y = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var body = Expr.Gt(new IdentifierExpr(Token.NoToken, x, /*immutable=*/true),
        new IdentifierExpr(Token.NoToken, y, /*immutable=*/true));
      var forAll = new ForallExpr(Token.NoToken, new List<Variable>() {x, y}, body, /*immutable=*/ true);
      Assert.AreEqual(forAll.ComputeHashCode(), forAll.GetHashCode());
    }

    [Test()]
    public void CachedHashCodeExistsExpr()
    {
      var x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var y = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var body = Expr.Gt(new IdentifierExpr(Token.NoToken, x, /*immutable=*/true),
        new IdentifierExpr(Token.NoToken, y, /*immutable=*/true));
      var exists = new ExistsExpr(Token.NoToken, new List<Variable>() {x, y}, body, /*immutable=*/ true);
      Assert.AreEqual(exists.ComputeHashCode(), exists.GetHashCode());
    }

    [Test()]
    public void CachedHashCodeLambdaExpr()
    {
      var x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var y = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var body = Expr.Gt(new IdentifierExpr(Token.NoToken, x, /*immutable=*/true),
        new IdentifierExpr(Token.NoToken, y, /*immutable=*/true));
      var lambda = new LambdaExpr(Token.NoToken, new List<TypeVariable>(), new List<Variable>() {x, y},
        null, body, /*immutable=*/true);
      Assert.AreEqual(lambda.ComputeHashCode(), lambda.GetHashCode());
    }

    // Runtime immutability enforcement

    [Test()]
    public void IdentifierExprName()
    {
      var id = new IdentifierExpr(Token.NoToken, "foo", BasicType.Bool, /*immutable=*/true);
      Assert.IsTrue(id.Immutable);
      Assert.Throws(typeof(InvalidOperationException), () => id.Name = "foo2");
    }

    [Test()]
    public void IdentifierExprDecl()
    {
      var id = new IdentifierExpr(Token.NoToken, "foo", BasicType.Bool, /*immutable=*/true);
      Assert.IsTrue(id.Immutable);
      var typedIdent = new TypedIdent(Token.NoToken, "foo2", BasicType.Bool);
      Assert.Throws(typeof(InvalidOperationException), () => id.Decl = new GlobalVariable(Token.NoToken, typedIdent));
    }

    private NAryExpr GetUnTypedImmutableNAry()
    {
      var id = new IdentifierExpr(Token.NoToken, "foo", BasicType.Bool, /*immutable=*/true);
      Assert.IsTrue(id.Immutable);
      Assert.IsTrue(id.Type.IsBool);
      var e = new NAryExpr(Token.NoToken, new BinaryOperator(Token.NoToken, BinaryOperator.Opcode.And), new List<Expr>()
      {
        id,
        id
      }, /*immutable=*/true);
      Assert.IsNull(e.Type);
      Assert.IsTrue(e.Immutable);
      return e;
    }

    [Test()]
    public void ProtectedExprType()
    {
      var e = GetUnTypedImmutableNAry();

      // Now Typecheck
      // Even though it's immutable we allow the TypeCheck field to be set if the Expr has never been type checked
      var TC = new TypecheckingContext(this);
      e.Typecheck(TC);
      Assert.IsNotNull(e.Type);
      Assert.IsTrue(e.Type.IsBool);
    }

    [Test()]
    public void ProtectedExprChangeTypeFail()
    {
      var e = GetUnTypedImmutableNAry();

      // Now Typecheck
      // Even though it's immutable we allow the TypeCheck field to be set if the Expr has never been type checked
      var TC = new TypecheckingContext(this);
      e.Typecheck(TC);
      Assert.IsNotNull(e.Type);
      Assert.IsTrue(e.Type.IsBool);

      // Trying to modify the Type to a different Type now should fail
      Assert.Throws(typeof(InvalidOperationException), () => e.Type = BasicType.Int);
    }

    [Test()]
    public void ProtectedExprTypeChangeTypeSucceed()
    {
      var e = GetUnTypedImmutableNAry();

      // Now Typecheck
      // Even though it's immutable we allow the TypeCheck field to be set if the Expr has never been type checked
      var TC = new TypecheckingContext(this);
      e.Typecheck(TC);
      Assert.IsNotNull(e.Type);
      Assert.IsTrue(e.Type.IsBool);

      // Trying to assign the same Type should succeed
      e.Type = BasicType.Bool;
    }

    [Test()]
    public void ProtectedOldExpr()
    {
      var e = new OldExpr(Token.NoToken, Expr.True, /*immutable=*/ true);
      Assert.Throws(typeof(InvalidOperationException), () => e.Expr = Expr.False);
    }

    [Test()]
    public void ProtectedNAryFunc()
    {
      var e = GetUnTypedImmutableNAry();
      Assert.Throws(typeof(InvalidOperationException),
        () => e.Fun = new BinaryOperator(Token.NoToken, BinaryOperator.Opcode.Sub));
    }

    [Test()]
    public void ProtectedNAryArgsList()
    {
      var e = GetUnTypedImmutableNAry();
      Assert.Throws(typeof(NotSupportedException), () => e.Args.Add(null));
    }

    [Test()]
    public void ProtectedNAryArgs()
    {
      var e = GetUnTypedImmutableNAry();
      Assert.Throws(typeof(InvalidOperationException), () => e.Args = new List<Expr>());
    }

    [Test()]
    public void ProtectedForAllExprBody()
    {
      var x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var y = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var xId = new IdentifierExpr(Token.NoToken, x, /*immutable=*/true);
      var yId = new IdentifierExpr(Token.NoToken, y, /*immutable=*/true);
      var body = Expr.Gt(xId, yId);
      var forAll = new ForallExpr(Token.NoToken, new List<Variable>() {x, y}, body, /*immutable=*/true);
      // Changing the body of an immutable ForAllExpr should fail
      Assert.Throws(typeof(InvalidOperationException), () => forAll.Body = Expr.Lt(xId, yId));
    }

    [Test()]
    public void ProtectedExistsExprBody()
    {
      var x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var y = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var xId = new IdentifierExpr(Token.NoToken, x, /*immutable=*/true);
      var yId = new IdentifierExpr(Token.NoToken, y, /*immutable=*/true);
      var body = Expr.Gt(xId, yId);
      var exists = new ExistsExpr(Token.NoToken, new List<Variable>() {x, y}, body, /*immutable=*/true);
      // Changing the body of an immutable ExistsExpr should fail
      Assert.Throws(typeof(InvalidOperationException), () => exists.Body = Expr.Lt(xId, yId));
    }

    [Test()]
    public void ProtectedLambdaExprBody()
    {
      var x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var y = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", BasicType.Int));
      var xId = new IdentifierExpr(Token.NoToken, x, /*immutable=*/true);
      var yId = new IdentifierExpr(Token.NoToken, y, /*immutable=*/true);
      var body = Expr.Gt(xId, yId);
      var lambda = new LambdaExpr(Token.NoToken, new List<TypeVariable>(), new List<Variable>() {x, y},
        null, body, /*immutable=*/true);
      // Changing the body of an immutable LambdaExpr should fail
      Assert.Throws(typeof(InvalidOperationException), () => lambda.Body = Expr.Lt(xId, yId));
    }

    [Test()]
    public void ProtectedBvConcatExprLhs()
    {
      var lhs = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(0), 32, /*immutable=*/true);
      var rhs = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(1), 32, /*immutable=*/true);
      var concat = new BvConcatExpr(Token.NoToken, lhs, rhs, /* immutable=*/true);
      Assert.IsTrue(concat.Immutable);
      Assert.Throws(typeof(InvalidOperationException), () => concat.E0 = rhs);
    }

    [Test()]
    public void ProtectedBvConcatExprRhs()
    {
      var lhs = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(0), 32, /*immutable=*/true);
      var rhs = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(1), 32, /*immutable=*/true);
      var concat = new BvConcatExpr(Token.NoToken, lhs, rhs, /* immutable=*/true);
      Assert.IsTrue(concat.Immutable);
      Assert.Throws(typeof(InvalidOperationException), () => concat.E1 = lhs);
    }

    [Test()]
    public void ProtectedBvExtract()
    {
      var bv = new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(0), 32, /*immutable=*/true);
      var extract = new BvExtractExpr(Token.NoToken, bv, 32, 0, /*immutable=*/true);
      Assert.IsTrue(extract.Immutable);
      Assert.Throws(typeof(InvalidOperationException), () => extract.Bitvector = bv);
    }
  }
}
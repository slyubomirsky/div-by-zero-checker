package org.checkerframework.checker.dividebyzero;

import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.source.Result;

import javax.lang.model.type.TypeKind;
import java.lang.annotation.Annotation;
import com.sun.source.tree.*;

import java.util.Set;
import java.util.EnumSet;

import org.checkerframework.checker.dividebyzero.qual.*;

public class DivByZeroVisitor extends BaseTypeVisitor<DivByZeroAnnotatedTypeFactory> {

    /** Set of operators we care about */
    private static final Set<Tree.Kind> DIVISION_OPERATORS = EnumSet.of(
        /* x /  y */ Tree.Kind.DIVIDE,
        /* x /= y */ Tree.Kind.DIVIDE_ASSIGNMENT,
        /* x %  y */ Tree.Kind.REMAINDER,
        /* x %= y */ Tree.Kind.REMAINDER_ASSIGNMENT);

    /**
     * Determine whether to report an error at the given binary AST node.
     * The error text is defined in the messages.properties file.
     * @param node the AST node to inspect
     * @return true if an error should be reported, false otherwise
     */
    private boolean errorAt(BinaryTree node) {
        // A BinaryTree represents a binary operator, like + or -.

        // no error if we're not considering a division
        Tree.Kind operator = node.getKind();
        if (!DIVISION_OPERATORS.contains(operator)) {
            return false;
        }

        // we are only considering integers so only consider if both operands are ints
        // (after all, if at least one operand is a float, the expression is promoted to one on floats)
        ExpressionTree divisor = node.getRightOperand();
        if (!isInt(node.getLeftOperand()) || !isInt(divisor)) {
            return false;
        }

        // We only get a divide by zero error if the right operand (divisor) is zero or potentially zero.
        // All relevant annotations: Zero, GreaterThanOrEqualToZero, LessThanOrEqualToZero, AllZ, Top
        // Note: Division by an undefined value is a different sort of error, so that's why we don't catch that case here
        return (hasAnnotation(divisor, Top.class) 
            || hasAnnotation(divisor, AllZ.class) 
            || hasAnnotation(divisor, GreaterThanOrEqualToZero.class)
            || hasAnnotation(divisor, LessThanOrEqualToZero.class)
            || hasAnnotation(divisor, Zero.class));
    }

    /**
     * Determine whether to report an error at the given compound assignment
     * AST node. The error text is defined in the messages.properties file.
     * @param node the AST node to inspect
     * @return true if an error should be reported, false otherwise
     */
    private boolean errorAt(CompoundAssignmentTree node) {
        // no error if we're not considering a division
        Tree.Kind operator = node.getKind();
        if (!DIVISION_OPERATORS.contains(operator)) {
            return false;
        }

        // we are only considering integers so only consider if both operands are ints
        // (after all, if at least one operand is a float, the expression is promoted to one on floats)
        ExpressionTree divisor = node.getExpression();
        if (!isInt(node.getVariable()) || !isInt(divisor)) {
            return false;
        }

        // We only get a divide by zero error if the divisor is zero or potentially zero.
        // All relevant annotations: Zero, GreaterThanOrEqualToZero, LessThanOrEqualToZero, AllZ, Top
        // Note: Division by an undefined value is a different sort of error, so that's why we don't catch that case here
        return (hasAnnotation(divisor, Top.class) 
            || hasAnnotation(divisor, AllZ.class) 
            || hasAnnotation(divisor, GreaterThanOrEqualToZero.class)
            || hasAnnotation(divisor, LessThanOrEqualToZero.class)
            || hasAnnotation(divisor, Zero.class));
    }

    // ========================================================================
    // Useful helpers

    private static final Set<TypeKind> INT_TYPES = EnumSet.of(
        TypeKind.INT,
        TypeKind.LONG);

    private boolean isInt(Tree node) {
        return INT_TYPES.contains(atypeFactory.getAnnotatedType(node).getKind());
    }

    private boolean hasAnnotation(Tree node, Class<? extends Annotation> c) {
        return atypeFactory.getAnnotatedType(node).hasAnnotation(c);
    }

    // ========================================================================
    // Checker Framework plumbing

    public DivByZeroVisitor(BaseTypeChecker c) {
        super(c);
    }

    @Override
    public Void visitBinary(BinaryTree node, Void p) {
        if (isInt(node)) {
            if (errorAt(node)) {
                checker.report(Result.failure("divide.by.zero"), node);
            }
        }
        return super.visitBinary(node, p);
    }

    @Override
    public Void visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
        if (isInt(node.getExpression())) {
            if (errorAt(node)) {
                checker.report(Result.failure("divide.by.zero"), node);
            }
        }
        return super.visitCompoundAssignment(node, p);
    }

}

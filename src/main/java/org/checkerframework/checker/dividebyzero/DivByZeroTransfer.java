package org.checkerframework.checker.dividebyzero;

import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFAnalysis;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.ConditionalTransferResult;
import org.checkerframework.dataflow.analysis.FlowExpressions;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;

import javax.lang.model.element.AnnotationMirror;
import java.lang.annotation.Annotation;

import java.util.Set;

import org.checkerframework.checker.dividebyzero.qual.*;

public class DivByZeroTransfer extends CFTransfer {

    enum Comparison {
        /** == */ EQ,
        /** != */ NE,
        /** <  */ LT,
        /** <= */ LE,
        /** >  */ GT,
        /** >= */ GE
    }

    enum BinaryOperator {
        /** + */ PLUS,
        /** - */ MINUS,
        /** * */ TIMES,
        /** / */ DIVIDE,
        /** % */ MOD
    }

    // ========================================================================
    // Transfer functions to implement

    /**
     * Assuming that a simple comparison (lhs `op` rhs) returns true, this
     * function should refine what we know about the left-hand side (lhs). (The
     * input value "lhs" is always a legal return value, but not a very useful
     * one.)
     *
     * <p>For example, given the code
     * <pre>
     * if (y != 0) { x = 1 / y; }
     * </pre>
     * the comparison "y != 0" causes us to learn the fact that "y is not zero"
     * inside the body of the if-statement. This function would be called with
     * "NE", "top", and "zero", and should return "not zero" (or the appropriate
     * result for your lattice).
     *
     * <p>Note that the returned value should always be lower in the lattice
     * than the given point for lhs. The "glb" helper function below will
     * probably be useful here.
     *
     * @param operator   a comparison operator
     * @param lhs        the lattice point for the left-hand side of the comparison expression
     * @param rhs        the lattice point for the right-hand side of the comparison expression
     * @return a refined type for lhs
     */
    private AnnotationMirror refineLhsOfComparison(
            Comparison operator,
            AnnotationMirror lhs,
            AnnotationMirror rhs) {
        AnnotationMirror zero = reflect(Zero.class);
        AnnotationMirror top = reflect(Top.class);
        AnnotationMirror udv = reflect(UndefinedValue.class);
        AnnotationMirror neg = reflect(StrictlyNegative.class);
        AnnotationMirror pos = reflect(StrictlyPositive.class);
        AnnotationMirror gez = reflect(GreaterThanOrEqualToZero.class);
        AnnotationMirror lez = reflect(LessThanOrEqualToZero.class);
        AnnotationMirror nonZero = reflect(NonZero.class);
        AnnotationMirror allZ = reflect(AllZ.class);

        // to avoid any weirdness, bottom cannot possibly be refined, so eliminate it now
        if (equal(lhs, bottom())) {
            return bottom();
        }
        // should be impossible too
        if (equal(rhs, bottom())) {
            return lhs;
        }

        switch(operator) {
        case EQ:
            // * denotes impossible, never will be true
            // a = b | 0 | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
            //   0   | 0 | 0* | 0* |  0  |  0* |  0  | 0 | 0* | 0
            //   -   | 0*| -  | -* |  -  |  -  |  -* | - | -* | -
            //   +   | 0*| +* | +  |  +* |  +  |  +  | + | +* | +
            //  <=0  | 0 | -  |<=0*| <=0 |  -  |  0  |<=0|<=0*|<=0
            //  !=0  | 0*| -  | +  |  -  | !=0 |  +  |!=0|!=0*|!=0
            //  >=0  | 0 |>=0*| +  |  0  |  +  | >=0 |>=0|>=0*|>=0
            //   Z   | 0 | -  | +  | <=0 | !=0 | >=0 | Z | Z* | Z
            //   UD  | 0*| -* | +* | <=0*| !=0*| >=0*| Z*| UD | UD
            //  top  | 0 | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
            // If we consider the impossible cases to be bot, then these are all the GLB
            return glb(lhs, rhs);
        case NE:
            // (only impossible case is 0 != 0)
            // a != b | 0 | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
            //   0    | 0*| 0  | 0  |  0  |  0  |  0  | 0 | 0  | 0
            //   -    | - | -  | -  |  -  |  -  |  -  | - | -  | -
            //   +    | + | +  | +  |  +  |  +  |  +  | + | +  | +
            //  <=0   | - |<=0 |<=0 | <=0 | <=0 | <=0 |<=0|<=0 |<=0
            //  !=0   |!=0|!=0 |!=0 | !=0 | !=0 | !=0 |!=0|!=0 |!=0
            //  >=0   | + |>=0 |>=0 | >=0 | >=0 | >=0 |>=0|>=0 |>=0
            //   Z    |!=0| Z  | Z  |  Z  |  Z  |  Z  | Z | Z  | Z
            //   UD   |UD |UD  | UD |  UD |  UD |  UD | UD| UD | UD
            //  top   |!=0|top |top | top | top | top |top| Z  | top
            //
            // Reasoning: The only case that gives us more information is != 0,
            // since != being true or false for a *specific* value adds no information
            // unless we know that specific value is zero.
            // For example, let's consider <=0 != <=0: Suppose the LHS is 0 and the RHS is -4. 
            // These are valid members of the equivalence classes yet the LHS is 0, so we cannot draw any conclusion
            // from the RHS potentially being 0 (it may not be 0).
            // We consider top to be potentially undefined so not being equal to a specific int does not disqualify that
            AnnotationMirror[][] neTable = {
            //                  0    |    -    |    +    |   <=0   |   !=0   |   >=0   |   Z    |   UD    |   top   
            /*    0    */  { bottom(),   zero  ,   zero  ,  zero   ,  zero   ,  zero   ,  zero  ,  zero   ,  zero   },
            /*    -    */  {  neg    ,   neg   ,   neg   ,  neg    ,  neg    ,  neg    ,  neg   ,  neg    ,  neg    },
            /*    +    */  {  pos    ,   pos   ,   pos   ,  pos    ,  pos    ,  pos    ,  pos   ,  pos    ,  pos    },
            /*   <=0   */  {  neg    ,   lez   ,   lez   ,  lez    ,  lez    ,  lez    ,  lez   ,  lez    ,  lez    },
            /*   !=0   */  { nonZero , nonZero , nonZero , nonZero , nonZero , nonZero , nonZero, nonZero , nonZero },
            /*   >=0   */  {  pos    ,   gez   ,   gez   ,  gez    ,  gez    ,  gez    ,  gez   ,  gez    ,  gez    },
            /*    Z    */  { nonZero ,  allZ   ,  allZ   , allZ    ,  allZ   ,  allZ   ,  allZ  ,  allZ   ,  allZ   },
            /*    UD   */  {  udv    ,   udv   ,   udv   ,  udv    ,  udv    ,  udv    ,  udv   ,  udv    ,  udv    },
            /*   top   */  { nonZero ,   top   ,   top   ,  top    ,  top    ,  top    ,  top   ,  allZ   ,  top    }
            };
            return matchTable(neTable, lhs, rhs);
        case LT:
            // * denotes impossible, never will be true
            // a < b | 0  | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
            //   0   | 0* | 0* | 0  |  0* |  0  |  0  | 0 | 0* | 0
            //   -   | -  | -  | -  |  -  |  -  |  -  | - | -* | -
            //   +   | +* | +* | +  |  +* |  +  |  +  | + | +* | +
            //  <=0  | -  | -  |<=0 |  -  | <=0 | <=0 |<=0|<=0*|<=0
            //  !=0  | -  | -  |!=0 |  -  | !=0 | !=0 |!=0|!=0*|!=0
            //  >=0  |>=0*|>=0*|>=0 | >=0*| >=0 | >=0 |>=0|>=0*|>=0
            //   Z   | -  | -  | Z  |  -  |  Z  |  Z  | Z | Z* | Z
            //   UD  |UD  |UD  |UD  |  UD | UD  | UD  |UD | UD | UD
            //  top  | -  | -  | Z  |  -  |  Z  |  Z  | Z | UD | Z
            // Notes: This is an exclusive bound, so if the RHS is <=0, the LHS
            // cannot possibly be 0. Note that we can draw no new conclusions if the RHS
            // is +, !=0, or >=0, since a value less than any *specific member* of those groups
            // can still be positive, negative, or 0.

            AnnotationMirror[][] ltTable = {
            //                  0    |    -    |    +    |   <=0   |   !=0   |   >=0   |   Z    |   UD    |   top   
            /*    0    */  { bottom(), bottom(),   zero  , bottom(),  zero   ,  zero   ,  zero  , bottom(),  zero   },
            /*    -    */  {  neg    ,   neg   ,   neg   ,  neg    ,  neg    ,  neg    ,  neg   , bottom(),  neg    },
            /*    +    */  { bottom(), bottom(),   pos   , bottom(),  pos    ,  pos    ,  pos   , bottom(),  pos    },
            /*   <=0   */  {  neg    ,  neg    ,   lez   ,  neg    ,  lez    ,  lez    ,  lez   , bottom(),  lez    },
            /*   !=0   */  {  neg    ,  neg    , nonZero ,  neg    , nonZero , nonZero , nonZero, bottom(), nonZero },
            /*   >=0   */  { bottom(), bottom(),   gez   , bottom(),  gez    ,  gez    ,  gez   , bottom(),  gez    },
            /*    Z    */  {  neg    ,  neg    ,  allZ   ,  neg    ,  allZ   ,  allZ   ,  allZ  , bottom(),  allZ   },
            /*    UD   */  {  udv    ,  udv    ,  udv    ,  udv    ,  udv    ,  udv    ,  udv   ,  udv    ,   udv   },
            /*   top   */  {  neg    ,  neg    ,  allZ   ,  neg    ,  allZ   ,  allZ   ,  allZ  ,  udv    ,  allZ   }
            };
            return matchTable(ltTable, lhs, rhs);
        case LE:
            // * denotes impossible, never will be true
            // a <= b | 0 | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
            //   0    | 0 | 0  | 0  |  0  |  0  |  0  | 0 | 0* | 0
            //   -    | - | -  | -  |  -  |  -  |  -  | - | -* | -
            //   +    | +*| +* | +  |  +* |  +  |  +  | + | +* | +
            //  <=0   |<=0| -  |<=0 | <=0 | <=0 | <=0 |<=0|<=0*|<=0
            //  !=0   | - | -  |!=0 |  -  | !=0 | !=0 |!=0|!=0*|!=0
            //  >=0   | 0 |>=0*|>=0 |  0  | >=0 | >=0 |>=0|>=0*|>=0
            //   Z    |<=0| -  | Z  | <=0 |  Z  |  Z  | Z | Z* | Z
            //   UD   |UD*|UD* | UD*|  UD*|  UD*|  UD*|UD*| UD*| UD*
            //  top   |<=0| -  | Z  | <=0 |  Z  |  Z  | Z | Z* | Z
            // Reasoning: The inclusive bound changes some things.
            // Interesting cases: 
            // * >=0 <= 0: The only way for this to be true is if the LHS *is* 0.
            // * >=0 <= <=0: The only for this to be true is if the LHS and RHS are both 0.
            // * !=0 <= <=0: The LHS is already nonzero so it must be negative (similarly !=0 <= 0)
            // Otherwise, if the RHS is <=0 or 0, generally consider the result <=0 and if the RHS is -,
            //   consider the result -. Can't draw any new conclusions for the other cases
            AnnotationMirror[][] leTable = {
            //                  0    |    -    |    +    |   <=0   |   !=0   |   >=0   |   Z    |   UD    |   top   
            /*    0    */  {  zero   ,   zero  ,   zero  ,   zero  ,  zero   ,  zero   ,  zero  , bottom(),  zero   },
            /*    -    */  {  neg    ,   neg   ,   neg   ,  neg    ,  neg    ,  neg    ,  neg   , bottom(),  neg    },
            /*    +    */  { bottom(), bottom(),   pos   , bottom(),  pos    ,  pos    ,  pos   , bottom(),  pos    },
            /*   <=0   */  {  lez    ,  neg    ,   lez   ,  lez    ,  lez    ,  lez    ,  lez   , bottom(),  lez    },
            /*   !=0   */  {  neg    ,  neg    , nonZero ,  neg    , nonZero , nonZero , nonZero, bottom(), nonZero },
            /*   >=0   */  {  zero   , bottom(),   gez   ,  zero   ,  gez    ,  gez    ,  gez   , bottom(),  gez    },
            /*    Z    */  {  lez    ,  neg    ,  allZ   ,  lez    ,  allZ   ,  allZ   ,  allZ  , bottom(),  allZ   },
            /*    UD   */  {  udv    ,  udv    ,  udv    ,  udv    ,  udv    ,  udv    ,  udv   ,  udv    ,   udv   },
            /*   top   */  {  lez    ,  neg    ,  allZ   ,  lez    ,  allZ   ,  allZ   ,  allZ  ,  udv    ,  allZ   }
            };
            return matchTable(leTable, lhs, rhs);
        case GT:
            // * denotes impossible, never will be true
            // a > b | 0  | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
            //   0   | 0* | 0  | 0* |  0  |  0  |  0* | 0 | 0* | 0
            //   -   | -* | -  | -* |  -  |  -  |  -* | - | -* | -
            //   +   | +  | +  | +  |  +  |  +  |  +  | + | +* | +
            //  <=0  |<=0*|<=0 |<=0*| <=0 | <=0 | <=0*|<=0|<=0*|<=0
            //  !=0  | +  |!=0 | +  | !=0 | !=0 |  +  |!=0|!=0*|!=0
            //  >=0  | +  |>=0 | +  | >=0 | >=0 |  +  |>=0|>=0*|>=0
            //   Z   | +  | Z  | +  |  Z  |  Z  |  +  | Z | Z* | Z
            //   UD  |UD  |UD  |UD  |  UD | UD  | UD  |UD | UD | UD
            //  top  | +  | Z  | +  |  Z  |  Z  |  +  | Z | UD | Z
            // Notes: Similar to the LT table, but flipped between positives and negatives.
            // If the RHS is >=0, the LHS must be strictly greater than 0, since it's an exclusive bound
            // (hence >=0 > >=0 results in a strictly positive value, since 0 is not greater than 0).
            AnnotationMirror[][] gtTable = {
            //                  0    |    -    |    +    |   <=0   |   !=0   |   >=0   |   Z    |   UD    |   top   
            /*    0    */  { bottom(),   zero  , bottom(),  zero   ,   zero  , bottom(),  zero  , bottom(),  zero   },
            /*    -    */  { bottom(),   neg   , bottom(),  neg    ,   neg   , bottom(),  neg   , bottom(),  neg    },
            /*    +    */  {   pos   ,   pos   ,   pos   ,  pos    ,   pos   ,  pos    ,  pos   , bottom(),  pos    },
            /*   <=0   */  { bottom(),   lez   , bottom(),  lez    ,   lez   , bottom(),  lez   , bottom(),  lez    },
            /*   !=0   */  {   pos   , nonZero ,   pos   , nonZero , nonZero ,  pos    , nonZero, bottom(), nonZero },
            /*   >=0   */  {   pos   ,   gez   ,   pos   ,  gez    ,   gez   ,  pos    ,  gez   , bottom(),  gez    },
            /*    Z    */  {   pos   ,   allZ  ,   pos   ,  allZ   ,  allZ   ,  pos    ,  allZ  , bottom(),  allZ   },
            /*    UD   */  {   udv   ,   udv   ,   udv   ,  udv    ,  udv    ,  udv    ,  udv   ,  udv    ,   udv   },
            /*   top   */  {   pos   ,   allZ  ,   pos   ,  allZ   ,  allZ   ,  pos    ,  allZ  ,  udv    ,  allZ   }
            };
            return matchTable(gtTable, lhs, rhs);
        case GE:
            // * denotes impossible, never will be true
            // a >= b | 0 | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
            //   0    | 0 | 0  | 0* |  0  |  0  |  0  | 0 | 0* | 0
            //   -    | -*| -  | -* |  -  |  -  |  -* | - | -* | -
            //   +    | + | +  | +  |  +  |  +  |  +  | + | +* | +
            //  <=0   | 0 |<=0 |<=0*| <=0 | <=0 |  0  |<=0|<=0*|<=0
            //  !=0   | + |!=0 | +  | !=0 | !=0 |  +  |!=0|!=0*|!=0
            //  >=0   |>=0|>=0 | +  | >=0 | >=0 | >=0 |>=0|>=0*|>=0
            //   Z    |>=0| Z  | +  |  Z  |  Z  | >=0 | Z | Z* | Z
            //   UD   |UD*|UD* | UD*|  UD*|  UD*|  UD*|UD*| UD*| UD*
            //  top   |>=0| Z  | +  |  Z  |  Z  | >=0 | Z | Z* | Z
            // Notes: Similar to the LE table, but flipped between positives and negatives.
            // * <=0 >= 0 can only be true if the LHS is 0 (similarly <=0 >= >=0, though not >=0 >= <=0, which is a tautology)
            // * Being >= - gives no extra information, but being >= + means the number must be +
            // * Generally, being >= + implies the number is +, being >= >=0 means the number is >=0 (so if it already can't be 0 it must be +)
            //   Can't draw any new conclusions from being >= - or >= <=0.
            AnnotationMirror[][] geTable = {
            //                  0    |    -    |    +    |   <=0   |   !=0   |   >=0   |   Z    |   UD    |   top   
            /*    0    */  {   zero  ,   zero  , bottom(),  zero   ,   zero  ,  zero   ,  zero  , bottom(),  zero   },
            /*    -    */  { bottom(),   neg   , bottom(),  neg    ,   neg   , bottom(),  neg   , bottom(),  neg    },
            /*    +    */  {   pos   ,   pos   ,   pos   ,  pos    ,   pos   ,  pos    ,  pos   , bottom(),  pos    },
            /*   <=0   */  {   zero  ,   lez   , bottom(),  lez    ,   lez   ,  zero   ,  lez   , bottom(),  lez    },
            /*   !=0   */  {   pos   , nonZero ,   pos   , nonZero , nonZero ,  pos    , nonZero, bottom(), nonZero },
            /*   >=0   */  {   gez   ,   gez   ,   pos   ,  gez    ,   gez   ,  gez    ,  gez   , bottom(),  gez    },
            /*    Z    */  {   gez   ,  allZ   ,   pos   ,  allZ   ,  allZ   ,  gez    ,  allZ  , bottom(),  allZ   },
            /*    UD   */  {   udv   ,   udv   ,   udv   ,  udv    ,  udv    ,  udv    ,  udv   ,  udv    ,   udv   },
            /*   top   */  {   gez   ,  allZ   ,   pos   ,  allZ   ,  allZ   ,  gez    ,  allZ  ,  udv    ,  allZ   }
            };
            return matchTable(geTable, lhs, rhs);
        default:
            return lhs;
        }
    }

    /**
     * For an arithmetic expression (lhs `op` rhs), compute the point in the
     * lattice for the result of evaluating the expression. ("Top" is always a
     * legal return value, but not a very useful one.)
     *
     * <p>For example,
     * <pre>x = 1 + 0</pre>
     * should cause us to conclude that "x is not zero".
     *
     * @param operator   a binary operator
     * @param lhs        the lattice point for the left-hand side of the expression
     * @param rhs        the lattice point for the right-hand side of the expression
     * @return the lattice point for the result of the expression
     */
    private AnnotationMirror arithmeticTransfer(
            BinaryOperator operator,
            AnnotationMirror lhs,
            AnnotationMirror rhs) {
        AnnotationMirror zero = reflect(Zero.class);
        AnnotationMirror top = reflect(Top.class);
        AnnotationMirror udv = reflect(UndefinedValue.class);
        AnnotationMirror neg = reflect(StrictlyNegative.class);
        AnnotationMirror pos = reflect(StrictlyPositive.class);
        AnnotationMirror gez = reflect(GreaterThanOrEqualToZero.class);
        AnnotationMirror lez = reflect(LessThanOrEqualToZero.class);
        AnnotationMirror nonZero = reflect(NonZero.class);
        AnnotationMirror allZ = reflect(AllZ.class);

        // eliminate bottom right away
        if (equal(lhs, bottom()) || equal(rhs, bottom())) {
            return bottom();
        }

        // We will need the table for addition twice
        // a + b | 0 | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
        //   0   | 0 | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
        //   -   | - | -  | Z  |  -  |  Z  |  Z  | Z | UD | top
        //   +   | + | Z  | +  |  Z  |  Z  |  +  | Z | UD | top
        //  <=0  |<=0| -  | Z  | <=0 |  Z  |  Z  | Z | UD | top
        //  !=0  |!=0| Z  | Z  |  Z  |  Z  |  Z  | Z | UD | top
        //  >=0  |>=0| Z  | +  |  Z  |  Z  | >=0 | Z | UD | top
        //   Z   | Z | Z  | Z  |  Z  |  Z  |  Z  | Z | UD | top
        //   UD  |UD |UD  | UD |  UD |  UD |  UD |UD | UD | UD
        //  top  |top| top| top| top | top | top |top| UD | top
        // see part 1 of homework for explanation
        AnnotationMirror[][] additionTable = {
            //                  0    |    -    |    +    |   <=0   |   !=0   |   >=0   |   Z    |   UD    |   top   
            /*    0    */  {  zero   ,   neg   ,   pos   ,   lez   , nonZero ,   gez   ,  allZ  ,  udv    ,   top   },
            /*    -    */  {  neg    ,   neg   ,  allZ   ,   neg   ,  allZ   ,  allZ   ,  allZ  ,  udv    ,   top   },
            /*    +    */  {  pos    ,  allZ   ,   pos   ,  allZ   ,  allZ   ,  pos    ,  allZ  ,  udv    ,   top   },
            /*   <=0   */  {  lez    ,  neg    ,  allZ   ,  lez    ,  allZ   ,  allZ   ,  allZ  ,  udv    ,   top   },
            /*   !=0   */  {  nonZero,  allZ   ,  allZ   ,  allZ   ,  allZ   ,  allZ   ,  allZ  ,  udv    ,   top   },
            /*   >=0   */  {  gez    ,  allZ   ,  pos    ,  allZ   ,  allZ   ,  gez    ,  allZ  ,  udv    ,   top   },
            /*    Z    */  {  allZ   ,  allZ   ,  allZ   ,  allZ   ,  allZ   ,  allZ   ,  allZ  ,  udv    ,   top   },
            /*    UD   */  {  udv    ,  udv    ,  udv    ,  udv    ,  udv    ,  udv    ,  udv   ,  udv    ,   udv   },
            /*   top   */  {  top    ,  top    ,  top    ,  top    ,  top    ,  top    ,  top   ,  udv    ,   top   }        
        };

        switch (operator) {
        case PLUS:
            return matchTable(additionTable, lhs, rhs);
        case MINUS:
            // equivalent to just flipping sign on the second argument and treating as addition
            return matchTable(additionTable, lhs, flipAnnotationSign(rhs));
        case TIMES:
            // a * b | 0 | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
            //   0   | 0 | 0  | 0  |  0  |  0  |  0  | 0 | UD | top
            //   -   | 0 | +  | -  | >=0 | !=0 | <=0 | Z | UD | top
            //   +   | 0 | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
            //  <=0  | 0 | >=0| <=0| >=0 | !=0 | <=0 | Z | UD | top
            //  !=0  | 0 | !=0| !=0| !=0 | !=0 | !=0 | Z | UD | top
            //  >=0  | 0 | <=0| >=0| <=0 | !=0 | >=0 | Z | UD | top
            //   Z   | 0 | Z  | Z  |  Z  |  Z  |  Z  | Z | UD | top
            //   UD  | UD|UD  | UD |  UD |  UD |  UD |UD | UD | UD
            //  top  |top| top| top| top | top | top |top| UD | top
            // see part 1 of homework for explanation
            AnnotationMirror[][] multiplicationTable = {
                //                  0    |    -    |    +    |   <=0   |   !=0   |   >=0   |   Z    |   UD    |   top   
                /*    0    */  {  zero   ,   zero  ,   zero  ,   zero  ,   zero  ,  zero   ,  zero  ,  udv    ,   top   },
                /*    -    */  {  zero   ,  pos    ,   neg   ,   gez   , nonZero ,  lez    ,  allZ  ,  udv    ,   top   },
                /*    +    */  {  zero   ,  neg    ,   pos   ,   lez   , nonZero ,  gez    ,  allZ  ,  udv    ,   top   },
                /*   <=0   */  {  zero   ,  gez    ,   lez   ,   gez   , nonZero ,  lez    ,  allZ  ,  udv    ,   top   },
                /*   !=0   */  {  zero   , nonZero , nonZero , nonZero , nonZero ,  nonZero,  allZ  ,  udv    ,   top   },
                /*   >=0   */  {  zero   ,  allZ   ,  pos    ,  allZ   , nonZero ,  gez    ,  allZ  ,  udv    ,   top   },
                /*    Z    */  {  zero   ,  allZ   ,  allZ   ,  allZ   ,  allZ   ,  allZ   ,  allZ  ,  udv    ,   top   },
                /*    UD   */  {  udv    ,  udv    ,  udv    ,  udv    ,  udv    ,  udv    ,  udv   ,  udv    ,   udv   },
                /*   top   */  {  top    ,  top    ,  top    ,  top    ,  top    ,  top    ,  top   ,  udv    ,   top   }        
            };
            return matchTable(multiplicationTable, lhs, rhs);
        case DIVIDE:
            // a / b | 0 | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
            //   0   | UD| 0  | 0  | top |  0  | top |top| UD | top
            //   -   | UD| >=0| <=0| top |  Z  | top |top| UD | top
            //   +   | UD| <=0| >=0| top |  Z  | top |top| UD | top
            //  <=0  | UD| >=0| <=0| top |  Z  | top |top| UD | top
            //  !=0  | UD| Z  | Z  | top |  Z  | top |top| UD | top
            //  >=0  | UD| <=0| >=0| top |  Z  | top |top| UD | top
            //   Z   | UD| Z  | Z  | top |  Z  | top |top| UD | top
            //   UD  | UD|UD  | UD |  UD |  UD |  UD |UD | UD | UD
            //  top  | UD| top| top| top | top | top |top| UD | top
            // see part 1 of homework for explanation
            AnnotationMirror[][] divisionTable = {
            //                  0    |    -    |    +    |   <=0   |   !=0   |   >=0   |   Z    |   UD    |   top   
            /*    0    */  {  udv    ,  zero   ,  zero   ,   top   ,  zero   ,   top   ,  top   ,  udv    ,   top   },
            /*    -    */  {  udv    ,   gez   ,  lez    ,   top   ,  allZ   ,   top   ,  top   ,  udv    ,   top   },
            /*    +    */  {  udv    ,   lez   ,  gez    ,   top   ,  allZ   ,   top   ,  top   ,  udv    ,   top   },
            /*   <=0   */  {  udv    ,   gez   ,  lez    ,   top   ,  allZ   ,   top   ,  top   ,  udv    ,   top   },
            /*   !=0   */  {  udv    ,  allZ   ,  allZ   ,   top   ,  allZ   ,   top   ,  top   ,  udv    ,   top   },
            /*   >=0   */  {  udv    ,   lez   ,  gez    ,   top   ,  allZ   ,   top   ,  top   ,  udv    ,   top   },
            /*    Z    */  {  udv    ,  allZ   ,  allZ   ,   top   ,  allZ   ,   top   ,  top   ,  udv    ,   top   },
            /*    UD   */  {  udv    ,  udv    ,  udv    ,   udv   ,  udv    ,   udv   ,  udv   ,  udv    ,   udv   },
            /*   top   */  {  udv    ,  top    ,  top    ,   top   ,  top    ,   top   ,  top   ,  udv    ,   top   }        
            };
            return matchTable(divisionTable, lhs, rhs);
        case MOD:
            // a % b | 0 | -  | +  | <=0 | !=0 | >=0 | Z | UD | top
            //   0   | UD| 0  | 0  | top |  0  | top |top| UD | top
            //   -   | UD| <=0| <=0| top | <=0 | top |top| UD | top
            //   +   | UD| >=0| >=0| top | >=0 | top |top| UD | top
            //  <=0  | UD| <=0| <=0| top | <=0 | top |top| UD | top
            //  !=0  | UD| Z  | Z  | top |  Z  | top |top| UD | top
            //  >=0  | UD| >=0| >=0| top | >=0 | top |top| UD | top
            //   Z   | UD| Z  | Z  | top |  Z  | top |top| UD | top
            //   UD  | UD| UD | UD |  UD |  UD |  UD |UD | UD | UD
            //  top  | UD| top| top| top | top | top |top| UD | top
            // Very similar to division table, but signs work differently with mod.
            // Namely, in Java, the sign of the modulus is the sign of the left
            // operand *regardless of the sign of the right operand*
            // per http://www.cs.umd.edu/~clin/MoreJava/Intro/expr-mod.html
            AnnotationMirror[][] modTable = {
            //                  0    |    -    |    +    |   <=0   |   !=0   |   >=0   |   Z    |   UD    |   top   
            /*    0    */  {  udv    ,  zero   ,  zero   ,   top   ,  zero   ,   top   ,  top   ,  udv    ,   top   },
            /*    -    */  {  udv    ,   lez   ,  lez    ,   top   ,  lez    ,   top   ,  top   ,  udv    ,   top   },
            /*    +    */  {  udv    ,   gez   ,  gez    ,   top   ,  gez    ,   top   ,  top   ,  udv    ,   top   },
            /*   <=0   */  {  udv    ,   lez   ,  lez    ,   top   ,  lez    ,   top   ,  top   ,  udv    ,   top   },
            /*   !=0   */  {  udv    ,  allZ   ,  allZ   ,   top   ,  allZ   ,   top   ,  top   ,  udv    ,   top   },
            /*   >=0   */  {  udv    ,   gez   ,  gez    ,   top   ,  gez    ,   top   ,  top   ,  udv    ,   top   },
            /*    Z    */  {  udv    ,  allZ   ,  allZ   ,   top   ,  allZ   ,   top   ,  top   ,  udv    ,   top   },
            /*    UD   */  {  udv    ,  udv    ,  udv    ,   udv   ,  udv    ,   udv   ,  udv   ,  udv    ,   udv   },
            /*   top   */  {  udv    ,  top    ,  top    ,   top   ,  top    ,   top   ,  top   ,  udv    ,   top   }        
            };
            return matchTable(modTable, lhs, rhs);
        default:
            return top();
        }
    }

    // Flipped counterparts:
    // - : +
    // + : -
    // <=0 : >=0
    // >=0 : <=0
    // for all others, keep the same
    private AnnotationMirror flipAnnotationSign(AnnotationMirror val) {
        AnnotationMirror neg = reflect(StrictlyNegative.class);
        AnnotationMirror pos = reflect(StrictlyPositive.class);
        AnnotationMirror gez = reflect(GreaterThanOrEqualToZero.class);
        AnnotationMirror lez = reflect(LessThanOrEqualToZero.class);
        if (equal(val, neg)) {
            return pos;
        }
        if (equal(val, pos)) {
            return neg;
        }
        if (equal(val, lez)) {
            return gez;
        }
        if (equal(val, gez)) {
            return lez;
        }
        return val;
    }

    // A really dumb but simple way of getting around having to override hashcodes.
    // Just assigns an index value to each abstract value to index into an array of
    // abstract values
    private int tableIndex(AnnotationMirror val) {
        // -1 for bottom: we assume we will eliminate bottoms
        if (equal(val, bottom())) {
            return -1;
        }
        if (equal(val, reflect(Zero.class))) {
            return 0;
        }
        if (equal(val, reflect(StrictlyNegative.class))) {
            return 1;
        }
        if (equal(val, reflect(StrictlyPositive.class))) {
            return 2;
        }
        if (equal(val, reflect(LessThanOrEqualToZero.class))) {
            return 3;
        }
        if (equal(val, reflect(NonZero.class))) {
            return 4;
        }
        if (equal(val, reflect(GreaterThanOrEqualToZero.class))) {
            return 5;
        }
        if (equal(val, reflect(AllZ.class))) {
            return 6;
        }
        if (equal(val, reflect(UndefinedValue.class))) {
            return 7;
        }
        // only top remains
        return 8;
    }

    private AnnotationMirror matchTable(AnnotationMirror[][] lookupTable, AnnotationMirror lhs, AnnotationMirror rhs) {
        assert lookupTable.length == 9;
        assert lookupTable[0].length == 9;
        int lhsIdx = tableIndex(lhs);
        int rhsIdx = tableIndex(rhs);
        // eliminate bottoms first
        assert lhsIdx != -1 && rhsIdx != -1;
        return lookupTable[lhsIdx][rhsIdx];
    }

    // ========================================================================
    // Useful helpers

    /** Get the top of the lattice */
    private AnnotationMirror top() {
        return analysis.getTypeFactory().getQualifierHierarchy().getTopAnnotations().iterator().next();
    }

    /** Get the bottom of the lattice */
    private AnnotationMirror bottom() {
        return analysis.getTypeFactory().getQualifierHierarchy().getBottomAnnotations().iterator().next();
    }

    /** Compute the least-upper-bound of two points in the lattice */
    private AnnotationMirror lub(AnnotationMirror x, AnnotationMirror y) {
        return analysis.getTypeFactory().getQualifierHierarchy().leastUpperBound(x, y);
    }

    /** Compute the greatest-lower-bound of two points in the lattice */
    private AnnotationMirror glb(AnnotationMirror x, AnnotationMirror y) {
        return analysis.getTypeFactory().getQualifierHierarchy().greatestLowerBound(x, y);
    }

    /** Convert a "Class" object (e.g. "Top.class") to a point in the lattice */
    private AnnotationMirror reflect(Class<? extends Annotation> qualifier) {
        return AnnotationBuilder.fromClass(
            analysis.getTypeFactory().getProcessingEnv().getElementUtils(),
            qualifier);
    }

    /** Determine whether two AnnotationMirrors are the same point in the lattice */
    private boolean equal(AnnotationMirror x, AnnotationMirror y) {
        return AnnotationUtils.areSame(x, y);
    }

    /** `x op y` == `y flip(op) x` */
    private Comparison flip(Comparison op) {
        switch (op) {
            case EQ: return Comparison.EQ;
            case NE: return Comparison.NE;
            case LT: return Comparison.GT;
            case LE: return Comparison.GE;
            case GT: return Comparison.LT;
            case GE: return Comparison.LE;
            default: throw new IllegalArgumentException(op.toString());
        }
    }

    /** `x op y` == `!(x negate(op) y)` */
    private Comparison negate(Comparison op) {
        switch (op) {
            case EQ: return Comparison.NE;
            case NE: return Comparison.EQ;
            case LT: return Comparison.GE;
            case LE: return Comparison.GT;
            case GT: return Comparison.LE;
            case GE: return Comparison.LT;
            default: throw new IllegalArgumentException(op.toString());
        }
    }

    // ========================================================================
    // Checker Framework plumbing

    public DivByZeroTransfer(CFAnalysis analysis) {
        super(analysis);
    }

    private TransferResult<CFValue, CFStore> implementComparison(Comparison op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
        QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
        AnnotationMirror l = findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
        AnnotationMirror r = findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

        if (l == null || r == null) {
            // this can happen for generic types
            return out;
        }

        CFStore thenStore = out.getThenStore().copy();
        CFStore elseStore = out.getElseStore().copy();

        thenStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getLeftOperand()),
            refineLhsOfComparison(op, l, r));

        thenStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getRightOperand()),
            refineLhsOfComparison(flip(op), r, l));

        elseStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getLeftOperand()),
            refineLhsOfComparison(negate(op), l, r));

        elseStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getRightOperand()),
            refineLhsOfComparison(flip(negate(op)), r, l));

        return new ConditionalTransferResult<>(out.getResultValue(), thenStore, elseStore);
    }

    private TransferResult<CFValue, CFStore> implementOperator(BinaryOperator op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
        QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
        AnnotationMirror l = findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
        AnnotationMirror r = findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

        if (l == null || r == null) {
            // this can happen for generic types
            return out;
        }

        AnnotationMirror res = arithmeticTransfer(op, l, r);
        CFValue newResultValue = analysis.createSingleAnnotationValue(res, out.getResultValue().getUnderlyingType());
        return new RegularTransferResult<>(newResultValue, out.getRegularStore());
    }

    @Override
    public TransferResult<CFValue, CFStore> visitEqualTo(EqualToNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.EQ, n, super.visitEqualTo(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNotEqual(NotEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.NE, n, super.visitNotEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThan(GreaterThanNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.GT, n, super.visitGreaterThan(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThanOrEqual(GreaterThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.GE, n, super.visitGreaterThanOrEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThan(LessThanNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.LT, n, super.visitLessThan(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThanOrEqual(LessThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.LE, n, super.visitLessThanOrEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitIntegerDivision(IntegerDivisionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.DIVIDE, n, super.visitIntegerDivision(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitIntegerRemainder(IntegerRemainderNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MOD, n, super.visitIntegerRemainder(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitFloatingDivision(FloatingDivisionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.DIVIDE, n, super.visitFloatingDivision(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitFloatingRemainder(FloatingRemainderNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MOD, n, super.visitFloatingRemainder(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalMultiplication(NumericalMultiplicationNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.TIMES, n, super.visitNumericalMultiplication(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalAddition(NumericalAdditionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.PLUS, n, super.visitNumericalAddition(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalSubtraction(NumericalSubtractionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MINUS, n, super.visitNumericalSubtraction(n, p));
    }

    private static AnnotationMirror findAnnotation(
            Set<AnnotationMirror> set, QualifierHierarchy hierarchy) {
        if (set.size() == 0) {
            return null;
        }
        Set<? extends AnnotationMirror> tops = hierarchy.getTopAnnotations();
        return hierarchy.findAnnotationInSameHierarchy(set, tops.iterator().next());
    }

}

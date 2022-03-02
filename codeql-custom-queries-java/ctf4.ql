import java
//import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.TaintTracking
import semmle.code.java.dataflow.FlowSources
import DataFlow::PathGraph

/* Step 1.1 */
/** The generic interface `javax.validation.ConstraintValidator`. */
class TypeConstraintValidator extends Interface {
    TypeConstraintValidator() { this.hasQualifiedName("javax.validation", "ConstraintValidator") }
  
    /** Gets a method named `isValid` declared in this interface. */
    Method getIsValidMethod() {
      result.getDeclaringType() = this and
      result.hasName("isValid")
    }
}

/**
 * An implementation of the method named `isValid` from the
 * interface `javax.validation.ConstraintValidator`.
 */
class ConstraintValidatorIsValidMethod extends Method {
    ConstraintValidatorIsValidMethod() {
      this.overridesOrInstantiates*(any(TypeConstraintValidator t).getIsValidMethod())
    }
}

/**
 * The first parameter of a method that implements `ConstraintValidator.isValid`,
 * where the method is used to validate a field whose value comes from user input.
 */
class BeanValidationSource extends DataFlow::Node {
    BeanValidationSource() {
      exists(ConstraintValidatorIsValidMethod isValidMethod |
        // This source is the first parameter of the `isValid` method
        this.asParameter() = isValidMethod.getParameter(0) and
        // which must be present in the source code
        isValidMethod.fromSource() and
        // Bonus step: and must be used to validate user-controlled data
        Bonus::validatesUserControlledBeanProperty(isValidMethod, _, _, _)
      )
    }
}

/* Logic used for the bonus task in step 1.1. */
module Bonus {
    /**
     * Holds if `isValidMethod` is declared on the constraint validator `validatorType`
     * and is used to validate the field/property `validatedField`,
     * whose value may be obtained from the user-controlled `remoteInput`.
     */
    predicate validatesUserControlledBeanProperty(
      ConstraintValidatorIsValidMethod isValidMethod, Field validatedField, RefType validatorType,
      RemoteFlowSource remoteInput
    ) {
      // This `isValid` method is used to validate a field, or the field's class.
      validatorType = isValidMethod.getDeclaringType() and
      (
        validatedConstraint(validatedField, _, _, validatorType) or
        validatedConstraint(validatedField.getDeclaringType(), _, _, validatorType)
      ) and
      // The value of the field is obtained from user input.
      any(UserInputToValidatedFieldConfig config)
          .hasFlow(remoteInput, DataFlow::exprNode(validatedField.getAnAssignedValue()))
    }
  
    /** The interface `javax.validation.Constraint`. */
    class TypeConstraint extends Interface {
      TypeConstraint() { this.hasQualifiedName("javax.validation", "Constraint") }
    }
  
    /** A `@Constraint` annotation. */
    class ConstraintAnnotation extends Annotation {
      ConstraintAnnotation() { this.getType() instanceof TypeConstraint }
  
      /** Holds if this constraint is validated by the class `validatorType`. */
      predicate isValidatedBy(RefType validatorType) {
        validatorType =
          this.getValue("validatedBy").(ArrayInit).getAnInit().(TypeLiteral).getTypeName().getType()
      }
    }
  
    /**
     * Holds if `validatedElement` is annotated with a validation constraint defined by `constraintType`,
     * which in turn is annotated with `constraintAnnotation` and validated by `validatorType`.
     */
    predicate validatedConstraint(
      Annotatable validatedElement, RefType constraintType, ConstraintAnnotation constraintAnnotation,
      RefType validatorType
    ) {
      validatedElement.getAnAnnotation().getType() = constraintType and
      constraintType.getAnAnnotation() = constraintAnnotation and
      constraintAnnotation.isValidatedBy(validatorType)
    }
  
    // This 
    import semmle.code.java.dataflow.TaintTracking2
  
    /**
     * Taint tracking configuration describing the flow of data
     * from user input to a field.
     * This is used in the bonus part of step 1.1, to detect user-controlled bean properties.
     *
     * This analysis will be used to compute the sources of the original taint tracking configuration,
     * so we use a second copy of the taint tracking library to avoid compiler warnings due to
     * recursion through a negation.
     */
    class UserInputToValidatedFieldConfig extends TaintTracking2::Configuration {
      UserInputToValidatedFieldConfig() { this = "UserInputToValidatedFieldConfig" }
  
      override predicate isSource(DataFlow2::Node source) { source instanceof RemoteFlowSource }
  
      override predicate isSink(DataFlow2::Node sink) {
        sink.asExpr() = any(Field field).getAnAssignedValue()
      }
    }
  
    /**
     * Tracks the flow of data from a protobuf message to a corresponding Java object,
     * created using a method called `toCore<Name>`.
     * This additional step is used to track from remote input parameters
     * to bean validation of their values.
     */
    class ProtoToCoreTaintStep extends TaintTracking::AdditionalTaintStep {
      override predicate step(DataFlow::Node n1, DataFlow::Node n2) {
        exists(MethodAccess ma |
          ma.getMethod().getName().matches("toCore%") and
          n2.asExpr() = ma and
          n1.asExpr() = ma.getArgument(0)
        )
      }
    }
  
    /**
     * Tracks the flow of data through utility methods in the class `CollectionsExt`.
     * This additional step is used to track from remote input parameters
     * to bean validation of their values.
     */
    class CollectionsExtTaintStep extends TaintTracking::AdditionalTaintStep {
      override predicate step(DataFlow::Node n1, DataFlow::Node n2) {
        exists(MethodAccess ma |
          ma.getMethod().getName() = ["nullableImmutableCopyOf", "nonNull"] and
          ma.getMethod().getDeclaringType().getName() = "CollectionsExt" and
          n2.asExpr() = ma and
          n1.asExpr() = ma.getArgument(0)
        )
      }
    }
  }

predicate isSource(DataFlow::Node source) { 
    /* TODO describe source */
    //source.asExpr() instanceof StringLiteral
    //source = ConstraintValidator.getParameter(0)
    //source instanceof RemoteFlowSource
    //ConstraintValidator = source.asExpr().hasQualifiedName("javax.validation", "ConstraintValidator")

    source instanceof BeanValidationSource
}

// from Method method, MethodAccess call
// where 
//     call.getMethod() = method and
//     method.getName().matches("isValid")
// select method

// from MethodAccess call, Method method
// where 
//     call.getMethod() = method and 
//     method.getName().matches("isValid")
// select call

// from BlockStmt b
// where b.getNumStmt() = 0
// select b, "This is an empty block."
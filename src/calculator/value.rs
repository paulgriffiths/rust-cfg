use crate::errors::{Error, Result};
use rug::ops::Pow;
use rug::{Complete, Integer};
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// A typed integral or real numeric value. Integral values use arbitrary
/// precision arithmetic. Operations on Values will automatically promote
/// integers to reals when appropriate.
pub enum Value {
    Integer(Integer),
    Real(f64),
}

impl Clone for Value {
    /// Clones a value
    fn clone(&self) -> Value {
        match self {
            Value::Integer(n) => Value::Integer(n.clone()),
            Value::Real(r) => Value::Real(*r),
        }
    }
}

impl fmt::Debug for Value {
    /// Formats a value for debugging
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Integer(n) => write!(f, "(Integer) {}", n),
            Value::Real(r) => write!(f, "(Real) {}", r),
        }
    }
}

impl fmt::Display for Value {
    /// Formats a value as a string
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Integer(n) => write!(f, "{}", n),
            Value::Real(r) => write!(f, "{}", r),
        }
    }
}

impl PartialEq for Value {
    /// Tests two Values for equality.
    fn eq(&self, other: &Value) -> bool {
        match self {
            Value::Integer(first) => match other {
                Value::Integer(second) => first == second,
                Value::Real(second) => first == second,
            },
            Value::Real(first) => match other {
                Value::Integer(second) => first == second,
                Value::Real(second) => first == second,
            },
        }
    }
}

/// Implements '+' operator
impl Add for Value {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match self {
            Value::Integer(first) => match other {
                Value::Integer(second) => Value::Integer(first + second),
                Value::Real(second) => Value::Real(first.to_f64() + second),
            },
            Value::Real(first) => match other {
                Value::Integer(second) => Value::Real(first + second.to_f64()),
                Value::Real(second) => Value::Real(first + second),
            },
        }
    }
}

/// Implements binary '-' operator
impl Sub for Value {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        match self {
            Value::Integer(first) => match other {
                Value::Integer(second) => Value::Integer(first - second),
                Value::Real(second) => Value::Real(first.to_f64() - second),
            },
            Value::Real(first) => match other {
                Value::Integer(second) => Value::Real(first - second.to_f64()),
                Value::Real(second) => Value::Real(first - second),
            },
        }
    }
}

/// Implements '*' operator
impl Mul for Value {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        match self {
            Value::Integer(first) => match other {
                Value::Integer(second) => Value::Integer(first * second),
                Value::Real(second) => Value::Real(first.to_f64() * second),
            },
            Value::Real(first) => match other {
                Value::Integer(second) => Value::Real(first * second.to_f64()),
                Value::Real(second) => Value::Real(first * second),
            },
        }
    }
}

/// Implements '/' operator
impl Div for Value {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        match self {
            Value::Integer(first) => match other {
                Value::Integer(second) => {
                    // If integer division can be done without a remainer,
                    // return an integer. Otherwise, return a real.
                    let (quotient, remainder) = first.div_rem_ref(&second).complete();
                    if remainder.is_zero() {
                        Value::Integer(quotient)
                    } else {
                        Value::Real(first.to_f64() / second.to_f64())
                    }
                }
                Value::Real(second) => Value::Real(first.to_f64() / second),
            },
            Value::Real(first) => match other {
                Value::Integer(second) => Value::Real(first / second.to_f64()),
                Value::Real(second) => Value::Real(first / second),
            },
        }
    }
}

/// Implements unary '-' operator
impl Neg for Value {
    type Output = Self;

    fn neg(self) -> Self {
        match self {
            Value::Integer(n) => Value::Integer(-n),
            Value::Real(r) => Value::Real(-r),
        }
    }
}

impl Value {
    /// Creates a new integer value from a decimal string representation
    pub fn new_integer(value: &str) -> Result<Value> {
        match Integer::from_str_radix(value, 10) {
            Err(_) => Err(Error::InvalidInteger(value.to_string())),
            Ok(n) => Ok(Value::Integer(n)),
        }
    }

    /// Creates a new real value from a decimal string representation
    pub fn new_real(value: &str) -> Result<Value> {
        match value.parse::<f64>() {
            Err(_) => Err(Error::InvalidReal(value.to_string())),
            Ok(f) => Ok(Value::Real(f)),
        }
    }

    /// Returns true if a value is negative
    pub fn is_negative(&self) -> bool {
        match self {
            Value::Integer(n) => n.is_negative(),
            Value::Real(r) => *r < 0.0,
        }
    }

    /// Returns true if a value is zero
    pub fn is_zero(&self) -> bool {
        match self {
            Value::Integer(n) => n.is_zero(),
            Value::Real(r) => *r == 0.0,
        }
    }

    /// Performs exponentiation on a value
    pub fn pow(self, exp: Value) -> Self {
        match self {
            Value::Integer(base) => match exp {
                Value::Integer(exp) => {
                    // Perform exponentiation with integers if possible, as
                    // that allows us to get arbitrary length integers, but
                    // the result will be a real number if the exponent is
                    // negative, to promote to reals in that case
                    if exp.is_negative() {
                        Value::Real(base.to_f64().powf(exp.to_f64()))
                    } else {
                        let Some(e) = exp.to_u32() else {
                            panic!("exponent out of range");
                        };
                        Value::Integer(base.pow(e))
                    }
                }
                Value::Real(exp) => Value::Real(base.to_f64().powf(exp)),
            },
            Value::Real(base) => match exp {
                Value::Integer(exp) => Value::Real(base.powf(exp.to_f64())),
                Value::Real(exp) => Value::Real(base.powf(exp)),
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_clone() -> Result<()> {
        assert_eq!(Value::new_integer("3")?, Value::new_integer("3")?.clone());
        assert_eq!(Value::new_real("42.5")?, Value::new_real("42.5")?.clone());

        Ok(())
    }

    #[test]
    fn test_debug() -> Result<()> {
        assert_eq!(format!("{:?}", Value::new_integer("12")?), "(Integer) 12");
        assert_eq!(format!("{:?}", Value::new_real("42.5")?), "(Real) 42.5");

        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        assert_eq!(format!("{}", Value::new_integer("12")?), "12");
        assert_eq!(format!("{}", Value::new_integer("-12")?), "-12");
        assert_eq!(format!("{}", Value::new_integer("0")?), "0");
        assert_eq!(format!("{}", Value::new_real("42.5")?), "42.5");
        assert_eq!(format!("{}", Value::new_real("-42.5")?), "-42.5");
        assert_eq!(format!("{}", Value::new_real("0")?), "0");
        assert_eq!(format!("{}", Value::new_real("-0")?), "-0");

        Ok(())
    }

    #[test]
    fn test_eq() -> Result<()> {
        assert_eq!(Value::new_integer("3")?, Value::new_integer("3")?);
        assert_ne!(Value::new_integer("3")?, Value::new_integer("4")?);
        assert_eq!(Value::new_integer("3")?, Value::new_real("3")?);
        assert_ne!(Value::new_integer("3")?, Value::new_real("4")?);
        assert_eq!(Value::new_real("3")?, Value::new_integer("3")?);
        assert_ne!(Value::new_real("3")?, Value::new_integer("4")?);
        assert_eq!(Value::new_real("3")?, Value::new_real("3")?);
        assert_ne!(Value::new_real("3")?, Value::new_real("4")?);

        Ok(())
    }

    #[test]
    fn test_add() -> Result<()> {
        assert_eq!(
            Value::new_integer("3")? + Value::new_integer("7")?,
            Value::new_integer("10")?
        );
        assert_eq!(
            Value::new_integer("-3")? + Value::new_real("7")?,
            Value::new_real("4")?
        );
        assert_eq!(
            Value::new_real("3")? + Value::new_integer("-7")?,
            Value::new_real("-4")?
        );
        assert_eq!(
            Value::new_real("-3")? + Value::new_real("-7")?,
            Value::new_real("-10")?
        );

        Ok(())
    }

    #[test]
    fn test_sub() -> Result<()> {
        assert_eq!(
            Value::new_integer("3")? - Value::new_integer("7")?,
            Value::new_integer("-4")?
        );
        assert_eq!(
            Value::new_integer("-3")? - Value::new_real("7")?,
            Value::new_real("-10")?
        );
        assert_eq!(
            Value::new_real("3")? - Value::new_integer("-7")?,
            Value::new_real("10")?
        );
        assert_eq!(
            Value::new_real("-3")? - Value::new_real("-7")?,
            Value::new_real("4")?
        );

        Ok(())
    }

    #[test]
    fn test_mul() -> Result<()> {
        assert_eq!(
            Value::new_integer("3")? * Value::new_integer("7")?,
            Value::new_integer("21")?
        );
        assert_eq!(
            Value::new_integer("-3")? * Value::new_real("7")?,
            Value::new_real("-21")?
        );
        assert_eq!(
            Value::new_real("3")? * Value::new_integer("-7")?,
            Value::new_real("-21")?
        );
        assert_eq!(
            Value::new_real("-3")? * Value::new_real("-7")?,
            Value::new_real("21")?
        );

        Ok(())
    }

    #[test]
    fn test_div() -> Result<()> {
        assert_eq!(
            Value::new_integer("12")? / Value::new_integer("4")?,
            Value::new_integer("3")?
        );
        assert_eq!(
            Value::new_integer("12")? / Value::new_integer("24")?,
            Value::new_real("0.5")?
        );
        assert_eq!(
            Value::new_integer("-2")? / Value::new_real("8")?,
            Value::new_real("-0.25")?
        );
        assert_eq!(
            Value::new_real("2")? / Value::new_integer("-8")?,
            Value::new_real("-0.25")?
        );
        assert_eq!(
            Value::new_real("-2")? / Value::new_real("-8")?,
            Value::new_real("0.25")?
        );

        Ok(())
    }

    #[test]
    fn test_pow() -> Result<()> {
        assert_eq!(
            Value::new_integer("12")?.pow(Value::new_integer("4")?),
            Value::new_integer("20736")?
        );
        assert_eq!(
            Value::new_integer("10")?.pow(Value::new_integer("-2")?),
            Value::new_real("0.01")?
        );
        assert_eq!(
            Value::new_integer("3")?.pow(Value::new_real("4")?),
            Value::new_real("81")?
        );
        assert_eq!(
            Value::new_real("3")?.pow(Value::new_integer("4")?),
            Value::new_real("81")?
        );
        assert_eq!(
            Value::new_real("3")?.pow(Value::new_real("4")?),
            Value::new_real("81")?
        );

        Ok(())
    }

    #[test]
    fn test_neg() -> Result<()> {
        assert_eq!(-Value::new_integer("42")?, Value::new_integer("-42")?);
        assert_eq!(-Value::new_real("23.5")?, Value::new_real("-23.5")?);

        Ok(())
    }

    #[test]
    fn test_is_negative() -> Result<()> {
        assert!(Value::new_integer("-42")?.is_negative());
        assert!(!Value::new_integer("42")?.is_negative());
        assert!(Value::new_real("-0.5")?.is_negative());
        assert!(!Value::new_real("0.5")?.is_negative());

        Ok(())
    }

    #[test]
    fn test_is_zero() -> Result<()> {
        assert!(Value::new_integer("0")?.is_zero());
        assert!(!Value::new_integer("42")?.is_zero());
        assert!(Value::new_real("0.0")?.is_zero());
        assert!(Value::new_real("-0.0")?.is_zero());
        assert!(!Value::new_real("42.5")?.is_zero());

        Ok(())
    }

    #[test]
    fn test_invalid_values() {
        assert_eq!(
            Value::new_integer("oops"),
            Err(Error::InvalidInteger(String::from("oops")))
        );
        assert_eq!(
            Value::new_real("eek"),
            Err(Error::InvalidReal(String::from("eek")))
        );
    }
}

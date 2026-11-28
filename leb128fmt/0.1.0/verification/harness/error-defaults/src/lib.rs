use leb128fmt::Error;

pub fn clone_from(destination: &mut Error, source: &Error) {
    <Error as Clone>::clone_from(destination, source);
}

pub fn not_equal(left: &Error, right: &Error) -> bool {
    <Error as PartialEq>::ne(left, right)
}

#[allow(deprecated)]
pub fn assert_receiver_is_total_eq(error: &Error) {
    <Error as Eq>::assert_receiver_is_total_eq(error)
}
#[allow(deprecated)]
pub fn description(error: &Error) -> &str {
    <Error as std::error::Error>::description(error)
}

#[allow(deprecated)]
pub fn cause(error: &Error) -> Option<&dyn std::error::Error> {
    <Error as std::error::Error>::cause(error)
}

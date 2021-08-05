use crate::tests;

use super::DEFAULT_DYNAMIC_POOL;

#[test]
fn swap_with_exact_base_correctly_evaluates_all_pool_assets() {
    tests::swap_with_exact_base_correctly_evaluates_all_pool_assets(DEFAULT_DYNAMIC_POOL)
}

#[test]
fn swap_with_exact_quote_correctly_evaluates_all_pool_assets() {
    tests::swap_with_exact_quote_correctly_evaluates_all_pool_assets(DEFAULT_DYNAMIC_POOL)
}

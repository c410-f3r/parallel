use crate::{
    mock::{Amm, ExtBuilder, Origin, Tokens, ALICE, BOB},
    tests::{self, DEFAULT_STABLE_POOL},
};
use orml_traits::MultiCurrency;
use parallel_primitives::{token_units, CurrencyId};

#[test]
fn does_not_incur_slippage_if_amount_is_less_or_equal_than_12_pct() {
    ExtBuilder::default().build().execute_with(|| {
        let pool = DEFAULT_STABLE_POOL;
        let total_amount = pool.base_amount + pool.quote_amount;
        let x = total_amount / 100 * 12;
        Amm::create_pool(Origin::signed(ALICE), pool.clone()).unwrap();
        Amm::swap_with_exact_base(Origin::signed(BOB), 0, x, 100).unwrap();
        assert_eq!(
            Tokens::free_balance(CurrencyId::DOT, &BOB),
            token_units(1000).unwrap() - x
        );
        assert_eq!(
            Tokens::free_balance(CurrencyId::xDOT, &BOB),
            token_units(1000).unwrap() + x
        );
    });
}

#[test]
fn incurs_slippage_if_amount_is_greater_than_12_pct() {
    ExtBuilder::default().build().execute_with(|| {
        let pool = DEFAULT_STABLE_POOL;
        let total_amount = pool.base_amount + pool.quote_amount;
        let x = total_amount / 100 * 13;
        Amm::create_pool(Origin::signed(ALICE), pool.clone()).unwrap();
        Amm::swap_with_exact_base(Origin::signed(BOB), 0, x, 100).unwrap();
        assert_eq!(
            Tokens::free_balance(CurrencyId::DOT, &BOB),
            token_units(1000).unwrap() - x
        );
        assert!(Tokens::free_balance(CurrencyId::xDOT, &BOB) > token_units(1000).unwrap() + x);
    });
}

#[test]
fn swap_with_exact_base_correctly_evaluates_all_pool_assets() {
    tests::swap_with_exact_base_correctly_evaluates_all_pool_assets(DEFAULT_STABLE_POOL)
}

#[test]
fn swap_with_exact_quote_correctly_evaluates_all_pool_assets() {
    tests::swap_with_exact_quote_correctly_evaluates_all_pool_assets(DEFAULT_STABLE_POOL)
}

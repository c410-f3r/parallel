#![cfg(test)]

mod dynamic;
mod stable;

use crate::{
    amm_type::AmmType,
    mock::{Amm, ExtBuilder, Origin, Runtime, Tokens, ALICE, BOB},
    Pool, Pools, Error
};
use frame_support::assert_noop;
use orml_traits::MultiCurrency;
use parallel_primitives::{token_units, CurrencyId};

const DEFAULT_DYNAMIC_POOL: Pool = Pool {
    amm_type: AmmType::Dynamic,
    base_amount: 50,
    quote_amount: 50,
    asset_base: CurrencyId::DOT,
    asset_quote: CurrencyId::xDOT,
};
const DEFAULT_STABLE_POOL: Pool = Pool {
    amm_type: AmmType::Stable,
    base_amount: 50,
    quote_amount: 50,
    asset_base: CurrencyId::DOT,
    asset_quote: CurrencyId::xDOT,
};

#[test]
fn create_pool_stores_a_pool() {
    ExtBuilder::default().build().execute_with(|| {
        let pool = DEFAULT_DYNAMIC_POOL;
        Amm::create_pool(Origin::signed(ALICE), pool.clone()).unwrap();
        assert_eq!(Pools::<Runtime>::get(0).unwrap(), pool)
    });
}

#[test]
fn create_pool_does_not_allow_pairs_with_the_same_asset() {
    ExtBuilder::default().build().execute_with(|| {
        let mut pool = DEFAULT_DYNAMIC_POOL;
        pool.asset_base = CurrencyId::KSM;
        pool.asset_quote = CurrencyId::KSM;
        assert_noop!(
            Amm::create_pool(Origin::signed(ALICE), pool),
            Error::<Runtime>::AssetsCanNotBeEqual
        );
    });
}

fn swap_with_exact_base_correctly_evaluates_all_pool_assets(pool: Pool) {
    ExtBuilder::default().build().execute_with(|| {
        Amm::create_pool(Origin::signed(ALICE), pool).unwrap();
        Amm::swap_with_exact_base(Origin::signed(BOB), 0, 1, 10).unwrap();
        let pool_account = Amm::pool_account(&0);
        assert_eq!(
            Tokens::free_balance(CurrencyId::DOT, &pool_account),
            DEFAULT_DYNAMIC_POOL.base_amount + 1
        );
        assert_eq!(
            Tokens::free_balance(CurrencyId::xDOT, &pool_account),
            DEFAULT_DYNAMIC_POOL.quote_amount - 1
        );
        assert_eq!(
            Tokens::free_balance(CurrencyId::DOT, &BOB),
            token_units(1000).unwrap() - 1
        );
        assert_eq!(
            Tokens::free_balance(CurrencyId::xDOT, &BOB),
            token_units(1000).unwrap() + 1
        );
    });
}

fn swap_with_exact_quote_correctly_evaluates_all_pool_assets(pool: Pool) {
    ExtBuilder::default().build().execute_with(|| {
        Amm::create_pool(Origin::signed(ALICE), pool).unwrap();
        Amm::swap_with_exact_quote(Origin::signed(BOB), 0, 1, 0).unwrap();
        let pool_account = Amm::pool_account(&0);
        assert_eq!(
            Tokens::free_balance(CurrencyId::DOT, &pool_account),
            DEFAULT_DYNAMIC_POOL.base_amount - 1
        );
        assert_eq!(
            Tokens::free_balance(CurrencyId::xDOT, &pool_account),
            DEFAULT_DYNAMIC_POOL.quote_amount + 1
        );
        assert_eq!(
            Tokens::free_balance(CurrencyId::DOT, &BOB),
            token_units(1000).unwrap() + 1
        );
        assert_eq!(
            Tokens::free_balance(CurrencyId::xDOT, &BOB),
            token_units(1000).unwrap() - 1
        );
    });
}

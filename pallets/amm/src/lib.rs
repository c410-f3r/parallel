// Copyright 2021 Parallel Finance Developer.
// This file is part of Parallel Finance.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Automatic Market Maker (AMM)
//!
//! Given any [X, Y] asset pair, "base" is the `X` asset while "quote" is the `Y` asset.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod amm_type;
mod amount_evaluation;
mod mock;
mod pool;
mod tests;

use amm_type::AmmType;
use amount_evaluation::AmountEvaluation;
pub use pallet::*;
use pool::{LiquidityProviderAmounts, Pool};

#[frame_support::pallet]
mod pallet {
    use crate::{AmmType, AmountEvaluation, LiquidityProviderAmounts, Pool};
    use core::{marker::PhantomData, ops::RangeInclusive};
    use frame_support::{Blake2_128Concat, PalletId, Parameter, dispatch::DispatchResult, pallet_prelude::{StorageDoubleMap, StorageMap, StorageValue, ValueQuery}, traits::{EnsureOrigin, GenesisBuild, Get, Hooks, IsType}};
    use frame_system::{ensure_signed, pallet_prelude::OriginFor};
    use orml_traits::{MultiCurrency, MultiCurrencyExtended};
    use parallel_primitives::{Amount, Balance, CurrencyId, Rate};
    use sp_arithmetic::traits::BaseArithmetic;
    use sp_runtime::{
        traits::{AccountIdConversion, CheckedAdd, Saturating},
        ArithmeticError, DispatchError, FixedPointNumber, SaturatedConversion,
    };

    // Amplification Coefficient Weight.
    //
    // In this pallet, the actual amplification coefficient will be `exchange_rate` * `ACW`.
    const ACW: Rate = Rate::from_inner(Rate::DIV / 100 * 50); // 50%

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Adds liquidity to a pool based on the provided base amount and the quote amount range.
        #[pallet::weight(0)]
        #[frame_support::transactional]
        pub fn add_liquidity(
            origin: OriginFor<T>,
            base_amount: Balance,
            quote_amount_range: RangeInclusive<Balance>,
            pool_id: T::PoolId,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;
            let pool = Self::pool(&pool_id)?;
            let pool_account = Self::pool_account(&pool_id);
            Self::operate_liquidity(
                base_amount,
                &who,
                |stored_pool, amount_evaluation| {
                    let diff = amount_evaluation.account_amount;
                    Self::ensure_amount_range_is_within_value(&quote_amount_range, &diff)?;
                    Self::mutate_liquidity_provider(&pool_id, &who, |lp_amounts| {
                        lp_amounts.base_amount = lp_amounts
                            .base_amount
                            .checked_add(base_amount)
                            .ok_or(ArithmeticError::Overflow)?;
                        lp_amounts.quote_amount = lp_amounts
                            .quote_amount
                            .checked_add(diff)
                            .ok_or(ArithmeticError::Overflow)?;
                        Ok(())
                    })?;
                    stored_pool.base_amount = stored_pool
                        .base_amount
                        .checked_add(base_amount)
                        .ok_or(ArithmeticError::Overflow)?;
                    stored_pool.quote_amount = stored_pool
                        .quote_amount
                        .checked_add(diff)
                        .ok_or(ArithmeticError::Overflow)?;
                    Ok(())
                },
                &pool_id,
                &pool,
                &pool_account,
                Self::calculate_added_base_amount(base_amount, &pool)?,
            )
        }

        /// Creates an initial pool with the specified asset ratio.
        #[pallet::weight(0)]
        #[frame_support::transactional]
        pub fn create_pool(origin: OriginFor<T>, pool: Pool) -> DispatchResult {
            let who = ensure_signed(origin)?;
            if pool.asset_base == pool.asset_quote {
                return Err(Error::<T>::AssetsCanNotBeEqual.into());
            }
            let pool_id = Self::increase_pools_counter()?;
            let pool_account = Self::pool_account(&pool_id);
            LiquidityProviders::<T>::insert(
                &pool_id,
                &who,
                LiquidityProviderAmounts {
                    base_amount: pool.base_amount,
                    quote_amount: pool.quote_amount,
                },
            );
            T::Currency::transfer(pool.asset_base, &who, &pool_account, pool.base_amount)?;
            T::Currency::transfer(pool.asset_quote, &who, &pool_account, pool.quote_amount)?;
            <Pools<T>>::insert(pool_id, pool);
            Ok(())
        }

        /// Removes liquidity of a pool based on the provided base amount and the quote amount range.
        #[pallet::weight(0)]
        #[frame_support::transactional]
        pub fn remove_liquidity(
            origin: OriginFor<T>,
            base_amount: Balance,
            quote_amount_range: RangeInclusive<Balance>,
            pool_id: T::PoolId,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;
            let pool = Self::pool(&pool_id)?;
            let pool_account = Self::pool_account(&pool_id);
            Self::operate_liquidity(
                base_amount,
                &pool_account,
                |stored_pool, amount_evaluation| {
                    let diff = amount_evaluation.account_amount;
                    Self::ensure_amount_range_is_within_value(&quote_amount_range, &diff)?;
                    Self::mutate_liquidity_provider(&pool_id, &who, |lp_amounts| {
                        lp_amounts.base_amount = lp_amounts
                            .base_amount
                            .checked_sub(base_amount)
                            .ok_or(ArithmeticError::Underflow)?;
                        lp_amounts.quote_amount = lp_amounts
                            .quote_amount
                            .checked_sub(diff)
                            .ok_or(ArithmeticError::Underflow)?;
                        Ok(())
                    })?;
                    stored_pool.base_amount = stored_pool
                        .base_amount
                        .checked_sub(base_amount)
                        .ok_or(ArithmeticError::Underflow)?;
                    stored_pool.quote_amount = stored_pool
                        .quote_amount
                        .checked_sub(diff)
                        .ok_or(ArithmeticError::Underflow)?;
                    Ok(())
                },
                &pool_id,
                &pool,
                &who,
                Self::calculate_subtracted_base_amount(base_amount, &pool)?,
            )
        }

        // Swaps the base asset for the corresponding quote asset or in other words, performs
        // a sell operation.
        #[pallet::weight(0)]
        #[frame_support::transactional]
        pub fn swap_with_exact_base(
            origin: OriginFor<T>,
            pool_id: T::PoolId,
            #[pallet::compact] base_amount: Balance,
            #[pallet::compact] max_quote_amount: Balance,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;
            let pool = Self::pool(&pool_id)?;
            let pool_base_amount = Self::calculate_subtracted_base_amount(base_amount, &pool)?;
            let AmountEvaluation {
                account_amount: account_quote_amount,
                pool_amount: pool_quote_amount,
            } = Self::calculate_amount(&pool, pool_base_amount)?;
            Self::ensure_amount_range_is_within_value(
                &(0..=max_quote_amount),
                &account_quote_amount,
            )?;
            let actual_account_quote_amount = Self::manage_swap_fee(
                &who,
                &pool_id,
                pool.asset_quote,
                account_quote_amount,
                |lp_amounts, fee| {
                    lp_amounts.quote_amount = lp_amounts
                        .quote_amount
                        .checked_add(fee)
                        .ok_or(ArithmeticError::Overflow)?;
                    Ok(())
                },
            )?;
            let pool_account = Self::pool_account(&pool_id);
            Self::swap(
                base_amount,
                actual_account_quote_amount,
                &who,
                pool_base_amount,
                pool_id,
                pool_quote_amount,
                &pool,
                &pool_account,
            )
        }

        // Swaps the quote asset for the corresponding base asset or in other words, performs
        // a buy operation.
        #[pallet::weight(0)]
        #[frame_support::transactional]
        pub fn swap_with_exact_quote(
            origin: OriginFor<T>,
            pool_id: T::PoolId,
            #[pallet::compact] quote_amount: Balance,
            #[pallet::compact] min_base_amount: Balance,
        ) -> DispatchResult {
            let who = ensure_signed(origin)?;
            let pool = Self::pool(&pool_id)?;
            let pool_quote_amount = Self::calculate_subtracted_quote_amount(quote_amount, &pool)?;
            let AmountEvaluation {
                account_amount: account_base_amount,
                pool_amount: pool_base_amount,
            } = Self::calculate_amount(&pool, pool_quote_amount)?;
            Self::ensure_amount_range_is_within_value(
                &(min_base_amount..=Balance::MAX),
                &account_base_amount,
            )?;
            let actual_account_base_amount = Self::manage_swap_fee(
                &who,
                &pool_id,
                pool.asset_base,
                account_base_amount,
                |lp_amounts, fee| {
                    lp_amounts.base_amount = lp_amounts
                        .base_amount
                        .checked_add(fee)
                        .ok_or(ArithmeticError::Overflow)?;
                    Ok(())
                },
            )?;
            let pool_account = Self::pool_account(&pool_id);
            Self::swap(
                actual_account_base_amount,
                quote_amount,
                &pool_account,
                pool_base_amount,
                pool_id,
                pool_quote_amount,
                &pool,
                &who,
            )
        }
    }

    #[pallet::config]
    pub trait Config: frame_system::Config {
        type Currency: MultiCurrencyExtended<
            Self::AccountId,
            CurrencyId = CurrencyId,
            Balance = Balance,
            Amount = Amount,
        >;
        type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
        type LpFee: Get<Rate>;
        type PalletId: Get<PalletId>;
        type PoolId: Default + BaseArithmetic + Parameter;
        type TreasuryAccount: Get<Self::AccountId>;
        type TreasuryFee: Get<Rate>;
        type UpdateOrigin: EnsureOrigin<Self::Origin>;
    }

    #[pallet::error]
    pub enum Error<T> {
        /// It is not possible to create a pool with the equal assets.
        AssetsCanNotBeEqual,
        /// The corresponding amounts of a liquidity provided could not be found.
        LiquidityProviderDoesNotExist,
        /// Stored pool fetched by its corresponding id does not exist.
        PoolDoesNotExist,
        /// Provided amount does not satisfy the current pool asset ratio.
        PoolDoesNotSatisfySlippage,
    }

    #[pallet::event]
    pub enum Event<T>
    where
        T: Config, {}

    #[pallet::genesis_config]
    pub struct GenesisConfig<T> {
        pub exchange_rate: Rate,
        pub phantom: PhantomData<T>,
    }

    #[cfg(feature = "std")]
    impl<T> Default for GenesisConfig<T> {
        fn default() -> Self {
            GenesisConfig {
                exchange_rate: Default::default(),
                phantom: PhantomData,
            }
        }
    }

    #[pallet::genesis_build]
    impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
        fn build(&self) {
            ExchangeRate::<T>::put(self.exchange_rate);
        }
    }

    #[pallet::hooks]
    impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {}

    #[pallet::pallet]
    pub struct Pallet<T>(PhantomData<T>);

    impl<T> Pallet<T>
    where
        T: Config,
    {
        // Each pool has an account derived from the pool id.
        pub(crate) fn pool_account(pool_id: &T::PoolId) -> T::AccountId {
            T::PalletId::get().into_sub_account(pool_id)
        }

        // Multiplies an arbitrary coefficient value with the current amplification coefficient.
        fn amplification_coeficient_mul(n: u128) -> Option<u128> {
            let exchange_rate = ExchangeRate::<T>::get();
            // Saturates because a very large amplification coefficient
            // will simply shape the curve as a constant sum equation.
            let amplif_coefficient = ACW.saturating_add(exchange_rate);
            amplif_coefficient.checked_mul_int(n)
        }

        // Adds the base amount of the provided pool with the given `amount`.
        fn calculate_added_base_amount(
            amount: Balance,
            pool: &Pool,
        ) -> Result<u128, DispatchError> {
            let opt = pool.base_amount.checked_add(amount);
            let rslt = opt.ok_or(ArithmeticError::Overflow)?;
            Ok(rslt)
        }

        // Subtracts the base amount of the provided pool with the given `amount`.
        fn calculate_subtracted_base_amount(
            amount: Balance,
            pool: &Pool,
        ) -> Result<u128, DispatchError> {
            let opt = pool.base_amount.checked_sub(amount);
            let rslt = opt.ok_or(ArithmeticError::Underflow)?;
            Ok(rslt)
        }

        // Subtracts the base amount of the provided pool with the given `amount`.
        fn calculate_subtracted_quote_amount(
            amount: Balance,
            pool: &Pool,
        ) -> Result<u128, DispatchError> {
            let opt = pool.quote_amount.checked_sub(amount);
            let rslt = opt.ok_or(ArithmeticError::Underflow)?;
            Ok(rslt)
        }

        // Calculates the amount according to the underlying formula and the provided pool.
        //
        // AmmType::Dynamic: let [x|y] = k / [x|y];
        // AmmType::Stable: let [x|y] = (k * (4*A*k + k - 4*A*[x|y])) / (4 * (A*k + [x|y]));
        fn calculate_amount(
            pool: &Pool,
            new_amount: Balance,
        ) -> Result<AmountEvaluation, DispatchError> {
            let k = Self::total_assets(pool.amm_type, pool)?;
            let opt = match pool.amm_type {
                AmmType::Dynamic => k.checked_div(new_amount),
                AmmType::Stable => {
                    let f = || {
                        let ak = Self::amplification_coeficient_mul(k)?;
                        let _4ax =
                            4u128.checked_mul(Self::amplification_coeficient_mul(new_amount)?)?;
                        let _4ak = 4u128.checked_mul(ak)?;
                        let dividend = k.checked_mul(_4ak.checked_add(k)?.checked_sub(_4ax)?)?;
                        let divisor = 4u128.checked_mul(ak.checked_add(new_amount)?)?;
                        dividend.checked_div(divisor)
                    };
                    f()
                }
            };
            let rslt = opt.ok_or_else::<DispatchError, _>(|| ArithmeticError::Overflow.into())?;
            let [greater, lesser] = if pool.quote_amount > rslt {
                [pool.quote_amount, rslt]
            } else {
                [rslt, pool.quote_amount]
            };
            let diff = greater
                .checked_sub(lesser)
                .ok_or_else::<DispatchError, _>(|| ArithmeticError::Underflow.into())?;
            Ok(AmountEvaluation {
                account_amount: diff,
                pool_amount: rslt,
            })
        }

        fn ensure_amount_range_is_within_value(
            quote_amount_range: &RangeInclusive<Balance>,
            value: &Balance,
        ) -> DispatchResult {
            if !quote_amount_range.contains(value) {
                return Err(Error::<T>::PoolDoesNotSatisfySlippage.into());
            }
            Ok(())
        }

        // Increases the internal pool counter by 1 and returns the id that should
        // be attached to a new stored pool.
        fn increase_pools_counter() -> Result<T::PoolId, DispatchError> {
            let curr = <PoolsCounter<T>>::get();
            <PoolsCounter<T>>::try_mutate(|n| {
                let opt = n.checked_add(&T::PoolId::from(1u8));
                *n = opt.ok_or_else::<DispatchError, _>(|| ArithmeticError::Overflow.into())?;
                Ok::<_, DispatchError>(())
            })?;
            Ok(curr)
        }

        // Sends fees to Liquidity Providers and Treasury based on the performed amount
        // of swapped quote.
        //
        // Returns the new quote amount minus transferred fees.
        fn manage_swap_fee<F>(
            account_id: &T::AccountId,
            pool_id: &T::PoolId,
            swapped_asset: CurrencyId,
            swapped_amount: Balance,
            mut cb: F,
        ) -> Result<Balance, DispatchError>
        where
            F: FnMut(&mut LiquidityProviderAmounts, Balance) -> DispatchResult,
        {
            let total_fee = T::LpFee::get()
                .checked_mul_int(swapped_amount)
                .ok_or(ArithmeticError::Overflow)?;
            let treasury_fee = T::TreasuryFee::get()
                .checked_mul_int(total_fee)
                .ok_or(ArithmeticError::Overflow)?;
            let lp_fee = total_fee
                .checked_sub(treasury_fee)
                .ok_or(ArithmeticError::Underflow)?;
            let amount_minus_fee = swapped_amount
                .checked_sub(total_fee)
                .ok_or(ArithmeticError::Underflow)?;

            let liquidity_providers: Vec<_> =
                LiquidityProviders::<T>::iter_prefix(pool_id).collect();
            let individual_lp_fee = lp_fee
                .checked_div(liquidity_providers.len().saturated_into())
                .ok_or(ArithmeticError::Underflow)?;
            for (lp_account, _) in liquidity_providers {
                Self::mutate_liquidity_provider(pool_id, &lp_account, |lp_amounts| {
                    cb(lp_amounts, individual_lp_fee)
                })?;
                T::Currency::transfer(swapped_asset, account_id, &lp_account, individual_lp_fee)?;
            }
            T::Currency::transfer(
                swapped_asset,
                account_id,
                &T::TreasuryAccount::get(),
                treasury_fee,
            )?;
            Ok(amount_minus_fee)
        }

        fn mutate_liquidity_provider<F>(
            pool_id: &T::PoolId,
            account_id: &T::AccountId,
            cb: F,
        ) -> DispatchResult
        where
            F: FnOnce(&mut LiquidityProviderAmounts) -> DispatchResult,
        {
            LiquidityProviders::<T>::try_mutate(pool_id, account_id, |opt| {
                if let Some(market) = opt {
                    cb(market)?;
                    return Ok(());
                }
                Err(Error::<T>::LiquidityProviderDoesNotExist.into())
            })
        }

        fn mutate_pool<F>(pool_id: &T::PoolId, cb: F) -> DispatchResult
        where
            F: FnOnce(&mut Pool) -> DispatchResult,
        {
            Pools::<T>::try_mutate(pool_id, |opt| {
                if let Some(market) = opt {
                    cb(market)?;
                    return Ok(());
                }
                Err(Error::<T>::PoolDoesNotExist.into())
            })
        }

        // Generic method that adds or removes liquidity
        fn operate_liquidity<F>(
            base_amount: Balance,
            from: &T::AccountId,
            mutate_pool: F,
            pool_id: &T::PoolId,
            pool: &Pool,
            to: &T::AccountId,
            new_amount: u128,
        ) -> DispatchResult
        where
            F: Fn(&mut Pool, &AmountEvaluation) -> DispatchResult,
        {
            let amount_evaluation = Self::calculate_amount(&pool, new_amount)?;
            T::Currency::transfer(pool.asset_base, from, to, base_amount)?;
            T::Currency::transfer(pool.asset_quote, from, to, amount_evaluation.account_amount)?;
            Self::mutate_pool(&pool_id, |stored_pool| {
                mutate_pool(stored_pool, &amount_evaluation)?;
                Ok(())
            })
        }

        // Retrieves a stored pool by its ID.
        fn pool(pool_id: &T::PoolId) -> Result<Pool, DispatchError> {
            Pools::<T>::get(pool_id).ok_or_else(|| Error::<T>::PoolDoesNotExist.into())
        }

        // Internal swap transfers
        fn swap(
            account_base_amount: Balance,
            account_quote_amount: Balance,
            from: &T::AccountId,
            pool_base_amount: Balance,
            pool_id: T::PoolId,
            pool_quote_amount: Balance,
            pool: &Pool,
            to: &T::AccountId,
        ) -> DispatchResult {
            T::Currency::transfer(pool.asset_base, from, to, account_base_amount)?;
            T::Currency::transfer(pool.asset_quote, to, from, account_quote_amount)?;
            Self::mutate_pool(&pool_id, |stored_pool| {
                stored_pool.base_amount = pool_base_amount;
                stored_pool.quote_amount = pool_quote_amount;
                Ok(())
            })?;

            Ok(())
        }

        // Calculates the total assets of a pool
        fn total_assets(amm_type: AmmType, pool: &Pool) -> Result<Balance, DispatchError> {
            let opt = match amm_type {
                AmmType::Dynamic => pool.base_amount.checked_mul(pool.quote_amount),
                AmmType::Stable => pool.base_amount.checked_add(pool.quote_amount),
            };
            opt.ok_or_else(|| ArithmeticError::Overflow.into())
        }
    }

    /// The exchange rate from the underlying to the internal collateral
    #[pallet::storage]
    pub type ExchangeRate<T: Config> = StorageValue<_, Rate, ValueQuery>;

    /// Accounts that deposits and withdraw assets in one or more pools
    #[pallet::storage]
    pub type LiquidityProviders<T: Config> = StorageDoubleMap<
        _,
        Blake2_128Concat,
        T::PoolId,
        Blake2_128Concat,
        T::AccountId,
        LiquidityProviderAmounts,
    >;

    /// A bag of liquidity composed by two different assets
    #[pallet::storage]
    pub type Pools<T: Config> = StorageMap<_, Blake2_128Concat, T::PoolId, Pool>;

    /// Auxiliary storage used to track pool ids
    #[pallet::storage]
    pub type PoolsCounter<T: Config> = StorageValue<_, T::PoolId, ValueQuery>;
}

/**
 *Submitted for verification at FtmScan.com on 2021-09-29
*/

// SPDX-License-Identifier: MIT

pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

// Global Enums and Structs



struct SingleAssetHedgeFarmingConfig {
    // A portion of want token is depoisited into a lending platform to be used as
    // collateral. Short token is borrowed and compined with the remaining want token
    // and deposited into LP and farmed.
    address want;
    address short;
    /*****************************/
    /*             Farm           */
    /*****************************/
    // Liquidity pool address for base <-> short tokens
    address wantShortLP;
    // Address for farming reward token - eg Spirit/BOO
    address farmToken;
    // Liquidity pool address for farmToken <-> wFTM
    address farmTokenLp;
    // Farm address for reward farming
    address farmMasterChef;
    // farm PID for base <-> short LP farm
    uint256 farmPid;
    /*****************************/
    /*        Money Market       */
    /*****************************/
    // Base token cToken @ MM
    address cTokenLend;
    // Short token cToken @ MM
    address cTokenBorrow;
    // Lend/Borrow rewards
    address compToken;
    address compTokenLP;
    // address compLpAddress = 0x613BF4E46b4817015c01c6Bb31C7ae9edAadc26e;
    address comptroller;
    /*****************************/
    /*            AMM            */
    /*****************************/
    // Liquidity pool address for base <-> short tokens @ the AMM.
    // @note: the AMM router address does not need to be the same
    // AMM as the farm, in fact the most liquid AMM is prefered to
    // minimise slippage.
    address router;
}

// Part: ICTokenStorage

interface ICTokenStorage {
    /**
     * @dev Container for borrow balance information
     * @member principal Total balance (with accrued interest), after applying the most recent balance-changing action
     * @member interestIndex Global borrowIndex as of the most recent balance-changing action
     */
    struct BorrowSnapshot {
        uint256 principal;
        uint256 interestIndex;
    }
}

// Part: ICompPriceOracle

interface ICompPriceOracle {
    function isPriceOracle() external view returns (bool);
    /**
      * @notice Get the underlying price of a cToken asset
      * @param cToken The cToken to get the underlying price of
      * @return The underlying asset price mantissa (scaled by 1e18).
      *  Zero means the price is unavailable.
      */
    function getUnderlyingPrice(address cToken) external view returns (uint);
}

// Part: IComptroller

interface IComptroller {
    /*** Assets You Are In ***/

    function enterMarkets(address[] calldata cTokens)
        external
        returns (uint256[] memory);

    function exitMarket(address cToken) external returns (uint256);

    /*** Policy Hooks ***/

    function mintAllowed(
        address cToken,
        address minter,
        uint256 mintAmount
    ) external returns (uint256);

    function mintVerify(
        address cToken,
        address minter,
        uint256 mintAmount,
        uint256 mintTokens
    ) external;

    function redeemAllowed(
        address cToken,
        address redeemer,
        uint256 redeemTokens
    ) external returns (uint256);

    function redeemVerify(
        address cToken,
        address redeemer,
        uint256 redeemAmount,
        uint256 redeemTokens
    ) external;

    function borrowAllowed(
        address cToken,
        address borrower,
        uint256 borrowAmount
    ) external returns (uint256);

    function borrowVerify(
        address cToken,
        address borrower,
        uint256 borrowAmount
    ) external;

    function repayBorrowAllowed(
        address cToken,
        address payer,
        address borrower,
        uint256 repayAmount
    ) external returns (uint256);

    function repayBorrowVerify(
        address cToken,
        address payer,
        address borrower,
        uint256 repayAmount,
        uint256 borrowerIndex
    ) external;

    function liquidateBorrowAllowed(
        address cTokenBorrowed,
        address cTokenCollateral,
        address liquidator,
        address borrower,
        uint256 repayAmount
    ) external returns (uint256);

    function liquidateBorrowVerify(
        address cTokenBorrowed,
        address cTokenCollateral,
        address liquidator,
        address borrower,
        uint256 repayAmount,
        uint256 seizeTokens
    ) external;

    function seizeAllowed(
        address cTokenCollateral,
        address cTokenBorrowed,
        address liquidator,
        address borrower,
        uint256 seizeTokens
    ) external returns (uint256);

    function seizeVerify(
        address cTokenCollateral,
        address cTokenBorrowed,
        address liquidator,
        address borrower,
        uint256 seizeTokens
    ) external;

    function transferAllowed(
        address cToken,
        address src,
        address dst,
        uint256 transferTokens
    ) external returns (uint256);

    function transferVerify(
        address cToken,
        address src,
        address dst,
        uint256 transferTokens
    ) external;

    function claimComp(address holder) external;

    /*** Liquidity/Liquidation Calculations ***/

    function liquidateCalculateSeizeTokens(
        address cTokenBorrowed,
        address cTokenCollateral,
        uint256 repayAmount
    ) external view returns (uint256, uint256);
}

// Part: IFarmMasterChef

interface IFarmMasterChef {
    function deposit(uint256 _pid, uint256 _amount) external;

    function withdraw(uint256 _pid, uint256 _amount) external;

    function userInfo(uint256 _pid, address user)
        external
        view
        returns (uint256);
}

// Part: IPriceOracle

interface IPriceOracle {
    function getPrice() external view returns (uint256);
}

// Part: IUniswapV2Router01

interface IUniswapV2Router01 {
    function factory() external pure returns (address);

    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    )
        external
        returns (
            uint256 amountA,
            uint256 amountB,
            uint256 liquidity
        );

    function addLiquidityETH(
        address token,
        uint256 amountTokenDesired,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    )
        external
        payable
        returns (
            uint256 amountToken,
            uint256 amountETH,
            uint256 liquidity
        );

    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint256 liquidity,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountA, uint256 amountB);

    function removeLiquidityETH(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountToken, uint256 amountETH);

    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint256 liquidity,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountA, uint256 amountB);

    function removeLiquidityETHWithPermit(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountToken, uint256 amountETH);

    function swapExactTokensForTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapTokensForExactTokens(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapExactETHForTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable returns (uint256[] memory amounts);

    function swapTokensForExactETH(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapExactTokensForETH(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapETHForExactTokens(
        uint256 amountOut,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable returns (uint256[] memory amounts);

    function quote(
        uint256 amountA,
        uint256 reserveA,
        uint256 reserveB
    ) external pure returns (uint256 amountB);

    function getAmountOut(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) external pure returns (uint256 amountOut);

    function getAmountIn(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut
    ) external pure returns (uint256 amountIn);

    function getAmountsOut(uint256 amountIn, address[] calldata path)
        external
        view
        returns (uint256[] memory amounts);

    function getAmountsIn(uint256 amountOut, address[] calldata path)
        external
        view
        returns (uint256[] memory amounts);
}

// Part: InterestRateModel

/**
 * @title Compound's InterestRateModel Interface
 * @author Compound
 */
interface InterestRateModel {
    /**
     * @dev Calculates the current borrow interest rate per block
     * @param cash The total amount of cash the market has
     * @param borrows The total amount of borrows the market has outstanding
     * @param reserves The total amnount of reserves the market has
     * @return The borrow rate per block (as a percentage, and scaled by 1e18)
     */
    function getBorrowRate(
        uint256 cash,
        uint256 borrows,
        uint256 reserves
    ) external view returns (uint256);

    /**
     * @dev Calculates the current supply interest rate per block
     * @param cash The total amount of cash the market has
     * @param borrows The total amount of borrows the market has outstanding
     * @param reserves The total amnount of reserves the market has
     * @param reserveFactorMantissa The current reserve factor the market has
     * @return The supply rate per block (as a percentage, and scaled by 1e18)
     */
    function getSupplyRate(
        uint256 cash,
        uint256 borrows,
        uint256 reserves,
        uint256 reserveFactorMantissa
    ) external view returns (uint256);
}

// Part: OpenZeppelin/openzeppelin-contracts@3.1.0/Address

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != accountHash && codehash != 0x0);
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: weiValue }(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// Part: OpenZeppelin/openzeppelin-contracts@3.1.0/Context

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

// Part: OpenZeppelin/openzeppelin-contracts@3.1.0/IERC20

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

// Part: OpenZeppelin/openzeppelin-contracts@3.1.0/Math

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a >= b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow, so we distribute
        return (a / 2) + (b / 2) + ((a % 2 + b % 2) / 2);
    }
}

// Part: OpenZeppelin/openzeppelin-contracts@3.1.0/ReentrancyGuard

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor () internal {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and make it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        // On the first call to nonReentrant, _notEntered will be true
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;

        _;

        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }
}

// Part: OpenZeppelin/openzeppelin-contracts@3.1.0/SafeMath

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

// Part: SpiritFarm

interface SpiritFarm {
    function pendingSpirit(uint256 _pid, address _user)
        external
        view
        returns (uint256);
}

// Part: UnitrollerAdminStorage

interface UnitrollerAdminStorage {
    /**
    * @notice Administrator for this contract
    */
    // address external admin;
    function admin() external view returns (address);

    /**
    * @notice Pending administrator for this contract
    */
    // address external pendingAdmin;
    function pendingAdmin() external view returns (address);

    /**
    * @notice Active brains of Unitroller
    */
    // address external comptrollerImplementation;
    function comptrollerImplementation() external view returns (address);

    /**
    * @notice Pending brains of Unitroller
    */
    // address external pendingComptrollerImplementation;
    function pendingComptrollerImplementation() external view returns (address);
}

// Part: ComptrollerV1Storage

interface ComptrollerV1Storage is UnitrollerAdminStorage {

    /**
     * @notice Oracle which gives the price of any given asset
     */
    // PriceOracle external oracle;
    function oracle() external view returns (address);

    /**
     * @notice Multiplier used to calculate the maximum repayAmount when liquidating a borrow
     */
    // uint external closeFactorMantissa;
    function closeFactorMantissa() external view returns (uint);

    /**
     * @notice Multiplier representing the discount on collateral that a liquidator receives
     */
    // uint external liquidationIncentiveMantissa;
    function liquidationIncentiveMantissa() external view returns (uint);

    /**
     * @notice Max number of assets a single account can participate in (borrow or use as collateral)
     */
    // uint external maxAssets;
    function maxAssets() external view returns (uint);

    /**
     * @notice Per-account mapping of "assets you are in", capped by maxAssets
     */
    // mapping(address => CToken[]) external accountAssets;
    // function accountAssets(address) external view returns (CToken[]);

}

// Part: ICToken

interface ICToken is ICTokenStorage {
    /*** Market Events ***/

    /**
     * @dev Event emitted when interest is accrued
     */
    event AccrueInterest(
        uint256 cashPrior,
        uint256 interestAccumulated,
        uint256 borrowIndex,
        uint256 totalBorrows
    );

    /**
     * @dev Event emitted when tokens are minted
     */
    event Mint(address minter, uint256 mintAmount, uint256 mintTokens);

    /**
     * @dev Event emitted when tokens are redeemed
     */
    event Redeem(address redeemer, uint256 redeemAmount, uint256 redeemTokens);

    /**
     * @dev Event emitted when underlying is borrowed
     */
    event Borrow(
        address borrower,
        uint256 borrowAmount,
        uint256 accountBorrows,
        uint256 totalBorrows
    );

    /**
     * @dev Event emitted when a borrow is repaid
     */
    event RepayBorrow(
        address payer,
        address borrower,
        uint256 repayAmount,
        uint256 accountBorrows,
        uint256 totalBorrows
    );

    /**
     * @dev Event emitted when a borrow is liquidated
     */
    event LiquidateBorrow(
        address liquidator,
        address borrower,
        uint256 repayAmount,
        address cTokenCollateral,
        uint256 seizeTokens
    );

    /*** Admin Events ***/

    /**
     * @dev Event emitted when pendingAdmin is changed
     */
    event NewPendingAdmin(address oldPendingAdmin, address newPendingAdmin);

    /**
     * @dev Event emitted when pendingAdmin is accepted, which means admin is updated
     */
    event NewAdmin(address oldAdmin, address newAdmin);

    /**
     * @dev Event emitted when comptroller is changed
     */
    event NewComptroller(
        IComptroller oldComptroller,
        IComptroller newComptroller
    );

    /**
     * @dev Event emitted when interestRateModel is changed
     */
    event NewMarketInterestRateModel(
        InterestRateModel oldInterestRateModel,
        InterestRateModel newInterestRateModel
    );

    /**
     * @dev Event emitted when the reserve factor is changed
     */
    event NewReserveFactor(
        uint256 oldReserveFactorMantissa,
        uint256 newReserveFactorMantissa
    );

    /**
     * @dev Event emitted when the reserves are added
     */
    event ReservesAdded(
        address benefactor,
        uint256 addAmount,
        uint256 newTotalReserves
    );

    /**
     * @dev Event emitted when the reserves are reduced
     */
    event ReservesReduced(
        address admin,
        uint256 reduceAmount,
        uint256 newTotalReserves
    );

    /**
     * @dev EIP20 Transfer event
     */
    event Transfer(address indexed from, address indexed to, uint256 amount);

    /**
     * @dev EIP20 Approval event
     */
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 amount
    );

    /**
     * @dev Failure event
     */
    event Failure(uint256 error, uint256 info, uint256 detail);

    /*** User Interface ***/
    function totalBorrows() external view returns (uint256);

    function totalReserves() external view returns (uint256);
    
    function totalSupply() external view returns (uint256);

    function transfer(address dst, uint256 amount) external returns (bool);

    function transferFrom(
        address src,
        address dst,
        uint256 amount
    ) external returns (bool);

    function approve(address spender, uint256 amount) external returns (bool);

    function allowance(address owner, address spender)
        external
        view
        returns (uint256);

    function balanceOf(address owner) external view returns (uint256);

    function balanceOfUnderlying(address owner) external returns (uint256);

    function getAccountSnapshot(address account)
        external
        view
        returns (
            uint256,
            uint256,
            uint256,
            uint256
        );

    function borrowRatePerBlock() external view returns (uint256);

    function supplyRatePerBlock() external view returns (uint256);

    function totalBorrowsCurrent() external returns (uint256);

    function borrowBalanceCurrent(address account) external returns (uint256);

    function borrowBalanceStored(address account)
        external
        view
        returns (uint256);

    function exchangeRateCurrent() external returns (uint256);

    function exchangeRateStored() external view returns (uint256);

    function getCash() external view returns (uint256);

    function accrueInterest() external returns (uint256);

    function seize(
        address liquidator,
        address borrower,
        uint256 seizeTokens
    ) external returns (uint256);

    /*** CCap Interface ***/

    function totalCollateralTokens() external view returns (uint256);

    function accountCollateralTokens(address account)
        external
        view
        returns (uint256);

    function isCollateralTokenInit(address account)
        external
        view
        returns (bool);

    function collateralCap() external view returns (uint256);

    /*** Admin Functions ***/

    function _setPendingAdmin(address payable newPendingAdmin)
        external
        returns (uint256);

    function _acceptAdmin() external returns (uint256);

    function _setComptroller(IComptroller newComptroller)
        external
        returns (uint256);

    function _setReserveFactor(uint256 newReserveFactorMantissa)
        external
        returns (uint256);

    function _reduceReserves(uint256 reduceAmount) external returns (uint256);

    function _setInterestRateModel(InterestRateModel newInterestRateModel)
        external
        returns (uint256);
}

// Part: OpenZeppelin/openzeppelin-contracts@3.1.0/ERC20

/**
 * @dev Implementation of the {IERC20} interface.
 *
 * This implementation is agnostic to the way tokens are created. This means
 * that a supply mechanism has to be added in a derived contract using {_mint}.
 * For a generic mechanism see {ERC20PresetMinterPauser}.
 *
 * TIP: For a detailed writeup see our guide
 * https://forum.zeppelin.solutions/t/how-to-implement-erc20-supply-mechanisms/226[How
 * to implement supply mechanisms].
 *
 * We have followed general OpenZeppelin guidelines: functions revert instead
 * of returning `false` on failure. This behavior is nonetheless conventional
 * and does not conflict with the expectations of ERC20 applications.
 *
 * Additionally, an {Approval} event is emitted on calls to {transferFrom}.
 * This allows applications to reconstruct the allowance for all accounts just
 * by listening to said events. Other implementations of the EIP may not emit
 * these events, as it isn't required by the specification.
 *
 * Finally, the non-standard {decreaseAllowance} and {increaseAllowance}
 * functions have been added to mitigate the well-known issues around setting
 * allowances. See {IERC20-approve}.
 */
contract ERC20 is Context, IERC20 {
    using SafeMath for uint256;
    using Address for address;

    mapping (address => uint256) private _balances;

    mapping (address => mapping (address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;
    uint8 private _decimals;

    /**
     * @dev Sets the values for {name} and {symbol}, initializes {decimals} with
     * a default value of 18.
     *
     * To select a different value for {decimals}, use {_setupDecimals}.
     *
     * All three of these values are immutable: they can only be set once during
     * construction.
     */
    constructor (string memory name, string memory symbol) public {
        _name = name;
        _symbol = symbol;
        _decimals = 18;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5,05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless {_setupDecimals} is
     * called.
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view returns (uint8) {
        return _decimals;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account) public view override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `recipient` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address recipient, uint256 amount) public virtual override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20};
     *
     * Requirements:
     * - `sender` and `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     * - the caller must have allowance for ``sender``'s tokens of at least
     * `amount`.
     */
    function transferFrom(address sender, address recipient, uint256 amount) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "ERC20: transfer amount exceeds allowance"));
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue, "ERC20: decreased allowance below zero"));
        return true;
    }

    /**
     * @dev Moves tokens `amount` from `sender` to `recipient`.
     *
     * This is internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `sender` cannot be the zero address.
     * - `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     */
    function _transfer(address sender, address recipient, uint256 amount) internal virtual {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(sender, recipient, amount);

        _balances[sender] = _balances[sender].sub(amount, "ERC20: transfer amount exceeds balance");
        _balances[recipient] = _balances[recipient].add(amount);
        emit Transfer(sender, recipient, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements
     *
     * - `to` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply = _totalSupply.add(amount);
        _balances[account] = _balances[account].add(amount);
        emit Transfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        _balances[account] = _balances[account].sub(amount, "ERC20: burn amount exceeds balance");
        _totalSupply = _totalSupply.sub(amount);
        emit Transfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner`s tokens.
     *
     * This is internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(address owner, address spender, uint256 amount) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Sets {decimals} to a value other than the default one of 18.
     *
     * WARNING: This function should only be called from the constructor. Most
     * applications that interact with token contracts will not expect
     * {decimals} to ever change, and may work incorrectly if it does.
     */
    function _setupDecimals(uint8 decimals_) internal {
        _decimals = decimals_;
    }

    /**
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be to transferred to `to`.
     * - when `from` is zero, `amount` tokens will be minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(address from, address to, uint256 amount) internal virtual { }
}

// Part: OpenZeppelin/openzeppelin-contracts@3.1.0/SafeERC20

/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

// Part: BaseStrategy

/********************
 *
 *   RoboVault: BaseStrategy
 *   v0.1.1
 *
 *   This is inherited by RoboVault strategies. It contains the common want
 *   functions of all the strategies.
 *
 *   Credit: Yearn Finance - The source of much inspiritation for BaseStrategy.sol
 *   https://github.com/yearn/yearn-vaults
 *
 ********************* */
abstract contract BaseStrategy is ERC20, ReentrancyGuard {
    using SafeERC20 for IERC20;
    using SafeMath for uint256;

    // Roles (with defaults)
    address public governance;
    address public strategist = 0xD074CDae76496d81Fab83023fee4d8631898bBAf;
    address public keeper;
    address public rewards;

    uint256 constant BPS_ADJUST = 10000; // BPS constant used when calculating percentages
    uint256 constant SHARE_DECIMALS = 1e18;

    // Configuration
    uint256 public withdrawalFee = 50; // 0.5% default - only applies when funds are removed from strat & not reserves
    uint256 public operationalFee = 0; // 0% default
    uint256 public profitFee = 1000; // 10% default
    uint256 public reserveAllocation = 500; // 5%
    uint256 public sharePriceTracker = SHARE_DECIMALS;
    uint256 constant profitFeeGovernance = 5000; // 50% to gov, 50% to rewards

    // upper limit for fees so owner cannot maliciously increase fees
    uint256 constant operationalFeeLimit = 500; // 5% limit
    uint256 constant profitFeeLimit = 2000; // 20% limit
    uint256 constant withdrawalFeeLimit = 50; // 0.5% limit
    uint256 constant reserveAllocationLimit = 1000; // 10%

    // Vault limits
    uint256 public accountDepositLimit = uint256(-1); // max deposit per account
    uint256 public vaultTvlLimit = uint256(-1); // max vault TVL. if this is reached, deposits will fail.

    IERC20 public want;

    event UpdatedGovernance(address newStrategist);
    event UpdatedStrategist(address newStrategist);
    event UpdatedKeeper(address newKeeper);
    event UpdatedRewards(address rewards);
    event UpdatedMinReportDelay(uint256 delay);
    event UpdatedMaxReportDelay(uint256 delay);
    event Harvested(
        uint256 harvested,
        uint256 profitFeeTaken,
        uint256 operationalFeeTaken
    );
    event UpdatedProfitFactor(uint256 profitFactor);
    event Deposit(address addr, uint256 want, uint256 shares);
    event Withdrawal(address addr, uint256 want, uint256 shares, uint256 fee);

    // The minimum number of seconds between harvest calls. See
    // `setMinReportDelay()` for more details.
    uint256 public minReportDelay = 0;

    // The maximum number of seconds between harvest calls. See
    // `setMaxReportDelay()` for more details.
    uint256 public maxReportDelay = 86400; // ~ once a day

    // The minimum multiple that `callCost` must be above the credit/profit to
    // be "justifiable". See `setProfitFactor()` for more details.
    uint256 public profitFactor = 100;

    // Stores the timestamp of the last harvest
    uint256 public lastHarvest = block.timestamp;

    modifier onlyGovernance() {
        require(msg.sender == governance);
        _;
    }

    // modifiers
    modifier onlyAuthorized() {
        require(msg.sender == strategist || msg.sender == governance);
        _;
    }

    modifier onlyStrategist() {
        require(msg.sender == strategist);
        _;
    }

    modifier onlyKeepers() {
        require(
            msg.sender == keeper ||
            msg.sender == strategist ||
            msg.sender == governance
        );
        _;
    }

    constructor(
        string memory _name,
        string memory _symbol,
        address _want
    ) public ERC20(_name, _symbol) {
        governance = msg.sender;
        want = IERC20(_want);
        lastHarvest = block.timestamp;
    }

    /**
     * @notice
     *  Used to change `governance`.
     *
     *  This may only be called by governance or the existing governance.
     * @param _governance The new address to assign as `governance`.
     */
    function setGovernance(address _governance) external onlyGovernance {
        require(_governance != address(0));
        governance = _governance;
        emit UpdatedGovernance(_governance);
    }

    /**
     * @notice
     *  Used to change `strategist`.
     *
     *  This may only be called by governance or the existing strategist.
     * @param _strategist The new address to assign as `strategist`.
     *
     *  This is the address that controls receives fees + can complete rebalancing and update strategy thresholds
     *  strategist can also exit leveraged position i.e. withdraw all pooled LP and repay outstanding debt moving vault funds to reserves
     */
    function setStrategist(address _strategist) external onlyAuthorized {
        require(_strategist != address(0));
        strategist = _strategist;
        emit UpdatedStrategist(_strategist);
    }

    /**
     * @notice
     *  Used to change `keeper`.
     *
     *  `keeper` is the only address that may call `tend()` or `harvest()`,
     *  other than `governance()` or `strategist`. However, unlike
     *  `governance()` or `strategist`, `keeper` may *only* call `tend()`
     *  and `harvest()`, and no other authorized functions, following the
     *  principle of least privilege.
     *
     *  This may only be called by governance or the strategist.
     * @param _keeper The new address to assign as `keeper`.
     */
    function setKeeper(address _keeper) external onlyAuthorized {
        require(_keeper != address(0));
        keeper = _keeper;
        emit UpdatedKeeper(_keeper);
    }

    /**
     * @notice
     *  Used to change `rewards`. EOA or smart contract which has the permission
     *  to pull rewards from the vault.
     *
     *  This may only be called by the strategist.
     * @param _rewards The address to use for pulling rewards.
     */
    function setRewards(address _rewards) external onlyStrategist {
        require(_rewards != address(0));
        rewards = _rewards;
        emit UpdatedRewards(_rewards);
    }

    /**
     * @notice
     *  Provide an accurate estimate for the total amount of assets
     *  (principle + return) that this Strategy is currently managing,
     *  denominated in terms of `want` tokens.
     *
     *  This total should be "realizable" e.g. the total value that could
     *  *actually* be obtained from this Strategy if it were to divest its
     *  entire position wantd on current on-chain conditions.
     * @dev
     *  Care must be taken in using this function, since it relies on external
     *  systems, which could be manipulated by the attacker to give an inflated
     *  (or reduced) value produced by this function, wantd on current on-chain
     *  conditions (e.g. this function is possible to influence through
     *  flashloan attacks, oracle manipulations, or other DeFi attack
     *  mechanisms).
     *
     * @return The estimated total assets in this Strategy.
     */
    function estimatedTotalAssets() public view virtual returns (uint256);

    /**
     * @notice
     *  Used to change `minReportDelay`. `minReportDelay` is the minimum number
     *  of blocks that should pass for `harvest()` to be called.
     *
     *  For external keepers (such as the Keep3r network), this is the minimum
     *  time between jobs to wait. (see `harvestTrigger()`
     *  for more details.)
     *
     *  This may only be called by governance or the strategist.
     * @param _delay The minimum number of seconds to wait between harvests.
     */
    function setMinReportDelay(uint256 _delay) external onlyAuthorized {
        minReportDelay = _delay;
        emit UpdatedMinReportDelay(_delay);
    }

    /**
     * @notice
     *  Used to change `maxReportDelay`. `maxReportDelay` is the maximum number
     *  of blocks that should pass for `harvest()` to be called.
     *
     *  For external keepers (such as the Keep3r network), this is the maximum
     *  time between jobs to wait. (see `harvestTrigger()`
     *  for more details.)
     *
     *  This may only be called by governance or the strategist.
     * @param _delay The maximum number of seconds to wait between harvests.
     */
    function setMaxReportDelay(uint256 _delay) external onlyAuthorized {
        maxReportDelay = _delay;
        emit UpdatedMaxReportDelay(_delay);
    }

    /**
     * @notice
     *  Used to change `profitFactor`. `profitFactor` is used to determine
     *  if it's worthwhile to harvest, given gas costs. (See `harvestTrigger()`
     *  for more details.)
     *
     *  This may only be called by governance or the strategist.
     * @param _profitFactor A ratio to multiply anticipated
     * `harvest()` gas cost against.
     */
    function setProfitFactor(uint256 _profitFactor) external onlyAuthorized {
        profitFactor = _profitFactor;
        emit UpdatedProfitFactor(_profitFactor);
    }

    /**
     * Perform any adjustments to the core position(s) of this Strategy given
     * what change the Vault made in the "investable capital" available to the
     * Strategy. Note that all "free capital" in the Strategy after the report
     * was made is available for reinvestment. Also note that this number
     * could be 0, and you should handle that scenario accordingly.
     *
     * See comments regarding `_debtOutstanding` on `prepareReturn()`.
     */
    // function adjustPosition(uint256 _debtOutstanding) internal virtual;

    /**
     * Liquidate up to `_amountNeeded` of `want` of this strategy's positions,
     * irregardless of slippage. Any excess will be re-invested with `adjustPosition()`.
     * This function should return the amount of `want` tokens made available by the
     * liquidation. If there is a difference between them, `_loss` indicates whether the
     * difference is due to a realized loss, or if there is some other sitution at play
     * (e.g. locked funds) where the amount made available is less than what is needed.
     * This function is used during emergency exit instead of `prepareReturn()` to
     * liquidate all of the Strategy's positions back to the Vault.
     *
     * NOTE: The invariant `_liquidatedAmount + _loss <= _amountNeeded` should always be maintained
     */
    function _liquidatePosition(uint256 _amountNeeded)
        internal
        virtual
        returns (uint256 _liquidatedAmount, uint256 _loss);

    /**
     * @notice
     *  Returns the approximate value in want the pending harvest would
     *  bring
     */
    function balancePendingHarvest() public view virtual returns (uint256);

    /**
     * @notice
     *  Provide a signal to the keeper that `harvest()` should be called. The
     *  keeper will provide the estimated gas cost that they would pay to call
     *  `harvest()`, and this function should use that estimate to make a
     *  determination if calling it is "worth it" for the keeper. This is not
     *  the only consideration into issuing this trigger, for example if the
     *  position would be negatively affected if `harvest()` is not called
     *  shortly, then this can return `true` even if the keeper might be "at a
     *  loss" (keepers are always reimbursed by RoboVault).
     * @dev
     *  `callCost` must be priced in terms of `want`.
     *
     *  This call and `tendTrigger` should never return `true` at the
     *  same time.
     *
     *  See `min/maxReportDelay`, `profitFactor`, `debtThreshold` to adjust the
     *  strategist-controlled parameters that will influence whether this call
     *  returns `true` or not. These parameters will be used in conjunction
     *  with the parameters reported to the Vault (see `params`) to determine
     *  if calling `harvest()` is merited.
     *
     * @param callCost The keeper's estimated cast cost to call `harvest()`.
     * @return `true` if `harvest()` should be called, `false` otherwise.
     */
    function harvestTrigger(uint256 callCost)
        external
        view
        virtual
        returns (bool)
    {
        // Should not trigger if we haven't waited long enough since previous harvest
        if (block.timestamp.sub(lastHarvest) < minReportDelay) return false;

        // Should trigger if hasn't been called in a while
        if (block.timestamp.sub(lastHarvest) >= maxReportDelay) return true;

        return (profitFactor.mul(callCost) < balancePendingHarvest());
    }

    /**
     * @notice
     *  Harvests the Strategy, recognizing any profits or losses and adjusting
     *  the Strategy's position.
     *
     *  In the rare case the Strategy is in emergency shutdown, this will exit
     *  the Strategy's position.
     *
     *  This may only be called by governance, the strategist, or the keeper.
     * @dev
     *  When `harvest()` is called, the Strategy reports to the Vault (via
     *  `vault.report()`), so in some cases `harvest()` must be called in order
     *  to take in profits, to borrow newly available funds from the Vault, or
     *  otherwise adjust its position. In other cases `harvest()` must be
     *  called to report to the Vault on the Strategy's position, especially if
     *  any losses have occurred.
     */
    function harvest() external onlyKeepers {
        // harvest
        uint256 harvested = _harvestInternal();

        // Take fees
        (uint256 pFee, uint256 oFee) = takeFees();

        // Update harvest timestamp - used for fee calculations
        lastHarvest = block.timestamp;

        emit Harvested(harvested, pFee, oFee);
    }

    /**
     * Virtual function for triggering a harvest
     *
     * Returns
     * want harvested in harvest
     */
    function _harvestInternal()
        internal
        virtual
        returns (uint256 _wantHarvested);

    /**
     * @notice
     *  Returns the share price of the strategy in `want` units, multiplied
     *  by 1e18
     */
    function getPricePerShare() public view returns (uint256) {
        uint256 bal = estimatedTotalAssets();
        uint256 supply = totalSupply();
        return bal.mul(1e18).div(supply);
    }

    /**
     * @notice
     *  Takes the fees from the vault and distributes it to goverenance and
     *  the strategists selected `rewards` address.
     *   - Fees are issued as minted shares.
     *   - Fees are split 50/50 Strategist/Governance
     *
     *  Profit Fee:
     *  A percentage fee take on profits.
     *
     *  Operational Fee:
     *  The operational fee is a percentage of TVL taken incrementally each harvest
     *  over 365 days.
     */
    function takeFees()
        internal
        returns (uint256 _profitFeeMinted, uint256 _operationFeeMinted)
    {
        // Profit Fee: Takes profitFee of profits
        _profitFeeMinted = 0;
        _operationFeeMinted = 0;
        uint256 pricePerShare = getPricePerShare();
        if (pricePerShare > sharePriceTracker) {
            uint256 profitPerShare = (pricePerShare.sub(sharePriceTracker));
            uint256 profitPercent = profitPerShare.mul(SHARE_DECIMALS).div(sharePriceTracker);
            _profitFeeMinted = totalSupply()
                .mul(profitPercent)
                .mul(profitFee)
                .div(BPS_ADJUST)
                .div(SHARE_DECIMALS);
            uint256 profitFeeGov =
                _profitFeeMinted.mul(profitFeeGovernance).div(BPS_ADJUST);
            uint256 profitFeeStrat = _profitFeeMinted.sub(profitFeeGov);
            _mint(rewards, profitFeeStrat);
            _mint(governance, profitFeeGov);
            sharePriceTracker = pricePerShare;
        }

        if (operationalFee != 0) {            
            // take operational fee
            uint256 timeSinceHarvest = (block.timestamp).sub(lastHarvest);
            uint256 annualAdj = uint256(365).mul(24).mul(60).mul(60);
            _operationFeeMinted = operationalFee
                    .mul(timeSinceHarvest)
                    .mul(totalSupply())
                    .div(BPS_ADJUST)
                    .div(annualAdj);
            _mint(governance, _operationFeeMinted);
        }
    }

    /**
     * @notice
     *  Burns `_shares` and returns the equilent about of want back to sender
     *
     *  This may only be called by the Vault.
     * @param _shares How much `want` to withdraw.
     * @return _loss Any realized losses
     */
    function withdraw(uint256 _shares) public returns (uint256 _loss) {
        require(_shares > 0);

        uint256 ibalance = balanceOf(msg.sender);
        require(_shares <= ibalance);

        uint256 total = estimatedTotalAssets();
        // Calc to redeem before updating balances
        uint256 redeem = (total.mul(_shares)).div(totalSupply());
        _burn(msg.sender, _shares);

        // Check balance
        uint256 reserves = want.balanceOf(address(this));
        uint256 fee = 0;
        if (redeem > reserves) {
            // take withdrawal fee for the portion being removed from strat
            fee = (redeem - reserves).mul(withdrawalFee).div(BPS_ADJUST);
            redeem = redeem.sub(fee);
            _liquidatePosition(redeem);
        }

        // Redeem want to sender
        want.safeTransfer(msg.sender, redeem);
        emit Withdrawal(msg.sender, redeem, _shares, fee);
    }

    /**
     * @notice
     *  Desposits `_amount` of users want balance into the vault
     */
    function deposit(uint256 _amount) public nonReentrant {
        require(_amount > 0);
        require(_amount <= accountDepositLimit);

        // Additional checks from te strategy on deposits
        checkDeposit(_amount);

        uint256 pool = estimatedTotalAssets();

        // Check the vault hasn't reached its limit
        require(pool.add(_amount) <= vaultTvlLimit);

        // Access want deposit
        want.transferFrom(msg.sender, address(this), _amount);

        // Calculate pool shares and mint for the user.
        uint256 shares = 0;
        if (totalSupply() == 0) {
            shares = _amount;
        } else {
            uint256 currentBalance =
                (pool.mul(balanceOf(msg.sender)).div(totalSupply()));
            require(

                _amount.add(currentBalance) <= accountDepositLimit
            );
            shares = (_amount.mul(totalSupply())).div(pool);
        }
        _mint(msg.sender, shares);
        emit Deposit(msg.sender, _amount, shares);
    }

    /**
     * @notice
     *  Implemented by the strategy. Checks if the strategy can access more deposits
     */
    function checkDeposit(uint256 _amount) public virtual returns (bool);

    /**
     * @notice
     *  Desposits all of users want balance into the vault
     */
    function depositAll() external {
        deposit(want.balanceOf(msg.sender));
    }

    /**
     * @notice
     *  Desposits all of users vault tokens
     */
    function withdrawAll() external {
        withdraw(balanceOf(msg.sender));
    }

    /**
     * Sets the fees of the vault
     *
     * @param _withdrawalFee fee taken from withdrawals greater than reserves
     * @param _operationalFee percentage of holdings taken annually, incrementally
     * @param _profitFee percentage fee of profits made
     */
    function setFees(
        uint256 _withdrawalFee,
        uint256 _operationalFee,
        uint256 _profitFee
    ) external onlyAuthorized {
        require(_withdrawalFee <= withdrawalFeeLimit);
        require(_operationalFee <= operationalFeeLimit);
        require(_profitFee <= profitFeeLimit);

        operationalFee = _operationalFee;
        profitFee = _profitFee;
        withdrawalFee = _withdrawalFee;
    }

    /**
     * Sets the accountDepositLimit and vaultTvlLimit for the vault
     *
     * @param _accountDepositLimit The max any indivdual account can hold before deposits from that account fail
     * @param _vaultTvlLimit The max the vault value can grow before deposits from any account fail
     */
    function setLimits(uint256 _accountDepositLimit, uint256 _vaultTvlLimit)
        external
        onlyAuthorized
    {
        accountDepositLimit = _accountDepositLimit;
        vaultTvlLimit = _vaultTvlLimit;
    }

    /**
     * Override this to add all tokens/tokenized positions this contract
     * manages on a *persistent* basis (e.g. not just for swapping back to
     * want ephemerally).
     *
     * NOTE: Do *not* include `want`, already included in `sweep` below.
     *
     * Example:
     *
     *    function protectedTokens() internal override view returns (address[] memory) {
     *      address[] memory protected = new address[](3);
     *      protected[0] = tokenA;
     *      protected[1] = tokenB;
     *      protected[2] = tokenC;
     *      return protected;
     *    }
     */
    function _protectedTokens()
        internal
        view
        virtual
        returns (address[] memory);

    /**
     * @notice
     *  Removes tokens from this Strategy that are not the type of tokens
     *  managed by this Strategy. This may be used in case of accidentally
     *  sending the wrong kind of token to this Strategy.
     *
     *  Tokens will be sent to `governance()`.
     *
     *  This will fail if an attempt is made to sweep `want`, or any tokens
     *  that are protected by this Strategy.
     *
     *  This may only be called by governance.
     * @dev
     *  Implement `protectedTokens()` to specify any additional tokens that
     *  should be protected from sweeping in addition to `want`.
     * @param _token The token to transfer out of this vault.
     */
    function sweep(address _token) external onlyGovernance {
        require(_token != address(want));
        require(_token != address(this));

        address[] memory protectedTokens = _protectedTokens();
        for (uint256 i; i < protectedTokens.length; i++)
            require(_token != protectedTokens[i]);

        IERC20(_token).safeTransfer(
            governance,
            IERC20(_token).balanceOf(address(this))
        );
    }
}

// Part: ComptrollerV2Storage

interface ComptrollerV2Storage is ComptrollerV1Storage {
    enum Version {
        VANILLA,
        COLLATERALCAP,
        WRAPPEDNATIVE
    }

    struct Market {
        bool isListed;
        uint collateralFactorMantissa;
        mapping(address => bool) accountMembership;
        bool isComped;
        Version version;
    }

    /**
     * @notice Official mapping of cTokens -> Market metadata
     * @dev Used e.g. to determine if a market is supported
     */
    // mapping(address => Market) external markets;
    // function markets(address) external view returns (Market);


    /**
     * @notice The Pause Guardian can pause certain actions as a safety mechanism.
     *  Actions which allow users to remove their own assets cannot be paused.
     *  Liquidation / seizing / transfer can only be paused globally, not by market.
     */
    // address external pauseGuardian;
    // bool external _mintGuardianPaused;
    // bool external _borrowGuardianPaused;
    // bool external transferGuardianPaused;
    // bool external seizeGuardianPaused;
    // mapping(address => bool) external mintGuardianPaused;
    // mapping(address => bool) external borrowGuardianPaused;
}

// Part: ICTokenErc20

interface ICTokenErc20 is ICToken {

    /*** User Interface ***/

    function mint(uint256 mintAmount) external returns (uint256);

    function redeem(uint256 redeemTokens) external returns (uint256);

    function redeemUnderlying(uint256 redeemAmount) external returns (uint256);

    function borrow(uint256 borrowAmount) external returns (uint256);

    function repayBorrow(uint256 repayAmount) external returns (uint256);

    function liquidateBorrow(
        address borrower,
        uint256 repayAmount,
        ICToken cTokenCollateral
    ) external returns (uint256);

    /*** Admin Functions ***/

    function _addReserves(uint256 addAmount) external returns (uint256);
}

// Part: ComptrollerV3Storage

interface ComptrollerV3Storage is ComptrollerV2Storage {
    // struct CompMarketState {
    //     /// @notice The market's last updated compBorrowIndex or compSupplyIndex
    //     uint224 index;

    //     /// @notice The block number the index was last updated at
    //     uint32 block;
    // }

    // /// @notice A list of all markets
    // CToken[] external allMarkets;

    // /// @notice The rate at which the flywheel distributes COMP, per block
    // uint external compRate;

    // /// @notice The portion of compRate that each market currently receives
    // mapping(address => uint) external compSpeeds;

    // /// @notice The COMP market supply state for each market
    // mapping(address => CompMarketState) external compSupplyState;

    // /// @notice The COMP market borrow state for each market
    // mapping(address => CompMarketState) external compBorrowState;

    // /// @notice The COMP borrow index for each market for each supplier as of the last time they accrued COMP
    // mapping(address => mapping(address => uint)) external compSupplierIndex;

    // /// @notice The COMP borrow index for each market for each borrower as of the last time they accrued COMP
    // mapping(address => mapping(address => uint)) external compBorrowerIndex;

    // /// @notice The COMP accrued but not yet transferred to each user
    // mapping(address => uint) external compAccrued;
}

// Part: HedgedFarmingVault

/********************
 *
 *   RoboVault: A Single Assset Hedge Farming Strategy
 *   v0.1.1
 *
 *   This stragegy works by lending deposited capital into a lending platform,
 *   borrow a 'short' token against it and minting want-want LP for farming.
 *   Debt and Collateral is balanced by keepers.
 *
 ********************* */
abstract contract HedgedFarmingVault is BaseStrategy {
    using SafeERC20 for IERC20;
    using SafeMath for uint256;

    SingleAssetHedgeFarmingConfig config;

    // ERC20 Tokens;
    IERC20 public short;
    IERC20 wantShortLP;
    IERC20 harvestTokenLP;
    IERC20 harvestToken;
    IERC20 compToken;

    // Contract Interfaces
    ICTokenErc20 cTokenLend;
    ICTokenErc20 cTokenBorrow;
    IFarmMasterChef farm;
    IUniswapV2Router01 public router;
    IComptroller comptroller;
    IPriceOracle oracle;
    // address paths;

    uint256 public slippageAdj = 9900; // 99%
    uint256 public slippageAdjHigh = 10100; // 101%

    constructor(
        string memory name,
        string memory symbol,
        SingleAssetHedgeFarmingConfig memory _config
    ) public BaseStrategy(name, symbol, _config.want) {
        config = _config;

        // initialise token interfaces
        short = IERC20(_config.short);
        wantShortLP = IERC20(config.wantShortLP);
        harvestTokenLP = IERC20(config.farmTokenLp);
        harvestToken = IERC20(config.farmToken);
        compToken = IERC20(config.compToken);

        // initialise other interfaces
        cTokenLend = ICTokenErc20(config.cTokenLend);
        cTokenBorrow = ICTokenErc20(config.cTokenBorrow);
        farm = IFarmMasterChef(config.farmMasterChef);
        router = IUniswapV2Router01(config.router);
        comptroller = IComptroller(config.comptroller);
    }

    function enterMarket() external onlyAuthorized {
        address[] memory cTokens = new address[](1);
        cTokens[0] = config.cTokenLend;
        comptroller.enterMarkets(cTokens);
    }

    function exitMarket() external onlyAuthorized {
        comptroller.exitMarket(config.cTokenLend);
    }

    /**
     * This method is often farm specific so it needs to be declared elsewhere.
     */
    function _farmPendingRewards(uint256 _pid, address _user)
        internal
        view
        virtual
        returns (uint256);

    // calculate total value of vault assets
    function estimatedTotalAssets() public view override returns (uint256) {
        uint256 lpvalue = balanceLp();
        uint256 collateral = balanceLend();
        uint256 reserves = balanceReserves();
        uint256 debt = balanceDebt();
        uint256 shortInWallet = balanceShortWantEq();
        uint256 pendingRewards = balancePendingHarvest();
        return
            reserves
                .add(collateral)
                .add(lpvalue)
                .add(shortInWallet)
                .add(pendingRewards)
                .sub(debt);
    }

    // debt ratio - used to trigger rebalancing of debt
    function calcDebtRatio() public view returns (uint256) {
        uint256 debt = balanceDebt();
        uint256 lpvalue = balanceLp();
        uint256 debtRatio = debt.mul(BPS_ADJUST).mul(2).div(lpvalue);
        return (debtRatio);
    }

    // calculate debt / collateral - used to trigger rebalancing of debt & collateral
    function calcCollateral() public view returns (uint256) {
        uint256 debt = balanceDebtOracle();
        uint256 collateral = balanceLendCollateral();
        uint256 collatRatio = debt.mul(BPS_ADJUST).div(collateral);
        return (collatRatio);
    }

    // current % of vault assets held in reserve - used to trigger deployment of assets into strategy
    function calcReserves() external view returns (uint256) {
        uint256 bal = want.balanceOf(address(this));
        uint256 totalBal = estimatedTotalAssets();
        uint256 reservesRatio = bal.mul(BPS_ADJUST).div(totalBal);
        return (reservesRatio);
    }

    function convertShortToWantLP(uint256 _amountShort)
        internal
        view
        returns (uint256)
    {
        uint256 shortLP = _getShortInLp();
        uint256 wantLP = getWantInLp();
        return (_amountShort.mul(wantLP).div(shortLP));
    }

    function convertShortToWantOracle(uint256 _amountShort)
        internal
        view
        returns (uint256)
    {
        return _amountShort.mul(oracle.getPrice()).div(1e18);
    }

    function convertWantToShortLP(uint256 _amountWant)
        internal
        view
        returns (uint256)
    {
        uint256 shortLP = _getShortInLp();
        uint256 wantLP = getWantInLp();
        return (_amountWant.mul(shortLP).div(wantLP));
    }

    /// get value of all LP in want currency
    function balanceLp() public view returns (uint256) {
        uint256 wantLP = getWantInLp();
        uint256 lpIssued = wantShortLP.totalSupply();
        uint256 lpPooled = countLpPooled();
        uint256 totalLP = lpPooled + wantShortLP.balanceOf(address(this));
        uint256 lpvalue = totalLP.mul(wantLP).mul(2).div(lpIssued);
        return (lpvalue);
    }

    // value of borrowed tokens in value of want tokens
    function balanceDebt() public view returns (uint256) {
        uint256 debt = cTokenBorrow.borrowBalanceStored(address(this));
        return (convertShortToWantLP(debt));
    }

    /**
     * Debt balance using price oracle
     */
    function balanceDebtOracle() public view returns (uint256) {
        uint256 debt = cTokenBorrow.borrowBalanceStored(address(this));
        return (convertShortToWantOracle(debt));
    }

    function balancePendingHarvest() public view virtual override returns (uint256) {
        uint256 rewardsPending = _farmPendingRewards(config.farmPid, address(this)).add(harvestToken.balanceOf(address(this)));
        uint256 harvestLP_A = _getHarvestInHarvestLp();
        uint256 shortLP_A = _getShortInHarvestLp();
        uint256 shortLP_B = _getShortInLp();
        uint256 wantLP_B = getWantInLp();
        uint256 balShort = rewardsPending.mul(shortLP_A).div(harvestLP_A);
        uint256 balRewards = balShort.mul(wantLP_B).div(shortLP_B);
        return (balRewards);
    }

    // reserves
    function balanceReserves() public view returns (uint256) {
        return (want.balanceOf(address(this)));
    }

    function balanceShort() public view returns (uint256) {
        return (short.balanceOf(address(this)));
    }

    function balanceShortWantEq() public view returns (uint256) {
        return (convertShortToWantLP(short.balanceOf(address(this))));
    }

    function balanceLend() public view returns (uint256) {
        uint256 b = cTokenLend.balanceOf(address(this));
        return (b.mul(cTokenLend.exchangeRateStored()).div(1e18));
    }

    function balanceLendCollateral() public view virtual returns (uint256) {
        uint256 b = cTokenLend.accountCollateralTokens(address(this));
        return (b.mul(cTokenLend.exchangeRateStored()).div(1e18));
    }

    function calcBorrowAllocation() internal view returns (uint256) {
        uint256 balLend = balanceLend();
        uint256 balLp = balanceLp();
        uint256 borrowAllocation =
            balLp.mul(BPS_ADJUST).div(balLend.add(balLp.div(2))).div(2);
        return (borrowAllocation);
    }

    function getWantInLending() internal view returns (uint256) {
        uint256 bal = want.balanceOf(address(cTokenLend));
        return (bal);
    }

    function getWantInLp() internal view returns (uint256) {
        uint256 want_lp = want.balanceOf(address(config.wantShortLP));
        return (want_lp);
    }

    function countLpPooled() internal view returns (uint256) {
        uint256 lpPooled = farm.userInfo(config.farmPid, address(this));
        return lpPooled;
    }

    function _getShortInLp() internal view returns (uint256) {
        uint256 short_lp = short.balanceOf(config.wantShortLP);
        return (short_lp);
    }

    // lend want tokens to lending platform
    function _lendWant(uint256 amount) internal {
        cTokenLend.mint(amount);
    }

    // borrow tokens woth _amount of want tokens
    function _borrowWantEq(uint256 _amount) internal returns (uint256) {
        uint256 borrowamount = convertWantToShortLP(_amount);
        _borrow(borrowamount);
        return (borrowamount);
    }

    function _borrow(uint256 borrowAmount) internal {
        cTokenBorrow.borrow(borrowAmount);
    }

    // automatically repays debt using any short tokens held in wallet up to total debt value
    function _repayDebt() internal {
        uint256 _bal = short.balanceOf(address(this));
        if (_bal == 0) return;

        uint256 _debt = cTokenBorrow.borrowBalanceStored(address(this));
        if (_bal < _debt) {
            cTokenBorrow.repayBorrow(_bal);
        } else {
            cTokenBorrow.repayBorrow(_debt);
        }
    }

    function _getHarvestInHarvestLp() internal view returns (uint256) {
        uint256 harvest_lp = harvestToken.balanceOf(config.farmTokenLp);
        return harvest_lp;
    }

    function _getShortInHarvestLp() internal view returns (uint256) {
        uint256 shortToken_lp = short.balanceOf(config.farmTokenLp);
        return shortToken_lp;
    }

    function _redeemWant(uint256 _redeem_amount) internal {
        cTokenLend.redeemUnderlying(_redeem_amount);
    }

    // withdraws some LP worth _amount, converts all withdrawn LP to short token to repay debt
    function _withdrawLpRebalance(uint256 _amount) internal returns (uint256 swapAmountWant, uint256 slippageWant) {
        uint256 lpUnpooled = wantShortLP.balanceOf(address(this));
        uint256 lpPooled = countLpPooled();
        uint256 lpCount = lpUnpooled.add(lpPooled);
        uint256 lpReq = _amount.mul(lpCount).div(balanceLp());
        uint256 lpWithdraw;
        if (lpReq - lpUnpooled < lpPooled) {
            lpWithdraw = lpReq - lpUnpooled;
        } else {
            lpWithdraw = lpPooled;
        }
        _withdrawSomeLp(lpWithdraw);
        _removeAllLp();
        swapAmountWant = Math.min(_amount.div(2), want.balanceOf(address(this)));
        slippageWant = _swapWantShort(swapAmountWant);

        _repayDebt();
    }

    //  withdraws some LP worth _amount, uses withdrawn LP to add to collateral & repay debt
    function _withdrawLpRebalanceCollateral(uint256 _amount) internal {
        uint256 lpUnpooled = wantShortLP.balanceOf(address(this));
        uint256 lpPooled = countLpPooled();
        uint256 lpCount = lpUnpooled.add(lpPooled);
        uint256 lpReq = _amount.mul(lpCount).div(balanceLp());
        uint256 lpWithdraw;
        if (lpReq - lpUnpooled < lpPooled) {
            lpWithdraw = lpReq - lpUnpooled;
        } else {
            lpWithdraw = lpPooled;
        }
        _withdrawSomeLp(lpWithdraw);
        _removeAllLp();

        if (_amount.div(2) <= want.balanceOf(address(this))) {
            _lendWant(_amount.div(2));
        } else {
            _lendWant(want.balanceOf(address(this)));
        }
        _repayDebt();
    }

    function _addToLpFull(
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin
    ) internal {
        router.addLiquidity(
            address(short),
            address(want),
            amountADesired,
            amountBDesired,
            amountAMin,
            amountBMin,
            address(this),
            now
        ); /// add liquidity
    }

    function _addToLP(uint256 _amountShort) internal {
        uint256 shortLP = _getShortInLp();
        uint256 wantLP = getWantInLp();
        uint256 _amountWant = _amountShort.mul(wantLP).div(shortLP);
        _addToLpFull(
            _amountShort,
            _amountWant,
            _amountShort.mul(slippageAdj).div(BPS_ADJUST),
            _amountWant.mul(slippageAdj).div(BPS_ADJUST)
        );
    }

    function _depoistLp() internal {
        uint256 lpBalance = wantShortLP.balanceOf(address(this)); /// get number of LP tokens
        farm.deposit(config.farmPid, lpBalance); /// deposit LP tokens to farm
    }

    function _withdrawSomeLp(uint256 _amount) internal {
        require(_amount <= countLpPooled());
        farm.withdraw(config.farmPid, _amount);
    }

    // all LP currently not in Farm is removed.
    function _removeAllLp() internal {
        uint256 _amount = wantShortLP.balanceOf(address(this));
        uint256 shortLP = _getShortInLp();
        uint256 wantLP = getWantInLp();
        uint256 lpIssued = wantShortLP.totalSupply();

        uint256 amountAMin =
            _amount.mul(shortLP).mul(slippageAdj).div(BPS_ADJUST).div(lpIssued);
        uint256 amountBMin =
            _amount.mul(wantLP).mul(slippageAdj).div(BPS_ADJUST).div(lpIssued);
        router.removeLiquidity(
            address(short),
            address(want),
            _amount,
            amountAMin,
            amountBMin,
            address(this),
            now
        );
    }

    function _withdrawAllPooled() internal {
        uint256 lpPooled = countLpPooled();
        farm.withdraw(config.farmPid, lpPooled);
    }

    function _pathFarmToWant()
        internal
        view
        virtual
        returns (address[] memory)
    {
        address[] memory pathWant = new address[](3);
        pathWant[0] = address(harvestToken);
        pathWant[1] = address(short);
        pathWant[2] = address(want);
        return pathWant;
    }

    // below functions interact with AMM converting Harvest Rewards & Swapping between want & short token as required for rebalancing
    function _sellHarvestWant() internal returns (uint256) {
        uint256 harvestBalance = harvestToken.balanceOf(address(this));
        uint256 harvestLP_A = _getHarvestInHarvestLp();
        uint256 shortLP_A = _getShortInHarvestLp();
        uint256 shortLP_B = _getShortInLp();
        uint256 wantLP_B = getWantInLp();

        uint256 amountOutMinamountOutShort =
            harvestBalance.mul(shortLP_A).div(harvestLP_A);
        uint256 amountOutMin =
            amountOutMinamountOutShort
                .mul(wantLP_B)
                .mul(slippageAdj)
                .div(BPS_ADJUST)
                .div(shortLP_B);
        router.swapExactTokensForTokens(
            harvestBalance,
            amountOutMin,
            _pathFarmToWant(),
            address(this),
            now
        );
        return (amountOutMin);
    }

    function _pathFarmToShort()
        internal
        view
        virtual
        returns (address[] memory)
    {
        address[] memory pathShort = new address[](2);
        pathShort[0] = address(harvestToken);
        pathShort[1] = address(short);
        return pathShort;
    }

    function _pathCompToShort()
        internal
        view
        virtual
        returns (address[] memory)
    {
        address[] memory pathShort = new address[](2);
        pathShort[0] = address(compToken);
        pathShort[1] = address(short);
        return pathShort;
    }

    function _sellHarvestShort() internal {
        uint256 harvestBalance = harvestToken.balanceOf(address(this));
        if (harvestBalance == 0) return;
        router.swapExactTokensForTokens(
            harvestBalance,
            0,
            _pathFarmToShort(),
            address(this),
            now
        );
    }

    /**
     * Harvest comp token from the lending platform and swap for the short token
     * Note: this is a virtual so it can be replaced as necessary. For example, cream has no
     * comp reward token so this needs to be nulled.
     */
    function _sellCompShort() internal virtual {
        uint256 compBalance = compToken.balanceOf(address(this));
        if (compBalance == 0) return;
        router.swapExactTokensForTokens(
            compBalance,
            0,
            _pathCompToShort(),
            address(this),
            now
        );
    }

    function _pathWantToShort()
        internal
        view
        virtual
        returns (address[] memory)
    {
        address[] memory pathSwap = new address[](2);
        pathSwap[0] = address(want);
        pathSwap[1] = address(short);
        return pathSwap;
    }

    function _pathShortToWant()
        internal
        view
        virtual
        returns (address[] memory)
    {
        address[] memory pathSwap = new address[](2);
        pathSwap[0] = address(short);
        pathSwap[1] = address(want);
        return pathSwap;
    }

    /**
     * @notice
     *  Swaps _amount of want for short
     *
     * @param _amount The amount of want to swap
     *
     * @return slippageWant Returns the cost of fees + slippage in want
     */
    function _swapWantShort(uint256 _amount) internal returns (uint256 slippageWant) {
        uint256 shortLP = _getShortInLp();
        uint256 wantLP = getWantInLp();
        uint256 amountOutMax = _amount.mul(shortLP).div(wantLP);
        uint256[] memory amounts = router.swapExactTokensForTokens(
            _amount,
            amountOutMax.mul(slippageAdj).div(BPS_ADJUST),
            _pathWantToShort(),
            address(this),
            now
        );
        slippageWant = amountOutMax.sub(amounts[amounts.length - 1]).mul(wantLP).div(shortLP);
    }

    /**
     * @notice
     *  Swaps _amount of short for want
     *
     * @param _amount The amount of short to swap
     *
     * @return amountWant Returns the want amount minus fees
     * @return slippageWant Returns the cost of fees + slippage in want
     */
    function _swapShortWant(uint256 _amount) internal returns (uint256 amountWant, uint256 slippageWant) {
        uint256 shortLP = _getShortInLp();
        uint256 wantLP = getWantInLp();
        amountWant = _amount.mul(wantLP).div(shortLP);
        uint256[] memory amounts = router.swapExactTokensForTokens(
            _amount,
            amountWant.mul(slippageAdj).div(BPS_ADJUST),
            _pathShortToWant(),
            address(this),
            now
        );
        slippageWant = amountWant.sub(amounts[amounts.length - 1]);
    }

    function _swapWantShortExact(uint256 _amountOut) internal {
        uint256 shortLP = _getShortInLp();
        uint256 wantLP = getWantInLp();
        uint256 amountInMax =
            _amountOut.mul(wantLP).mul(slippageAdjHigh).div(BPS_ADJUST).div(
                shortLP
            );
        router.swapExactTokensForTokens(
            _amountOut,
            amountInMax,
            _pathWantToShort(),
            address(this),
            now
        );
    }

    function _protectedTokens()
        internal
        view
        override
        returns (address[] memory)
    {
        address[] memory protected = new address[](7);
        protected[0] = address(short);
        protected[1] = address(wantShortLP);
        protected[2] = address(harvestToken);
        protected[3] = address(harvestTokenLP);
        protected[4] = address(compToken);
        protected[5] = address(cTokenLend);
        protected[6] = address(cTokenBorrow);
        return protected;
    }
}

// Part: ComptrollerV4Storage

interface ComptrollerV4Storage is ComptrollerV3Storage {
    // @notice The borrowCapGuardian can set borrowCaps to any number for any market. Lowering the borrow cap could disable borrowing on the given market.
    // address external borrowCapGuardian;
    function borrowCapGuardian() external view returns (address);

    // @notice Borrow caps enforced by borrowAllowed for each cToken address. Defaults to zero which corresponds to unlimited borrowing.
    // mapping(address => uint) external borrowCaps;
    function borrowCaps(address) external view returns (uint);
}

// Part: HedgedFarmingStrategy

/********************
 *
 *   RoboVault: A Single Assset Hedge Farming Strategy
 *   v0.1.1
 *
 *   This stragegy works by lending deposited capital into a lending platform,
 *   borrow a 'short' token against it and minting want-want LP for farming.
 *   Debt and Collateral is balanced by keepers.
 *
 ********************* */
abstract contract HedgedFarmingStrategy is HedgedFarmingVault {
    using SafeERC20 for IERC20;
    using SafeMath for uint256;


    event DebtRebalance(uint256 debtRatio, uint256 swapAmount, uint256 slippage);
    event CollatRebalance(uint256 collatRatio, uint256 adjAmount);

    uint256 public stratLendAllocation = 6250;
    uint256 public stratDebtAllocation = 3750;
    uint256 public collatUpper = 6700;
    uint256 public collatTarget = 6000;
    uint256 public collatLower = 5300;
    uint256 public debtUpper = 10200;
    uint256 public debtLower = 9800;
    uint256 constant largeWithdrawThreshold = 4000; // 40%
    uint256 public rebalancePercent = 10000; // 100% (how far does rebalance of debt move towards 100% from threshold)

    // protocal limits & upper, target and lower thresholds for ratio of debt to collateral
    uint256 public collatLimit = 7500;

    constructor(
        string memory _name,
        string memory _symbol,
        SingleAssetHedgeFarmingConfig memory _conifg
    ) public HedgedFarmingVault(_name, _symbol, _conifg) {}

    function approveContracts() external onlyAuthorized {
        want.safeApprove(config.cTokenLend, uint256(-1));
        short.safeApprove(config.cTokenBorrow, uint256(-1));
        want.safeApprove(config.router, uint256(-1));
        short.safeApprove(config.router, uint256(-1));
        harvestToken.safeApprove(config.router, uint256(-1));
        if (address(compToken) != address(0))
            compToken.safeApprove(config.router, uint256(-1));
        wantShortLP.safeApprove(config.router, uint256(-1));
        wantShortLP.safeApprove(config.farmMasterChef, uint256(-1));
    }

    function resetApprovals() external onlyAuthorized {
        want.safeApprove(config.cTokenLend, 0);
        short.safeApprove(config.cTokenBorrow, 0);
        want.safeApprove(config.router, 0);
        short.safeApprove(config.router, 0);
        harvestToken.safeApprove(config.router, 0);
        if (address(compToken) != address(0))
            compToken.safeApprove(config.router, 0);
        wantShortLP.safeApprove(config.router, 0);
        wantShortLP.safeApprove(config.farmMasterChef, 0);
    }

    function setSlippageAdj(uint256 _lower, uint256 _upper)
        external
        onlyAuthorized
    {
        slippageAdj = _lower;
        slippageAdjHigh = _upper;
    }

    function setDebtThresholds(
        uint256 _lower,
        uint256 _upper,
        uint256 _rebalancePercent
    ) external onlyAuthorized {
        require(_lower <= BPS_ADJUST);
        require(_rebalancePercent <= BPS_ADJUST);
        require(_upper >= BPS_ADJUST);
        rebalancePercent = _rebalancePercent;
        debtUpper = _upper;
        debtLower = _lower;
    }

    function setCollateralThresholds(
        uint256 _lower,
        uint256 _target,
        uint256 _upper,
        uint256 _limit
    ) external onlyAuthorized {
        require(_limit <= BPS_ADJUST);
        collatLimit = _limit;
        require(collatLimit > _upper);
        require(_upper >= _target);
        require(_target >= _lower);
        collatUpper = _upper;
        collatTarget = _target;
        collatLower = _lower;
    }

    function setFundingAllocations(
        uint256 _reserveAllocation,
        uint256 _lendAllocation
    ) external onlyAuthorized {
        uint256 _debtAllocation = BPS_ADJUST.sub(_lendAllocation);
        uint256 impliedCollatRatio =
            _debtAllocation.mul(BPS_ADJUST).div(_lendAllocation);

        require(_reserveAllocation <= reserveAllocationLimit);
        require(impliedCollatRatio <= collatLimit);
        reserveAllocation = _reserveAllocation;
        stratLendAllocation = _lendAllocation;
        stratDebtAllocation = _debtAllocation;
    }

    function rebalanceDebtForced() external onlyAuthorized {
        _rebalanceDebtInternal();
    }

    function rebalanceCollateralForced() external onlyAuthorized {
        _rebalanceCollateralInternal();
    }

    function deployAuth(uint256 _amount) external onlyAuthorized {
        _deployCapital(_amount);
    }

    function liquidatePositionAuth(uint256 _amount) external onlyAuthorized {
        _liquidatePosition(_amount);
    }

    // remove all of Vaults LP tokens and repay debt meaning vault only holds want token (in lending + reserves)
    function exitLeveragePosition() external onlyAuthorized {
        _withdrawAllPooled();
        _removeAllLp();
        _repayDebt();

        if (balanceDebt() > 5) {
            uint256 debtOutstanding =
                cTokenBorrow.borrowBalanceStored(address(this));
            _swapWantShortExact(debtOutstanding);
            _repayDebt();
        } else if (balanceShort() > 5) {
            _swapShortWant(short.balanceOf(address(this)));
        }

        _redeemWant(balanceLend().sub(5));
    }

    /// function to deploy funds when reserves exceed reserve threshold (maximum is five percent)
    function deployStrat() external onlyKeepers {
        uint256 bal = want.balanceOf(address(this));
        uint256 totalBal = estimatedTotalAssets();
        uint256 reserves = totalBal.mul(reserveAllocation).div(BPS_ADJUST);
        if (bal > reserves) {
            _deployCapital(bal.sub(reserves));
        }
    }

    /// rebalances RoboVault strat position to within target collateral range
    function rebalanceCollateral() external onlyKeepers {
        // ratio of amount borrowed to collateral
        uint256 collatRatio = calcCollateral();
        require(
            collatRatio <= collatLower || collatRatio >= collatUpper
        );
        _rebalanceCollateralInternal();
    }

    /// rebalances RoboVault holding of short token vs LP to within target collateral range
    function rebalanceDebt() public onlyKeepers {
        uint256 debtRatio = calcDebtRatio();
        require(debtRatio < debtLower || debtRatio > debtUpper);
        _rebalanceDebtInternal();
    }

    /// called by keeper to harvest rewards and either repay debt
    function _harvestInternal()
        internal
        virtual override
        returns (uint256 _wantHarvested)
    {
        /// harvest from farm & wantd on amt borrowed vs LP value either -> repay some debt or add to collateral
        farm.withdraw(config.farmPid, 0); /// for spooky swap call withdraw with amt = 0
        comptroller.claimComp(address(this));
        _sellHarvestShort();
        _sellCompShort();
        uint256 debtPreHarvest = balanceDebt();
        _repayDebt();
        uint256 harvestValue = debtPreHarvest.sub(balanceDebt());
        return harvestValue;
    }

    function checkDeposit(uint256 _amount) public override returns (bool) {
        require(!collateralCapReached(_amount));
    }

    /**
     * Checks if collateral cap is reached or if deploying `_amount` will make it reach the cap
     * returns true if the cap is reached
     */
    function collateralCapReached(uint256 _amount)
        public
        virtual
        view
        returns (bool _capReached)
    {
        return
            cTokenLend.totalCollateralTokens().add(_amount) <
            cTokenLend.collateralCap();
    }

    /// before withdrawing from strat check there is enough liquidity in lending protocal
    function _liquidityCheck(uint256 _amount) internal view {
        uint256 lendBal = getWantInLending();
        require(lendBal > _amount);
    }

    /// this is the withdrawl fee when user withdrawal results in removal of funds from strategy (i.e. withdrawal in excess of reserves)
    function _calcWithdrawalFee(uint256 _r) internal view returns (uint256) {
        uint256 _fee = _r.mul(withdrawalFee).div(BPS_ADJUST);
        return (_fee);
    }

    function _rebalanceCollateralInternal() internal {
        uint256 collatRatio = calcCollateral();
        uint256 shortPos = balanceDebt();
        uint256 lendPos = balanceLendCollateral();

        if (collatRatio > collatTarget) {
            uint256 adjAmount =
                (shortPos.sub(lendPos.mul(collatTarget).div(BPS_ADJUST)))
                    .mul(BPS_ADJUST)
                    .div(BPS_ADJUST.add(collatTarget));
            /// remove some LP use 50% of withdrawn LP to repay debt and half to add to collateral
            _withdrawLpRebalanceCollateral(adjAmount.mul(2));
            emit CollatRebalance(collatRatio, adjAmount);
        } else if (collatRatio < collatTarget) {
            uint256 adjAmount =
                ((lendPos.mul(collatTarget).div(BPS_ADJUST)).sub(shortPos))
                    .mul(BPS_ADJUST)
                    .div(BPS_ADJUST.add(collatTarget));
            uint256 borrowAmt = _borrowWantEq(adjAmount);
            _redeemWant(adjAmount);
            _addToLP(borrowAmt);
            _depoistLp();
            emit CollatRebalance(collatRatio, adjAmount);
        }
    }

    // deploy assets according to vault strategy
    function _deployCapital(uint256 _amount) internal {
        checkDeposit(_amount);

        uint256 lendDeposit = stratLendAllocation.mul(_amount).div(BPS_ADJUST);
        _lendWant(lendDeposit);
        uint256 borrowAmtWant =
            stratDebtAllocation.mul(_amount).div(BPS_ADJUST);
        uint256 borrowAmt = _borrowWantEq(borrowAmtWant);
        _addToLP(borrowAmt);
        _depoistLp();
    }

    function _rebalanceDebtInternal() internal {
        uint256 debtRatio = calcDebtRatio();
        uint256 shortPos = balanceDebt();
        uint256 lpPos = balanceLp();
        uint256 slippage;
        uint256 swapAmount;

        if (debtRatio < BPS_ADJUST) {
            // amount of short token in LP is greater than amount borrowed ->
            // desired action: borrow more short token swap half for want token and add to LP + farm
            // but first check if that's going to need more collateral than is available
            uint256 lendBal = balanceLendCollateral();
            uint256 borrowAmtWant =
                lpPos.sub(shortPos.mul(2)).mul(rebalancePercent).div(
                    BPS_ADJUST
                );
            uint256 borrowAmt = _borrowWantEq(borrowAmtWant);

            uint256 postRebalCollatRatio =
                shortPos.add(borrowAmtWant).mul(BPS_ADJUST).div(lendBal);
            if (postRebalCollatRatio > collatLimit.mul(9700).div(BPS_ADJUST)) {
                (swapAmount, slippage) = _rebalanceVeryLowDebt();
            } else {
                (swapAmount, slippage) = _rebalanceLowDebt(borrowAmt);
            }
        } else {
            (swapAmount, slippage) = _rebalanceHighDebt(shortPos, lpPos);
        }
        emit DebtRebalance(debtRatio, swapAmount, slippage);
    }

    function _rebalanceHighDebt(uint256 shortPos, uint256 lpPos) internal returns (uint256 swapAmountWant, uint256 slippageWant) {
        // amount of short token in LP is less than amount borrowed ->
        // action = remove some LP -> repay debt + add want token to collateral
        uint256 wantValueAdj =
            ((shortPos.mul(2)).sub(lpPos)).mul(rebalancePercent).div(
                BPS_ADJUST
            );
        (swapAmountWant, slippageWant) = _withdrawLpRebalance(wantValueAdj);
    }

    function _rebalanceLowDebt(uint256 borrowAmt) internal returns (uint256 swapAmountWant, uint256 slippageWant) {
        uint256 swapAmountShort = borrowAmt.div(2);
        (swapAmountWant, slippageWant) = _swapShortWant(swapAmountShort);
        _addToLP(swapAmountShort);
        _depoistLp();
    }

    function _rebalanceVeryLowDebt() internal returns (uint256 swapAmountWant, uint256 slippageWant) {
        uint256 shortPos = balanceDebt();
        uint256 lpPos = balanceLp();
        uint256 adjAmount =
            lpPos.sub(shortPos.mul(2)).mul(rebalancePercent).div(BPS_ADJUST);
        uint256 lpRemove =
            adjAmount.mul(wantShortLP.totalSupply()).div(
                want.balanceOf(config.wantShortLP).mul(2)
            );
        _withdrawSomeLp(lpRemove);
        _removeAllLp();
        (swapAmountWant, slippageWant) = _swapShortWant(short.balanceOf(address(this)));
    }

    /**
     * Withdraws and removes `_deployedPercent` percentage if LP from farming and pool respectively
     *
     * @param _deployedPercent percentage multiplied by BPS_ADJUST of LP to remove.
     */
    function _removeLpPercent(uint256 _deployedPercent) internal {
        uint256 lpPooled = countLpPooled();
        uint256 lpUnpooled = wantShortLP.balanceOf(address(this));
        uint256 lpCount = lpUnpooled.add(lpPooled);
        uint256 lpReq = lpCount.mul(_deployedPercent).div(BPS_ADJUST);
        uint256 lpWithdraw;
        if (lpReq - lpUnpooled < lpPooled) {
            lpWithdraw = lpReq.sub(lpUnpooled);
        } else {
            lpWithdraw = lpPooled;
        }

        // Finnally withdraw the LP from farms and remove from pool
        _withdrawSomeLp(lpWithdraw);
        _removeAllLp();
    }

    /**
     * function to remove funds from strategy when users withdraws funds in excess of reserves
     *
     * Liquidation takes the following steps:
     * 1. Removes _amount worth of LP from the farms and pool
     * 2. Uses the short removed to repay debt (Swaps short or base for large withdrawals)
     * 3. Redeems the
     * @param _amount `want` amount to liquidate
     */
    function _liquidatePosition(uint256 _amount)
        internal
        override
        returns (uint256 _liquidatedAmount, uint256 _loss)
    {
        uint256 balTotal = estimatedTotalAssets();
        // Check _amount is less that the total value
        require(_amount <= balTotal);

        uint256 reserves = want.balanceOf(address(this));
        uint256 debtRatio = calcDebtRatio();

        // stratPercent: Percentage of the deployed capital we want to liquidate.
        uint256 stratPercent =
            _amount.sub(reserves).mul(BPS_ADJUST).div(balTotal.sub(reserves));
        _removeLpPercent(stratPercent);

        // This is a precaution - large withdrawals can imbalance the debt and collateral ratios.
        if (stratPercent > largeWithdrawThreshold) {
            if (debtRatio < BPS_ADJUST) {
                uint256 shortSwap =
                    short
                        .balanceOf(address(this))
                        .mul(BPS_ADJUST.sub(debtRatio))
                        .div(BPS_ADJUST);
                _swapShortWant(shortSwap);
            }
            if (debtRatio > BPS_ADJUST) {
                uint256 shortSwap =
                    short
                        .balanceOf(address(this))
                        .mul(debtRatio.sub(BPS_ADJUST))
                        .div(BPS_ADJUST);
                uint256 wantSwap = convertShortToWantLP(shortSwap);
                _swapWantShort(wantSwap);
            }
        }

        // Repay debt with any short in the balance
        _repayDebt();

        // Redeems the remaining amount of `want` needed
        uint256 redeemAmount = _amount.sub(want.balanceOf(address(this)));

        // need to add a check for collateral ratio after redeeming
        uint256 postRedeemCollateral =
            (balanceDebt()).mul(BPS_ADJUST).div(
                balanceLend().sub(redeemAmount)
            );
        if (postRedeemCollateral < collatLimit) {
            // Collateral ratio is okay, continue with redeming.
            _redeemWant(redeemAmount);
        } else {
            uint256 subAmt = collatUpper.mul(balanceLend().sub(redeemAmount));
            uint256 numerator = balanceDebt().mul(BPS_ADJUST).sub(subAmt);
            uint256 denominator = BPS_ADJUST.sub(collatUpper);

            _swapWantShortExact(numerator.div(denominator));
            _repayDebt();
            _redeemWant(redeemAmount);
        }

        _liquidatedAmount = want.balanceOf(address(this)).sub(reserves);
        _loss = 0;
        if (balTotal > estimatedTotalAssets()) {
            _loss = balTotal.sub(estimatedTotalAssets());
        }

        return (_liquidatedAmount, _loss);
    }
}

// Part: ComptrollerV5Storage

interface ComptrollerV5Storage is ComptrollerV4Storage {
    // @notice The supplyCapGuardian can set supplyCaps to any number for any market. Lowering the supply cap could disable supplying to the given market.
    // address external supplyCapGuardian;
    function supplyCapGuardian() external view returns (address);

    // @notice Supply caps enforced by mintAllowed for each cToken address. Defaults to zero which corresponds to unlimited supplying.
    // mapping(address => uint) external supplyCaps;
    function supplyCaps(address) external view returns (uint);
}

// Part: ScreamPriceOracle

contract ScreamPriceOracle is IPriceOracle {
    using SafeMath for uint256;

    address cTokenQuote;
    address cTokenBase;
    ICompPriceOracle oracle;
    uint256 multiply;
    uint256 divide;

    constructor(
        address _comtroller,
        address _cTokenQuote,
        address _cTokenBase,
        uint256 _multiply,
        uint256 _divide
    ) public {
        cTokenQuote = _cTokenQuote;
        cTokenBase = _cTokenBase;
        oracle = ICompPriceOracle(ComptrollerV5Storage(_comtroller).oracle());
        require(oracle.isPriceOracle());
        multiply = 10**_multiply;
        divide = 10**_divide;
    }

    function getPrice() external view override returns (uint256) {
        // If price returns 0, the price is not available
        uint256 quotePrice = oracle.getUnderlyingPrice(cTokenQuote);
        require(quotePrice != 0);

        uint256 basePrice = oracle.getUnderlyingPrice(cTokenBase);
        require(basePrice != 0);

        return basePrice.mul(multiply).div(quotePrice).div(divide);
    }
}

// File: WFTMUSDCScreamSpirit.sol

contract rvWFTMScreamSpirit is HedgedFarmingStrategy {

    constructor()
        public
        HedgedFarmingStrategy(
            "Robovault V2 WFTM",
            "rv2WFTMa",
            SingleAssetHedgeFarmingConfig(
                0x21be370D5312f44cB42ce377BC9b8a0cEF1A4C83, // want
                0x04068DA6C83AFCFA0e13ba15A6696662335D5B75, // short
                0xe7E90f5a767406efF87Fdad7EB07ef407922EC1D, // wantShortLP
                0x5Cc61A78F164885776AA610fb0FE1257df78E59B, // farmToken
                0x30748322B6E34545DBe0788C421886AEB5297789, // farmTokenLp
                0x9083EA3756BDE6Ee6f27a6e996806FBD37F6F093, // farmMasterChef
                4, // farmPid
                0x5AA53f03197E08C4851CAD8C92c7922DA5857E5d, // cTokenLend
                0xE45Ac34E528907d0A0239ab5Db507688070B20bf, // cTokenBorrow
                0xe0654C8e6fd4D733349ac7E09f6f23DA256bF475, // compToken
                0x30872e4fc4edbFD7a352bFC2463eb4fAe9C09086, // compTokenLP
                0x260E596DAbE3AFc463e75B6CC05d8c46aCAcFB09, // comptroller
                0x16327E3FbDaCA3bcF7E38F5Af2599D2DDc33aE52 // router
            )
        )
    {
        // create the price oracle
        oracle = new ScreamPriceOracle(
            config.comptroller,
            config.cTokenLend,
            config.cTokenBorrow,
            18,
            0
        );
    }


    function _farmPendingRewards(uint256 _pid, address _user)
        internal
        view
        override
        returns (uint256)
    {
        return SpiritFarm(config.farmMasterChef).pendingSpirit(_pid, _user);
    }

    // Harvest override due to FTM vaults being slightly different
    function balancePendingHarvest() public override view returns(uint256){
        // Get Farm Rewards. Ignoring the comp rewards becuase they need a STATIC_CALL.
        uint256 farmRewardsPending = _farmPendingRewards(config.farmPid, address(this)).add(harvestToken.balanceOf(address(this)));
        uint256 farmHarvestLpHarvest = _getHarvestInHarvestLp();
        uint256 farmHarvestLpBase = want.balanceOf(config.farmTokenLp);
        return farmRewardsPending.mul(farmHarvestLpBase).div(farmHarvestLpHarvest);
    }

    /**
     * Checks if collateral cap is reached or if deploying `_amount` will make it reach the cap
     * returns true if the cap is reached
     */
    function collateralCapReached(uint256 _amount)
        public
        override
        view
        returns (bool _capReached)
    {            
        // return false;
        uint256 cap = ComptrollerV5Storage(config.comptroller).supplyCaps(config.cTokenLend);

        // If the cap is zero, there is no cap. 
        if (cap == 0)
            return false;

        uint256 totalCash = cTokenLend.getCash();
        uint256 totalBorrows = cTokenLend.totalBorrows();
        uint256 totalReserves = cTokenLend.totalReserves();
        uint256 totalCollateralised = totalCash.add(totalBorrows).sub(totalReserves);
        return totalCollateralised.add(_amount) > cap;
    }

    // balanceLendCollateral == balanceLend in Scream's Compound version
    function balanceLendCollateral() public view override returns (uint256) {
        return balanceLend();
    }

    // Override to comp to WFTM - Only used for harvests 
    function _pathCompToShort()
        internal
        view
        override
        returns (address[] memory)
    {
        address[] memory pathShort = new address[](2);
        pathShort[0] = address(compToken);
        pathShort[1] = address(want);
        return pathShort;
    }

    // Override to farm to WFTM - Only used for harvests
    function _pathFarmToShort()
        internal
        view
        override
        returns (address[] memory)
    {
        address[] memory pathShort = new address[](2);
        pathShort[0] = address(harvestToken);
        pathShort[1] = address(want);
        return pathShort;
    }

    // Slightly different for WFTM vaults. Rather than repaying debt, we just add the harvest to reserves.
    function _harvestInternal()
        internal
        override
        returns (uint256 _wantHarvested)
    {
        /// harvest from farm & wantd on amt borrowed vs LP value either -> repay some debt or add to collateral
        farm.withdraw(config.farmPid, 0); /// for spooky swap call withdraw with amt = 0
        comptroller.claimComp(address(this));
        uint256 reservesPreHarvest = balanceReserves();
        _sellHarvestShort();
        _sellCompShort();
        _wantHarvested = reservesPreHarvest.sub(reservesPreHarvest);
    }
}
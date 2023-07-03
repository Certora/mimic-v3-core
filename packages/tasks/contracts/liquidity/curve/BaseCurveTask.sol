// SPDX-License-Identifier: GPL-3.0-or-later
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

pragma solidity ^0.8.0;

import '@mimic-fi/v3-helpers/contracts/math/FixedPoint.sol';
import '@mimic-fi/v3-helpers/contracts/utils/EnumerableMap.sol';

import '../../Task.sol';
import './interfaces/IBaseCurveTask.sol';

/**
 * @title Base curve task
 * @dev Task that offers the basic components for more detailed Curve related tasks.
 */
abstract contract BaseCurveTask is IBaseCurveTask, Task {
    using FixedPoint for uint256;
    using EnumerableMap for EnumerableMap.AddressToUintMap;

    // Task connector address
    address public override connector;

    // Default maximum slippage in fixed point
    uint256 public override defaultMaxSlippage;

    // Maximum slippage per token address
    EnumerableMap.AddressToUintMap private _customMaxSlippages;

    /**
     * @dev Modifier to tag the execution function of an task to trigger before and after hooks automatically
     */
    modifier baseCurveTaskCall(address token, uint256 amount, uint256 slippage) {
        _beforeCurveTask(token, amount, slippage);
        _;
        _afterCurveTask(token, amount, slippage);
    }

    /**
     * @dev Custom max slippage config. Only used in the initializer.
     */
    struct CustomMaxSlippage {
        address token;
        uint256 maxSlippage;
    }

    /**
     * @dev Base Curve task config. Only used in the initializer.
     */
    struct BaseCurveConfig {
        address connector;
        uint256 maxSlippage;
        CustomMaxSlippage[] customMaxSlippages;
        TaskConfig taskConfig;
    }

    /**
     * @dev Initializes a base Curve task
     */
    function _initialize(BaseCurveConfig memory config) internal onlyInitializing {
        _initialize(config.taskConfig);
        _setConnector(config.connector);
        _setDefaultMaxSlippage(config.maxSlippage);
        for (uint256 i = 0; i < config.customMaxSlippages.length; i++) {
            _setCustomMaxSlippage(config.customMaxSlippages[i].token, config.customMaxSlippages[i].maxSlippage);
        }
    }

    /**
     * @dev Tells the max slippage defined for a specific token
     */
    function customMaxSlippage(address token) public view override returns (uint256 maxSlippage) {
        (, maxSlippage) = _customMaxSlippages.tryGet(token);
    }

    /**
     * @dev Sets the task connector
     * @param newConnector Address of the new connector to be set
     */
    function setConnector(address newConnector) external override authP(authParams(newConnector)) {
        _setConnector(newConnector);
    }

    /**
     * @dev Sets the default max slippage
     */
    function setDefaultMaxSlippage(uint256 maxSlippage) external override authP(authParams(maxSlippage)) {
        _setDefaultMaxSlippage(maxSlippage);
    }

    /**
     * @dev Sets a a custom max slippage
     * @param token Address of the token to set a max slippage for
     * @param maxSlippage Max slippage to be set for the given token
     */
    function setCustomMaxSlippage(address token, uint256 maxSlippage)
        external
        override
        authP(authParams(token, maxSlippage))
    {
        _setCustomMaxSlippage(token, maxSlippage);
    }

    /**
     * @dev Tells the max slippage that should be used for a token
     */
    function _getApplicableMaxSlippage(address token) internal view returns (uint256) {
        return _customMaxSlippages.contains(token) ? _customMaxSlippages.get(token) : defaultMaxSlippage;
    }

    /**
     * @dev Hook to be called before the Curve task call starts. This implementation calls the base task `_beforeTask`
     * hook and finally adds some trivial token, amount, and max slippage validations.
     */
    function _beforeCurveTask(address token, uint256 amount, uint256 slippage) internal virtual {
        _beforeTask(token, amount);
        require(token != address(0), 'TASK_TOKEN_ZERO');
        require(amount > 0, 'TASK_AMOUNT_ZERO');
        require(slippage <= _getApplicableMaxSlippage(token), 'TASK_SLIPPAGE_TOO_HIGH');
    }

    /**
     * @dev Hook to be called after the Curve task call has finished. This implementation simply calls the base task
     * `_afterTask` hook.
     */
    function _afterCurveTask(address token, uint256 amount, uint256) internal virtual {
        _afterTask(token, amount);
    }

    /**
     * @dev Sets the task connector
     * @param newConnector New connector to be set
     */
    function _setConnector(address newConnector) internal {
        require(newConnector != address(0), 'TASK_CONNECTOR_ZERO');
        connector = newConnector;
        emit ConnectorSet(newConnector);
    }

    /**
     * @dev Sets the default max slippage
     * @param maxSlippage Default max slippage to be set
     */
    function _setDefaultMaxSlippage(uint256 maxSlippage) internal {
        require(maxSlippage <= FixedPoint.ONE, 'TASK_SLIPPAGE_ABOVE_ONE');
        defaultMaxSlippage = maxSlippage;
        emit DefaultMaxSlippageSet(maxSlippage);
    }

    /**
     * @dev Sets a custom max slippage for a token
     * @param token Address of the token to set the custom max slippage for
     * @param maxSlippage Max slippage to be set
     */
    function _setCustomMaxSlippage(address token, uint256 maxSlippage) internal {
        require(maxSlippage <= FixedPoint.ONE, 'TASK_SLIPPAGE_ABOVE_ONE');
        maxSlippage == 0 ? _customMaxSlippages.remove(token) : _customMaxSlippages.set(token, maxSlippage);
        emit CustomMaxSlippageSet(token, maxSlippage);
    }
}
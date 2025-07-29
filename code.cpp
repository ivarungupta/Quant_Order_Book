#include<iostream>
#include<cstdint>
#include<map>
#include<set>
#include<list>
#include<cmath>
#include<ctime>
#include<deque>
#include<stack>
#include<limits>
#include<string>
#include<vector>
#include<numeric>
#include<algorithm>
#include<unordered_map>
#include<memory>
#include<variant>
#include<optional>
#include<tuple>
#include<format>
#include<exception>
#include<cassert>

using namespace std;

// OrderType represents the type of order placed
enum class OrderType
{
    GoodTillCancel, // Order remains in the book until explicitly cancelled or fully filled
    FillAndKill     // Order is filled immediately or removed from the book
};

// Side represents the side of the market: Buy or Sell
enum class Side
{
    Buy,
    Sell
};

// Alias definitions for price, quantity, and order ID
using Price = int32_t;
using Quantity = uint32_t;
using OrderId = uint64_t;

// Represents a level in the order book (price + total quantity)
struct LevelInfo 
{
    Price price_;
    Quantity quantity_;
};

using LevelInfos = vector<LevelInfo>;

// Holds all price levels of bids and asks in the order book
class OrderBookLevelInfos
{
public:
    OrderBookLevelInfos(const LevelInfos& bidLevels, const LevelInfos& askLevels)
        : bidLevels_{ bidLevels }, askLevels_{ askLevels } {}

    const LevelInfos& GetBids() const { return bidLevels_; }
    const LevelInfos& GetAsks() const { return askLevels_; }

private:
    LevelInfos bidLevels_;
    LevelInfos askLevels_;
};

// Represents an individual order
class Order
{
public:
    Order(OrderType type, OrderId id, Side side, Price price, Quantity qty)
        : type_{ type }, id_{ id }, side_{ side }, price_{ price }, initialQty_{ qty }, remainingQty_{ qty } {}

    OrderId GetOrderId() const { return id_; }
    Side GetSide() const { return side_; }
    Price GetPrice() const { return price_; }
    OrderType GetOrderType() const { return type_; }
    Quantity GetInitialQuantity() const { return initialQty_; }
    Quantity GetRemainingQuantity() const { return remainingQty_; }
    Quantity GetFilledQuantity() const { return initialQty_ - remainingQty_; }
    bool IsFilled() const { return remainingQty_ == 0; }

    void Fill(Quantity qty) {
        if (qty > remainingQty_) {
            throw logic_error(format("Order ({}) cannot be filled for more than its remaining quantity.", id_));
        }
        remainingQty_ -= qty;
    }

private:
    OrderType type_;
    OrderId id_;
    Side side_;
    Price price_;
    Quantity initialQty_;
    Quantity remainingQty_;
};

using OrderPtr = shared_ptr<Order>;
using OrderList = list<OrderPtr>;

// Represents a modification instruction for an order
class OrderModify
{
public:
    OrderModify(OrderId id, Side side, Price price, Quantity qty)
        : id_{ id }, price_{ price }, side_{ side }, qty_{ qty } {}

    OrderId GetOrderId() const { return id_; }
    Price GetPrice() const { return price_; }
    Side GetSide() const { return side_; } 
    Quantity GetQuantity() const { return qty_; }

    OrderPtr ToOrderPointer(OrderType type) const {
        return make_shared<Order>(type, id_, side_, price_, qty_);
    }

private:
    OrderId id_;
    Price price_;
    Side side_;
    Quantity qty_; 
};

// TradeInfo contains details about a trade from either side (buy/sell)
struct TradeInfo
{
    OrderId orderId_;
    Price price_;
    Quantity quantity_;
};

// Trade holds matched trade information from both buyer and seller
class Trade{
public:
    Trade(const TradeInfo& buyer, const TradeInfo& seller)
        : buyerInfo_{ buyer }, sellerInfo_{ seller } {}

    const TradeInfo& GetBidTrade() const { return buyerInfo_; }
    const TradeInfo& GetAskTrade() const { return sellerInfo_; }

private:
    TradeInfo buyerInfo_;
    TradeInfo sellerInfo_;
};

using Trades = vector<Trade>;

// Main OrderBook class managing all trading operations
class OrderBook
{
private:
    struct OrderEntry
    {
        OrderPtr orderPtr_{ nullptr };
        OrderList::iterator listIt_;
    };

    map<Price, OrderList, greater<Price>> buyOrders_;  // Highest bid comes first
    map<Price, OrderList, less<Price>> sellOrders_;    // Lowest ask comes first
    unordered_map<OrderId, OrderEntry> orderLookup_;   // Fast access by OrderId

    // Determines if an order can be matched with opposite side
    bool CanMatch(Side side, Price price) const
    {
        if (side == Side::Buy) {
            if (sellOrders_.empty()) return false;
            auto bestAsk = sellOrders_.begin()->first;
            return price >= bestAsk;
        } else {
            if (buyOrders_.empty()) return false;
            auto bestBid = buyOrders_.begin()->first;
            return price <= bestBid;
        }
    }

    // Matches buy and sell orders
    Trades MatchOrders()
    {
        Trades matchedTrades;
        matchedTrades.reserve(orderLookup_.size());

        while (!buyOrders_.empty() && !sellOrders_.empty()) {
            auto& [topBuyPrice, topBuyList] = *buyOrders_.begin();
            auto& [topSellPrice, topSellList] = *sellOrders_.begin();

            if (topBuyPrice < topSellPrice) break; // No match possible

            while (!topBuyList.empty() && !topSellList.empty()) {
                auto& buyer = topBuyList.front();
                auto& seller = topSellList.front();
                Quantity tradeQty = min(buyer->GetRemainingQuantity(), seller->GetRemainingQuantity());

                buyer->Fill(tradeQty);
                seller->Fill(tradeQty);

                if (buyer->IsFilled()) {
                    topBuyList.pop_front();
                    orderLookup_.erase(buyer->GetOrderId());
                }
                if (seller->IsFilled()) {
                    topSellList.pop_front();
                    orderLookup_.erase(seller->GetOrderId());
                }

                if (topBuyList.empty()) buyOrders_.erase(topBuyPrice);
                if (topSellList.empty()) sellOrders_.erase(topSellPrice);

                matchedTrades.emplace_back(Trade{ TradeInfo{buyer->GetOrderId(), buyer->GetPrice(), tradeQty},
                                                TradeInfo{seller->GetOrderId(), seller->GetPrice(), tradeQty} });
            }
        }

        // Remove unmatched FillAndKill orders
        if (!buyOrders_.empty()) {
            auto& frontBuyer = buyOrders_.begin()->second.front();
            if (frontBuyer->GetOrderType() == OrderType::FillAndKill) CancelOrder(frontBuyer->GetOrderId());
        }
        if (!sellOrders_.empty()) {
            auto& frontSeller = sellOrders_.begin()->second.front();
            if (frontSeller->GetOrderType() == OrderType::FillAndKill) CancelOrder(frontSeller->GetOrderId());
        }

        return matchedTrades;
    }

public:
    // Adds a new order to the book and attempts matching
    Trades AddOrder(OrderPtr newOrder)
    {
        if (orderLookup_.contains(newOrder->GetOrderId())) return {};

        if (newOrder->GetOrderType() == OrderType::FillAndKill && !CanMatch(newOrder->GetSide(), newOrder->GetPrice())) {
            return {}; // Cannot be matched, skip it
        }

        OrderList::iterator listIter;

        if (newOrder->GetSide() == Side::Buy) {
            auto& orderList = buyOrders_[newOrder->GetPrice()];
            orderList.push_back(newOrder);
            listIter = prev(orderList.end());
        } else {
            auto& orderList = sellOrders_[newOrder->GetPrice()];
            orderList.push_back(newOrder);
            listIter = prev(orderList.end());
        }

        orderLookup_.emplace(newOrder->GetOrderId(), OrderEntry{ newOrder, listIter });

        return MatchOrders();
    }

    // Cancels an order based on order ID
    void CancelOrder(OrderId id)
    {
        if (!orderLookup_.contains(id)) return;

        const auto& [orderRef, iterRef] = orderLookup_.at(id);
        orderLookup_.erase(id);

        auto price = orderRef->GetPrice();
        auto& orderList = (orderRef->GetSide() == Side::Buy) ? buyOrders_[price] : sellOrders_[price];
        orderList.erase(iterRef);
        if (orderList.empty()) {
            if (orderRef->GetSide() == Side::Buy) buyOrders_.erase(price);
            else sellOrders_.erase(price);
        }
    }

    // Modifies an existing order
    Trades MatchOrder(OrderModify mod)
    {
        if (!orderLookup_.contains(mod.GetOrderId())) return {};
        const auto& [existing, _] = orderLookup_.at(mod.GetOrderId());
        CancelOrder(mod.GetOrderId());
        return AddOrder(mod.ToOrderPointer(existing->GetOrderType()));
    }

    size_t Size() const { return orderLookup_.size(); }

    // Retrieves current order book level info
    OrderBookLevelInfos GetOrderInfos() const 
    {
        LevelInfos buyInfo, sellInfo;
        buyInfo.reserve(orderLookup_.size());
        sellInfo.reserve(orderLookup_.size());

        auto BuildLevelInfo = [](Price price, const OrderList& orders) {
            return LevelInfo{ price, accumulate(orders.begin(), orders.end(), (Quantity)0,
                [](Quantity sum, const OrderPtr& order) { return sum + order->GetRemainingQuantity(); })};
        };

        for (const auto& [price, orders] : buyOrders_) buyInfo.push_back(BuildLevelInfo(price, orders));
        for (const auto& [price, orders] : sellOrders_) sellInfo.push_back(BuildLevelInfo(price, orders));

        return OrderBookLevelInfos{ buyInfo, sellInfo };
    }
};

// Function to run unit test cases for the order book
void runOrderBookTests() {
    OrderBook ob;

    cout << "\nTest Case 1: Basic Order Addition and Cancellation" << endl;
    {
        auto order = make_shared<Order>(OrderType::GoodTillCancel, 1, Side::Buy, 100, 10);
        auto trades = ob.AddOrder(order);
        assert(ob.Size() == 1);
        assert(trades.empty());
        ob.CancelOrder(1);
        assert(ob.Size() == 0);
        cout << "Test Case 1 Passed!" << endl;
    }

    cout << "\nTest Case 2: Order Matching" << endl;
    {
        auto buyOrder = make_shared<Order>(OrderType::GoodTillCancel, 2, Side::Buy, 100, 5);
        ob.AddOrder(buyOrder);

        auto sellOrder = make_shared<Order>(OrderType::GoodTillCancel, 3, Side::Sell, 100, 5);
        auto trades = ob.AddOrder(sellOrder);

        assert(trades.size() == 1);
        assert(trades[0].GetBidTrade().orderId_ == 2);
        assert(trades[0].GetAskTrade().orderId_ == 3);
        assert(trades[0].GetBidTrade().quantity_ == 5);
        assert(ob.Size() == 0);
        cout << "Test Case 2 Passed!" << endl;
    }

    cout << "\nTest Case 3: Partial Fill" << endl;
    {
        auto buyOrder = make_shared<Order>(OrderType::GoodTillCancel, 4, Side::Buy, 100, 10);
        ob.AddOrder(buyOrder);

        auto sellOrder = make_shared<Order>(OrderType::GoodTillCancel, 5, Side::Sell, 100, 6);
        auto trades = ob.AddOrder(sellOrder);

        assert(trades.size() == 1);
        assert(trades[0].GetBidTrade().quantity_ == 6);
        assert(ob.Size() == 1);

        auto levels = ob.GetOrderInfos();
        assert(levels.GetBids()[0].quantity_ == 4);
        cout << "Test Case 3 Passed!" << endl;
    }

    cout << "\nTest Case 4: FillAndKill Order" << endl;
    {
        OrderBook tempOb;
        auto sellOrder = make_shared<Order>(OrderType::GoodTillCancel, 6, Side::Sell, 100, 5);
        tempOb.AddOrder(sellOrder);

        auto buyOrder = make_shared<Order>(OrderType::FillAndKill, 7, Side::Buy, 100, 10);
        auto trades = tempOb.AddOrder(buyOrder);

        assert(trades.size() == 1);
        assert(trades[0].GetBidTrade().quantity_ == 5);
        assert(tempOb.Size() == 0);
        cout << "Test Case 4 Passed!" << endl;
    }
}

int main() {
    runOrderBookTests();
    return 0;
}

local function print(msg)
    if DEFAULT_CHAT_FRAME then
        DEFAULT_CHAT_FRAME:AddMessage(msg)
    end
end

local _G = getfenv(0)

-- =============================================================
-- HELPER FUNCTIONS
-- =============================================================
local function round(num, idp)
  local mult = 10^(idp or 0)
  return math.floor(num * mult + 0.5) / mult
end

local function rgbhex(r, g, b)
  if type(r) == "table" then
    if r.r then r, g, b = r.r, r.g, r.b else r, g, b = unpack(r) end
  end
  return string.format("|cff%02x%02x%02x", (r or 1) * 255, (g or 1) * 255, (b or 1) * 255)
end

local function IsFailure(msg)
    if not msg then return false end
    msg = string.lower(msg)
    if string.find(msg, "miss") or string.find(msg, "parry") or string.find(msg, "dodge") or 
       string.find(msg, "block") or string.find(msg, "resist") or string.find(msg, "fail") or 
       string.find(msg, "immune") or string.find(msg, "evade") then
        return true
    end
    return false
end

-- =============================================================
-- LIBTIPSCAN
-- =============================================================
local libtipscan = {}
local baseName = "UIScan"
local methods = {
  "SetBagItem", "SetAction", "SetAuctionItem", "SetAuctionSellItem", "SetBuybackItem",
  "SetCraftItem", "SetCraftSpell", "SetHyperlink", "SetInboxItem", "SetInventoryItem",
  "SetLootItem", "SetLootRollItem", "SetMerchantItem", "SetPetAction", "SetPlayerBuff",
  "SetQuestItem", "SetQuestLogItem", "SetQuestRewardSpell", "SetSendMailItem", "SetShapeshift",
  "SetSpell", "SetTalent", "SetTrackingSpell", "SetTradePlayerItem", "SetTradeSkillItem", "SetTradeTargetItem",
  "SetTrainerService", "SetUnit", "SetUnitBuff", "SetUnitDebuff",
}
local extra_methods = {
  "Find", "Line", "Text", "List",
}

local getText = function(obj)
  local name = obj:GetName()
  local text = {}
  for i=1, obj:NumLines() do
    local left, right = _G[string.format("%sTextLeft%d",name,i)], _G[string.format("%sTextRight%d",name,i)]
    left = left and left:IsVisible() and left:GetText()
    right = right and right:IsVisible() and right:GetText()
    left = left and left ~= "" and left or nil
    right = right and right ~= "" and right or nil
    if left or right then
      text[i] = {left, right}
    end
  end
  return text
end

local findText = function(obj, text, exact)
  local name = obj:GetName()
  for i=1, obj:NumLines() do
    local left, right = _G[string.format("%sTextLeft%d",name,i)], _G[string.format("%sTextRight%d",name,i)]
    left = left and left:IsVisible() and left:GetText()
    right = right and right:IsVisible() and right:GetText()
    if exact then
      if (left and left == text) or (right and right == text) then
        return i, text
      end
    else
      if left then
        local found,_,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10 = string.find(left, text)
        if found then
          return i, a1,a2,a3,a4,a5,a6,a7,a8,a9,a10
        end
      end
      if right then
        local found,_,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10 = string.find(right, text)
        if found then
          return i, a1,a2,a3,a4,a5,a6,a7,a8,a9,a10
        end
      end
    end
  end
end

local lineText = function(obj, line)
  local name = obj:GetName()
  if line <= obj:NumLines() then
    local left, right = _G[string.format("%sTextLeft%d",name,line)], _G[string.format("%sTextRight%d",name,line)]
    left = left and left:IsVisible() and left:GetText()
    right = right and right:IsVisible() and right:GetText()
    if left or right then return left, right end
  end
end

libtipscan._registry = setmetatable({},{__index = function(t,k)
  local v = CreateFrame("GameTooltip", string.format("%s%s",baseName,k), nil, "GameTooltipTemplate")
  v:SetOwner(WorldFrame,"ANCHOR_NONE")
  v:SetScript("OnHide", function () this:SetOwner(WorldFrame,"ANCHOR_NONE") end)
  function v:Text() return getText(self) end
  function v:Find(text, exact) return findText(self, text, exact) end
  function v:Line(line) return lineText(self, line) end
  for _,method in ipairs(methods) do
    local method = method
    local old = v[method]
    v[method] = function(v, a1,a2,a3,a4,a5,a6,a7,a8,a9,a10)
      v:ClearLines()
      return old(v, a1,a2,a3,a4,a5,a6,a7,a8,a9,a10)
    end
  end
  rawset(t,k,v)
  return v
end})

function libtipscan:GetScanner(type)
  local scanner = self._registry[type]
  scanner:ClearLines()
  return scanner
end

-- =============================================================
-- SUNDER TRACKING LOGIC
-- =============================================================

local scanner = libtipscan:GetScanner("sunderarmor")
local frame = CreateFrame("Frame")
local updateFrame = CreateFrame("Frame")
local addon_prefix_sunder_cast = 'SACAST'

local sundercounts = {}
local sync_timestamps = {} 
local me = UnitName("player")
local playerEntered = false 

-- State
local waitingForSunderApply = false
local pendingSunderTime = 0
local lastSelfSunderTime = 0 -- THROTTLE: Prevents double counts
local lastTargetState = nil -- 'missing', 'building', 'max'

-- Timers
local targetTimers = {} -- Key = Name:Level, Value = ExpiryTime
local currentTargetKey = nil
local sunderSoonWarned = false

-- Register Events
frame:RegisterEvent("CHAT_MSG_ADDON")
frame:RegisterEvent("CHAT_MSG_SPELL_PARTY_DAMAGE")
frame:RegisterEvent("CHAT_MSG_SPELL_FRIENDLYPLAYER_DAMAGE")
frame:RegisterEvent("CHAT_MSG_SPELL_PERIODIC_CREATURE_DAMAGE")
frame:RegisterEvent("CHAT_MSG_SPELL_PERIODIC_HOSTILEPLAYER_DAMAGE")
frame:RegisterEvent("CHAT_MSG_SPELL_SELF_DAMAGE") 
frame:RegisterEvent("PLAYER_TARGET_CHANGED")
frame:RegisterEvent("UNIT_AURA")
frame:RegisterEvent("PLAYER_ENTERING_WORLD")
frame:RegisterEvent("SPELLCAST_STOP") -- Used for Silent Maintenance

-- =============================================================
-- HELPER: GET STACKS & KEY
-- =============================================================
local function GetTargetSunderStack()
    if not UnitExists("target") then return 0 end
    for i=1,16 do
        local texture, stack = UnitDebuff("target", i)
        if texture and string.find(string.lower(texture), "sunder") then
            return stack
        end
    end
    return 0
end

local function GetTargetKey()
    if UnitExists("target") and not UnitIsDead("target") then
        local name = UnitName("target") or "Unknown"
        local lvl = UnitLevel("target") or 0
        return string.format("%s:%d", name, lvl)
    end
    return nil
end

-- =============================================================
-- LOGIC: CHECK TARGET STATUS
-- =============================================================
local function CheckTargetSunders(triggerEvent)
    if not playerEntered then return end
    
    if not UnitExists("target") or UnitIsDead("target") or not UnitCanAttack("player", "target") then
        if triggerEvent == "PLAYER_TARGET_CHANGED" then
             lastTargetState = nil
        end
        currentTargetKey = nil
        return
    end

    currentTargetKey = GetTargetKey()
    local sunderStack = GetTargetSunderStack()

    -- SAFETY: If we swapped to a new mob with 0 stacks, clear old timer
    if sunderStack == 0 and currentTargetKey and targetTimers[currentTargetKey] then
        targetTimers[currentTargetKey] = nil
    end

    -- 1. START SUNDER (Green)
    if sunderStack == 0 then
        if lastTargetState ~= 'missing' then
            print("|cff00ff00Start Sunder|r")
            lastTargetState = 'missing'
        end

    -- 2. STOP SUNDER (Red)
    elseif sunderStack == 5 then
        if triggerEvent == "PLAYER_TARGET_CHANGED" and lastTargetState ~= 'max' then
            print("|cffff0000Stop Sunder|r")
            lastTargetState = 'max'
        else
            if triggerEvent ~= "UNIT_AURA" then
               lastTargetState = 'max'
            end
        end

    -- 3. BUILDING
    else
        lastTargetState = 'building'
    end
end

-- =============================================================
-- HELPER: REGISTER SUNDER
-- =============================================================
local function RegisterSunder(casterName)
    -- 1. COUNT
    if not sundercounts[casterName] then sundercounts[casterName] = 0 end
    sundercounts[casterName] = sundercounts[casterName] + 1
    
    -- 2. DETERMINE STACK
    local stack = GetTargetSunderStack()
    
    -- Lag Fix: If server says 0 but we confirmed a hit, show 1.
    if stack == 0 and UnitExists("target") then
        stack = 1
    end
    
    local stackMsg = ""
    local messageColor = "" -- Default white
    local isMaintenance = false
    
    if UnitExists("target") then
        stackMsg = string.format(" (Stack: %d)", stack)
        
        -- MAINTENANCE: If stack is 5 AND we were ALREADY in 'max' state
        if stack == 5 and lastTargetState == 'max' then
            isMaintenance = true
            messageColor = "|cffffd700" -- Yellow
            stackMsg = " (sunder maintained!)" 
        end
        
        -- TIMER RESET
        local key = GetTargetKey()
        if key then
            targetTimers[key] = GetTime() + 30
            sunderSoonWarned = false -- Reset warning flag
        end
    end
    
    local finalMsg = string.format('%s%s sundered!%s|r', messageColor, casterName, stackMsg)

    -- 3. PRINT MESSAGE
    print(finalMsg)
    
    -- 4. PRINT STOP SUNDER (Red)
    if stack == 5 and not isMaintenance then
        print("|cffff0000Stop Sunder|r")
        lastTargetState = 'max'
    end
    
    if stack == 5 then lastTargetState = 'max' end
end

-- =============================================================
-- TIMER LOOP
-- =============================================================
updateFrame:SetScript("OnUpdate", function()
    if not playerEntered then return end
    
    if currentTargetKey and UnitExists("target") and not UnitIsDead("target") then
        local expiry = targetTimers[currentTargetKey]
        if expiry then
            local remaining = expiry - GetTime()
            if remaining <= 5 and remaining > 0 then
                if not sunderSoonWarned then
                    if GetTargetSunderStack() > 0 then
                        print("|cffffd700Sunder soon|r")
                        sunderSoonWarned = true
                    end
                end
            elseif remaining <= 0 then
                targetTimers[currentTargetKey] = nil
            end
        end
    end
end)

-- =============================================================
-- EVENT HANDLER
-- =============================================================
frame:SetScript("OnEvent", function()
    if event == "PLAYER_ENTERING_WORLD" then
        playerEntered = true
        print("|cff00ff00SunderCounter Loaded.|r Type /sundercount to view stats.")

    -- 1. ADDON SYNC
    elseif event == "CHAT_MSG_ADDON" and arg1 == addon_prefix_sunder_cast then
        local sender = arg4
        if sender ~= me then
            sync_timestamps[sender] = GetTime()
            RegisterSunder(sender)
        end

    -- 2. SELF SUNDER: FALLBACK FOR SILENT MAINTENANCE
    -- Only trigger this if we are ALREADY at 5 stacks.
    -- This prevents double-counting building stacks (0-4) which have reliable combat logs.
    elseif event == "SPELLCAST_STOP" then
        if waitingForSunderApply then
             if UnitExists("target") and UnitCanAttack("player", "target") then
                 -- MAINTENANCE CHECK: Only rely on blind SPELLCAST_STOP if stack is 5
                 if GetTargetSunderStack() == 5 then
                     -- THROTTLE (0.5s)
                     if (GetTime() - lastSelfSunderTime) > 0.5 then
                         lastSelfSunderTime = GetTime()
                         waitingForSunderApply = false
                         RegisterSunder(me)
                         
                         local channel = nil
                         if GetNumRaidMembers() > 0 then channel = "RAID"
                         elseif GetNumPartyMembers() > 0 then channel = "PARTY" end
                         if channel then
                             SendAddonMessage(addon_prefix_sunder_cast, "CAST", channel)
                         end
                     end
                 end
             end
        end

    -- 3. SELF SUNDER: VISIBLE COMBAT LOG (Building & Visible Maintenance)
    elseif event == "CHAT_MSG_SPELL_PERIODIC_CREATURE_DAMAGE" or 
           event == "CHAT_MSG_SPELL_PERIODIC_HOSTILEPLAYER_DAMAGE" or
           event == "CHAT_MSG_SPELL_SELF_DAMAGE" then
        
        if string.find(arg1, "Sunder Armor") then
            -- FAILURE CHECK
            if IsFailure(arg1) then
                if waitingForSunderApply then waitingForSunderApply = false end
                return
            end

            -- SUCCESS KEYWORDS
            local isAfflicted = string.find(arg1, "is afflicted by")
            local isCast = string.find(arg1, "You cast") or string.find(arg1, "You perform")
            local isHit = string.find(arg1, "hits") or string.find(arg1, "crits")
            
            if (waitingForSunderApply and (GetTime() - pendingSunderTime < 2)) or isCast then
                 if isAfflicted or isCast or isHit then
                    -- THROTTLE (0.5s)
                    if (GetTime() - lastSelfSunderTime) > 0.5 then
                        lastSelfSunderTime = GetTime()
                        waitingForSunderApply = false
                        RegisterSunder(me)
                        
                        local channel = nil
                        if GetNumRaidMembers() > 0 then channel = "RAID"
                        elseif GetNumPartyMembers() > 0 then channel = "PARTY" end
                        if channel then
                            SendAddonMessage(addon_prefix_sunder_cast, "CAST", channel)
                        end
                    end
                 end
            end
        end

    -- 4. COMBAT LOG: OTHERS
    elseif event == "CHAT_MSG_SPELL_PARTY_DAMAGE" or event == "CHAT_MSG_SPELL_FRIENDLYPLAYER_DAMAGE" then
        local caster = nil
        if string.find(arg1, "casts Sunder Armor") then
            _, _, caster = string.find(arg1, "(.+) casts Sunder Armor")
        elseif string.find(arg1, "performs Sunder Armor") then
            _, _, caster = string.find(arg1, "(.+) performs Sunder Armor")
        end

        if caster and caster ~= me then
            if string.find(caster, "%]") then
                local _, e = string.find(caster, "%] ")
                if e then caster = string.sub(caster, e+1) end
            end
            
            local lastSync = sync_timestamps[caster] or 0
            if (GetTime() - lastSync) > 2 then
                RegisterSunder(caster)
                sync_timestamps[caster] = GetTime()
            end
        end

    -- 5. TARGET CHANGE
    elseif event == "PLAYER_TARGET_CHANGED" then
        sunderSoonWarned = false 
        CheckTargetSunders("PLAYER_TARGET_CHANGED")

    -- 6. AURA UPDATE
    elseif event == "UNIT_AURA" then
        if arg1 == "target" then
            CheckTargetSunders("UNIT_AURA")
        end
    end
end)


local spellidcache = {}
local function GetSpellCooldownByName(spellName)
    local checkFor = function(bookType)
        local spellid = spellidcache[spellName]
        if spellid then
            local _, duration = GetSpellCooldown(spellid, bookType);
            return duration;
        end
        local i = 1
        while i < 1000 do
            local name, spellRank = GetSpellName(i, bookType);
            if not name then break end
            if name == spellName then
                spellidcache[name] = i
                local _, duration = GetSpellCooldown(i, bookType);
                return duration;
            end
            i = i + 1
        end
        return nil;
    end
    local cd = checkFor(BOOKTYPE_SPELL);
    return cd;
end

-- =============================================================
-- HOOKS
-- =============================================================

local hooks = {}

if not _G.hooksecurefunc then
    function hooksecurefunc(name, func, append)
      if not _G[name] then return end
      hooks[tostring(func)] = {}
      hooks[tostring(func)]["old"] = _G[name]
      hooks[tostring(func)]["new"] = func
      if append then
        hooks[tostring(func)]["function"] = function(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
          hooks[tostring(func)]["old"](a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
          hooks[tostring(func)]["new"](a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
        end
      else
        hooks[tostring(func)]["function"] = function(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
          hooks[tostring(func)]["new"](a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
          hooks[tostring(func)]["old"](a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
        end
      end
      _G[name] = hooks[tostring(func)]["function"]
    end
end

local function maybesunder(spell)
    if not spell then return end
    if type(spell) ~= 'string' then return end
    spell = string.lower(spell)

    if not string.find(spell, 'sunder armor') then return end

    local cd = GetSpellCooldownByName('Sunder Armor')
    if cd == 0 then return end

    if UnitCanAttack("player", "target") == nil then return end

    waitingForSunderApply = true
    pendingSunderTime = GetTime()
end

-- Hooks
hooksecurefunc("UseAction", function(slot, target, button)
    scanner:SetAction(slot)
    local spell, rank = scanner:Line(1)
    if spell then maybesunder(spell) end
end, true)

hooksecurefunc("CastSpell", function(spellid, bookType)
    local spellName = GetSpellName(spellid, bookType)
    if spellName then maybesunder(spellName) end
end, true)

hooksecurefunc("CastSpellByName", function(spell, target)
    maybesunder(spell)
end, true)

-- =============================================================
-- COMMANDS
-- =============================================================
local function resetcounts()
    sundercounts = {}
    print('|cffff0000Sunder counts reset.|r')
end

local function dumpcounts()
    print('|cffffd700Sunder Counts:|r')
    local len = 0
    for k, v in pairs(sundercounts) do
        print(string.format(' - %s: %d', k, v))
        len = len + 1
    end
    if len == 0 then
        print(' - No data recorded.')
    end
    print('----------------')
end

SLASH_SUNDERCOUNT1 = "/sundercount";
SLASH_SUNDERCOUNT2 = "/sundercounts";
SlashCmdList["SUNDERCOUNT"] = dumpcounts

SLASH_SUNDERRESET1 = "/sunderreset";
SlashCmdList["SUNDERRESET"] = resetcounts
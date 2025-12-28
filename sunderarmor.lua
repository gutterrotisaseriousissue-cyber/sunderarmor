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

-- Player State
local waitingForSunderApply = false
local pendingSunderTime = 0

-- Target State
local lastTargetState = nil -- 'missing', 'building', 'max'

-- Timer State (Per Target)
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
frame:RegisterEvent("PLAYER_LOGIN")
frame:RegisterEvent("PLAYER_ENTERING_WORLD")

-- =============================================================
-- HELPER: GET CURRENT TARGET SUNDER STACK
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

-- =============================================================
-- HELPER: GET TARGET KEY (For Timers)
-- =============================================================
local function GetTargetKey()
    if UnitExists("target") and not UnitIsDead("target") then
        local name = UnitName("target") or "Unknown"
        local lvl = UnitLevel("target") or 0
        return string.format("%s:%d", name, lvl)
    end
    return nil
end

-- =============================================================
-- LOGIC: CHECK TARGET STATUS (Start/Stop)
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

    -- SAFETY: If we swapped to a mob (same Name:Level) that has 0 stacks, clear timer.
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
            -- For UNIT_AURA, we rely on RegisterSunder for the print order
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
-- HELPER: PROCESS A SUNDER (Print & Count)
-- =============================================================
local function RegisterSunder(casterName)
    -- 1. COUNT IT
    if not sundercounts[casterName] then sundercounts[casterName] = 0 end
    sundercounts[casterName] = sundercounts[casterName] + 1
    
    local stack = GetTargetSunderStack()
    
    -- Fix "Stack: 0" lag issue
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
            stackMsg = " (Maintenance)" 
        end
        
        -- TIMER UPDATE
        local key = GetTargetKey()
        if key then
            targetTimers[key] = GetTime() + 30
            -- RESET WARNING FLAG so it fires again for this new cycle
            sunderSoonWarned = false 
        end
    end
    
    local finalMsg = string.format('%s%s sundered!%s|r', messageColor, casterName, stackMsg)

    -- 2. PRINT SUNDER MESSAGE
    print(finalMsg)
    
    -- 3. PRINT STOP SUNDER MESSAGE (Red)
    -- Only if we just hit 5 (Building -> Max). Do NOT print on Maintenance.
    if stack == 5 and not isMaintenance then
        print("|cffff0000Stop Sunder|r")
        lastTargetState = 'max'
    end
    
    if stack == 5 then lastTargetState = 'max' end
end

-- =============================================================
-- TIMER UPDATE LOOP (Per Target)
-- =============================================================
updateFrame:SetScript("OnUpdate", function()
    if not playerEntered then return end
    
    -- Check timer for the CURRENT target only
    if currentTargetKey and UnitExists("target") and not UnitIsDead("target") then
        local expiry = targetTimers[currentTargetKey]
        
        if expiry then
            local remaining = expiry - GetTime()
            
            -- Warn at 5 seconds remaining
            if remaining <= 5 and remaining > 0 then
                if not sunderSoonWarned then
                    -- Verify stack still exists before warning
                    if GetTargetSunderStack() > 0 then
                        print("|cffffd700Sunder soon|r")
                        sunderSoonWarned = true
                    end
                end
            elseif remaining <= 0 then
                -- Expired
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

    -- 2. COMBAT LOG: SELF (Loose Matching for Refresh)
    elseif event == "CHAT_MSG_SPELL_PERIODIC_CREATURE_DAMAGE" or 
           event == "CHAT_MSG_SPELL_PERIODIC_HOSTILEPLAYER_DAMAGE" or
           event == "CHAT_MSG_SPELL_SELF_DAMAGE" then
        
        local isAfflicted = string.find(arg1, "is afflicted by Sunder Armor")
        local isCast = string.find(arg1, "You cast Sunder Armor")
        local isPerform = string.find(arg1, "You perform Sunder Armor")
        
        -- If we clicked the button (waitingForSunderApply), we accept ANY indication of cast
        -- OR if we just see "You cast Sunder" (Refreshes often don't trigger waitingForSunderApply perfectly)
        if (waitingForSunderApply and (GetTime() - pendingSunderTime < 2)) or isCast or isPerform then
             if isAfflicted or isCast or isPerform then
                -- Filter out failures
                if not string.find(arg1, "fail") then
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

    -- 3. COMBAT LOG: OTHERS (Robust External Matching)
    elseif event == "CHAT_MSG_SPELL_PARTY_DAMAGE" or event == "CHAT_MSG_SPELL_FRIENDLYPLAYER_DAMAGE" then
        local caster = nil

        -- Match "Name casts Sunder Armor" (works with timestamps like [12:00] Name...)
        if string.find(arg1, "casts Sunder Armor") then
            _, _, caster = string.find(arg1, "(.+) casts Sunder Armor")
        elseif string.find(arg1, "performs Sunder Armor") then
            _, _, caster = string.find(arg1, "(.+) performs Sunder Armor")
        end

        if caster and caster ~= me then
            -- Clean timestamp if present (Simple bracket removal)
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

    -- 4. TARGET CHANGE
    elseif event == "PLAYER_TARGET_CHANGED" then
        sunderSoonWarned = false 
        CheckTargetSunders("PLAYER_TARGET_CHANGED")

    -- 5. AURA UPDATE
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
        -- Safety Break loop
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

-- Hook UseAction
hooksecurefunc("UseAction", function(slot, target, button)
    scanner:SetAction(slot)
    local spell, rank = scanner:Line(1)
    local text = GetActionText(slot)
    if text or not IsCurrentAction(slot) then return end
    maybesunder(spell)
end, true)

-- Hook CastSpell
hooksecurefunc("CastSpell", function(spellid, bookType)
    local spell = 'Sunder Armor'
    if spellidcache[spell] ~= spellid then return end
    maybesunder(spell)
end, true)

-- Hook CastSpellByName
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